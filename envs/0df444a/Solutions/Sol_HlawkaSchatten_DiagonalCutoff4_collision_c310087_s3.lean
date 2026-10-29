-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310087_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:19.354048+00:00
-- url     : https://prove2.me/submissions/da28b452-a584-4d9a-8d7e-b4efbadf3d58

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c310087_s3_s3_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-765704829/5000000000 : ℝ)*x 0 + (5435556189/10000000000 : ℝ)*x 1 + (680407627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765704829/5000000000 : ℝ)^71 ≤ (4436056416049/50000000000000 : ℝ)^55 := by
    have hnat : (765704829 : ℕ)^71*50000000000000^55 ≤ 4436056416049^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765704829 5000000000 4436056416049 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435556189/10000000000 : ℝ)^71 ≤ (22761142803403/50000000000000 : ℝ)^55 := by
    have hnat : (5435556189 : ℕ)^71*50000000000000^55 ≤ 22761142803403^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435556189 10000000000 22761142803403 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680407627/1250000000 : ℝ)^71 ≤ (45605601551731/100000000000000 : ℝ)^55 := by
    have hnat : (680407627 : ℕ)^71*100000000000000^55 ≤ 45605601551731^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680407627 1250000000 45605601551731 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-765704829/5000000000 : ℝ), (5435556189/10000000000 : ℝ), (680407627/1250000000 : ℝ)] ![(4436056416049/50000000000000 : ℝ), (22761142803403/50000000000000 : ℝ), (45605601551731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-765704829/5000000000 : ℝ)|^71 ≤ (4436056416049/50000000000000 : ℝ)^55
        have hw : |(-765704829/5000000000 : ℝ)|=(765704829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435556189/10000000000 : ℝ)|^71 ≤ (22761142803403/50000000000000 : ℝ)^55
        have hw : |(5435556189/10000000000 : ℝ)|=(5435556189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680407627/1250000000 : ℝ)|^71 ≤ (45605601551731/100000000000000 : ℝ)^55
        have hw : |(680407627/1250000000 : ℝ)|=(680407627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5443261719/10000000000 : ℝ)*x 0 + (-1531410643/10000000000 : ℝ)*x 1 + (1358888701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5443261719/10000000000 : ℝ)^71 ≤ (45605609155169/100000000000000 : ℝ)^55 := by
    have hnat : (5443261719 : ℕ)^71*100000000000000^55 ≤ 45605609155169^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443261719 10000000000 45605609155169 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531410643/10000000000 : ℝ)^71 ≤ (8872120198707/100000000000000 : ℝ)^55 := by
    have hnat : (1531410643 : ℕ)^71*100000000000000^55 ≤ 8872120198707^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531410643 10000000000 8872120198707 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358888701/2500000000 : ℝ)^71 ≤ (45522270633231/100000000000000 : ℝ)^55 := by
    have hnat : (1358888701 : ℕ)^71*100000000000000^55 ≤ 45522270633231^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358888701 2500000000 45522270633231 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5443261719/10000000000 : ℝ), (-1531410643/10000000000 : ℝ), (1358888701/2500000000 : ℝ)] ![(45605609155169/100000000000000 : ℝ), (8872120198707/100000000000000 : ℝ), (45522270633231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5443261719/10000000000 : ℝ)|^71 ≤ (45605609155169/100000000000000 : ℝ)^55
        have hw : |(5443261719/10000000000 : ℝ)|=(5443261719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1531410643/10000000000 : ℝ)|^71 ≤ (8872120198707/100000000000000 : ℝ)^55
        have hw : |(-1531410643/10000000000 : ℝ)|=(1531410643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358888701/2500000000 : ℝ)|^71 ≤ (45522270633231/100000000000000 : ℝ)^55
        have hw : |(1358888701/2500000000 : ℝ)|=(1358888701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5435556219/10000000000 : ℝ)*x 0 + (1360815027/2500000000 : ℝ)*x 1 + (-95713183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5435556219/10000000000 : ℝ)^71 ≤ (45522285931143/100000000000000 : ℝ)^55 := by
    have hnat : (5435556219 : ℕ)^71*100000000000000^55 ≤ 45522285931143^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435556219 10000000000 45522285931143 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360815027/2500000000 : ℝ)^71 ≤ (22802795865537/50000000000000 : ℝ)^55 := by
    have hnat : (1360815027 : ℕ)^71*50000000000000^55 ≤ 22802795865537^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360815027 2500000000 22802795865537 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95713183/625000000 : ℝ)^71 ≤ (8872122330163/100000000000000 : ℝ)^55 := by
    have hnat : (95713183 : ℕ)^71*100000000000000^55 ≤ 8872122330163^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95713183 625000000 8872122330163 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5435556219/10000000000 : ℝ), (1360815027/2500000000 : ℝ), (-95713183/625000000 : ℝ)] ![(45522285931143/100000000000000 : ℝ), (22802795865537/50000000000000 : ℝ), (8872122330163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5435556219/10000000000 : ℝ)|^71 ≤ (45522285931143/100000000000000 : ℝ)^55
        have hw : |(5435556219/10000000000 : ℝ)|=(5435556219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360815027/2500000000 : ℝ)|^71 ≤ (22802795865537/50000000000000 : ℝ)^55
        have hw : |(1360815027/2500000000 : ℝ)|=(1360815027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95713183/625000000 : ℝ)|^71 ≤ (8872122330163/100000000000000 : ℝ)^55
        have hw : |(-95713183/625000000 : ℝ)|=(95713183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1406885993/10000000000 : ℝ)*x 0 + (54356287/125000000 : ℝ)*x 1 + (1310076799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1406885993/10000000000 : ℝ)^71 ≤ (1988015138067/25000000000000 : ℝ)^55 := by
    have hnat : (1406885993 : ℕ)^71*25000000000000^55 ≤ 1988015138067^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406885993 10000000000 1988015138067 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54356287/125000000 : ℝ)^71 ≤ (3412946820719/10000000000000 : ℝ)^55 := by
    have hnat : (54356287 : ℕ)^71*10000000000000^55 ≤ 3412946820719^55*125000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54356287 125000000 3412946820719 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310076799/2000000000 : ℝ)^71 ≤ (57918471220723/100000000000000 : ℝ)^55 := by
    have hnat : (1310076799 : ℕ)^71*100000000000000^55 ≤ 57918471220723^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310076799 2000000000 57918471220723 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1406885993/10000000000 : ℝ), (54356287/125000000 : ℝ), (1310076799/2000000000 : ℝ)] ![(1988015138067/25000000000000 : ℝ), (3412946820719/10000000000000 : ℝ), (57918471220723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1406885993/10000000000 : ℝ)|^71 ≤ (1988015138067/25000000000000 : ℝ)^55
        have hw : |(-1406885993/10000000000 : ℝ)|=(1406885993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54356287/125000000 : ℝ)|^71 ≤ (3412946820719/10000000000000 : ℝ)^55
        have hw : |(54356287/125000000 : ℝ)|=(54356287/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310076799/2000000000 : ℝ)|^71 ≤ (57918471220723/100000000000000 : ℝ)^55
        have hw : |(1310076799/2000000000 : ℝ)|=(1310076799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5697276703/10000000000 : ℝ)*x 0 + (-116051747/2000000000 : ℝ)*x 1 + (5763074479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5697276703/10000000000 : ℝ)^71 ≤ (24185703085261/50000000000000 : ℝ)^55 := by
    have hnat : (5697276703 : ℕ)^71*50000000000000^55 ≤ 24185703085261^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697276703 10000000000 24185703085261 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116051747/2000000000 : ℝ)^71 ≤ (2534825081973/100000000000000 : ℝ)^55 := by
    have hnat : (116051747 : ℕ)^71*100000000000000^55 ≤ 2534825081973^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116051747 2000000000 2534825081973 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5763074479/10000000000 : ℝ)^71 ≤ (12273442184939/25000000000000 : ℝ)^55 := by
    have hnat : (5763074479 : ℕ)^71*25000000000000^55 ≤ 12273442184939^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5763074479 10000000000 12273442184939 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5697276703/10000000000 : ℝ), (-116051747/2000000000 : ℝ), (5763074479/10000000000 : ℝ)] ![(24185703085261/50000000000000 : ℝ), (2534825081973/100000000000000 : ℝ), (12273442184939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5697276703/10000000000 : ℝ)|^71 ≤ (24185703085261/50000000000000 : ℝ)^55
        have hw : |(5697276703/10000000000 : ℝ)|=(5697276703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116051747/2000000000 : ℝ)|^71 ≤ (2534825081973/100000000000000 : ℝ)^55
        have hw : |(-116051747/2000000000 : ℝ)|=(116051747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5763074479/10000000000 : ℝ)|^71 ≤ (12273442184939/25000000000000 : ℝ)^55
        have hw : |(5763074479/10000000000 : ℝ)|=(5763074479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (532626121/1250000000 : ℝ)*x 0 + (8911467/12500000 : ℝ)*x 1 + (-510090159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532626121/1250000000 : ℝ)^71 ≤ (33245605824301/100000000000000 : ℝ)^55 := by
    have hnat : (532626121 : ℕ)^71*100000000000000^55 ≤ 33245605824301^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532626121 1250000000 33245605824301 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8911467/12500000 : ℝ)^71 ≤ (646080977911/1000000000000 : ℝ)^55 := by
    have hnat : (8911467 : ℕ)^71*1000000000000^55 ≤ 646080977911^55*12500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8911467 12500000 646080977911 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510090159/10000000000 : ℝ)^71 ≤ (2146296377263/100000000000000 : ℝ)^55 := by
    have hnat : (510090159 : ℕ)^71*100000000000000^55 ≤ 2146296377263^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510090159 10000000000 2146296377263 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532626121/1250000000 : ℝ), (8911467/12500000 : ℝ), (-510090159/10000000000 : ℝ)] ![(33245605824301/100000000000000 : ℝ), (646080977911/1000000000000 : ℝ), (2146296377263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532626121/1250000000 : ℝ)|^71 ≤ (33245605824301/100000000000000 : ℝ)^55
        have hw : |(532626121/1250000000 : ℝ)|=(532626121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8911467/12500000 : ℝ)|^71 ≤ (646080977911/1000000000000 : ℝ)^55
        have hw : |(8911467/12500000 : ℝ)|=(8911467/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510090159/10000000000 : ℝ)|^71 ≤ (2146296377263/100000000000000 : ℝ)^55
        have hw : |(-510090159/10000000000 : ℝ)|=(510090159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3657278017/10000000000 : ℝ)*x 0 + (1349686223/2500000000 : ℝ)*x 1 + (1843470103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3657278017/10000000000 : ℝ)^71 ≤ (13647297649989/50000000000000 : ℝ)^55 := by
    have hnat : (3657278017 : ℕ)^71*50000000000000^55 ≤ 13647297649989^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657278017 10000000000 13647297649989 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349686223/2500000000 : ℝ)^71 ≤ (45124702299309/100000000000000 : ℝ)^55 := by
    have hnat : (1349686223 : ℕ)^71*100000000000000^55 ≤ 45124702299309^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349686223 2500000000 45124702299309 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843470103/5000000000 : ℝ)^71 ≤ (3447587797049/12500000000000 : ℝ)^55 := by
    have hnat : (1843470103 : ℕ)^71*12500000000000^55 ≤ 3447587797049^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843470103 5000000000 3447587797049 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3657278017/10000000000 : ℝ), (1349686223/2500000000 : ℝ), (1843470103/5000000000 : ℝ)] ![(13647297649989/50000000000000 : ℝ), (45124702299309/100000000000000 : ℝ), (3447587797049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3657278017/10000000000 : ℝ)|^71 ≤ (13647297649989/50000000000000 : ℝ)^55
        have hw : |(3657278017/10000000000 : ℝ)|=(3657278017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349686223/2500000000 : ℝ)|^71 ≤ (45124702299309/100000000000000 : ℝ)^55
        have hw : |(1349686223/2500000000 : ℝ)|=(1349686223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1843470103/5000000000 : ℝ)|^71 ≤ (3447587797049/12500000000000 : ℝ)^55
        have hw : |(1843470103/5000000000 : ℝ)|=(1843470103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-127522543/2500000000 : ℝ)*x 0 + (2130504477/5000000000 : ℝ)*x 1 + (1425834721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127522543/2500000000 : ℝ)^71 ≤ (536574111969/25000000000000 : ℝ)^55 := by
    have hnat : (127522543 : ℕ)^71*25000000000000^55 ≤ 536574111969^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127522543 2500000000 536574111969 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130504477/5000000000 : ℝ)^71 ≤ (8311401420823/25000000000000 : ℝ)^55 := by
    have hnat : (2130504477 : ℕ)^71*25000000000000^55 ≤ 8311401420823^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130504477 5000000000 8311401420823 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1425834721/2000000000 : ℝ)^71 ≤ (32304048924797/50000000000000 : ℝ)^55 := by
    have hnat : (1425834721 : ℕ)^71*50000000000000^55 ≤ 32304048924797^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425834721 2000000000 32304048924797 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127522543/2500000000 : ℝ), (2130504477/5000000000 : ℝ), (1425834721/2000000000 : ℝ)] ![(536574111969/25000000000000 : ℝ), (8311401420823/25000000000000 : ℝ), (32304048924797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127522543/2500000000 : ℝ)|^71 ≤ (536574111969/25000000000000 : ℝ)^55
        have hw : |(-127522543/2500000000 : ℝ)|=(127522543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2130504477/5000000000 : ℝ)|^71 ≤ (8311401420823/25000000000000 : ℝ)^55
        have hw : |(2130504477/5000000000 : ℝ)|=(2130504477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1425834721/2000000000 : ℝ)|^71 ≤ (32304048924797/50000000000000 : ℝ)^55
        have hw : |(1425834721/2000000000 : ℝ)|=(1425834721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1637596013/2500000000 : ℝ)*x 0 + (-87930373/625000000 : ℝ)*x 1 + (2174251457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1637596013/2500000000 : ℝ)^71 ≤ (28959235935667/50000000000000 : ℝ)^55 := by
    have hnat : (1637596013 : ℕ)^71*50000000000000^55 ≤ 28959235935667^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637596013 2500000000 28959235935667 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87930373/625000000 : ℝ)^71 ≤ (1590412073971/20000000000000 : ℝ)^55 := by
    have hnat : (87930373 : ℕ)^71*20000000000000^55 ≤ 1590412073971^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87930373 625000000 1590412073971 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174251457/5000000000 : ℝ)^71 ≤ (4266183467641/12500000000000 : ℝ)^55 := by
    have hnat : (2174251457 : ℕ)^71*12500000000000^55 ≤ 4266183467641^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174251457 5000000000 4266183467641 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1637596013/2500000000 : ℝ), (-87930373/625000000 : ℝ), (2174251457/5000000000 : ℝ)] ![(28959235935667/50000000000000 : ℝ), (1590412073971/20000000000000 : ℝ), (4266183467641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1637596013/2500000000 : ℝ)|^71 ≤ (28959235935667/50000000000000 : ℝ)^55
        have hw : |(1637596013/2500000000 : ℝ)|=(1637596013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87930373/625000000 : ℝ)|^71 ≤ (1590412073971/20000000000000 : ℝ)^55
        have hw : |(-87930373/625000000 : ℝ)|=(87930373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2174251457/5000000000 : ℝ)|^71 ≤ (4266183467641/12500000000000 : ℝ)^55
        have hw : |(2174251457/5000000000 : ℝ)|=(2174251457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (720384307/1250000000 : ℝ)*x 0 + (1424319179/2500000000 : ℝ)*x 1 + (-290129377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720384307/1250000000 : ℝ)^71 ≤ (49093768486829/100000000000000 : ℝ)^55 := by
    have hnat : (720384307 : ℕ)^71*100000000000000^55 ≤ 49093768486829^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720384307 1250000000 49093768486829 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424319179/2500000000 : ℝ)^71 ≤ (12092851578251/25000000000000 : ℝ)^55 := by
    have hnat : (1424319179 : ℕ)^71*25000000000000^55 ≤ 12092851578251^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424319179 2500000000 12092851578251 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290129377/5000000000 : ℝ)^71 ≤ (2534825189119/100000000000000 : ℝ)^55 := by
    have hnat : (290129377 : ℕ)^71*100000000000000^55 ≤ 2534825189119^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290129377 5000000000 2534825189119 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(720384307/1250000000 : ℝ), (1424319179/2500000000 : ℝ), (-290129377/5000000000 : ℝ)] ![(49093768486829/100000000000000 : ℝ), (12092851578251/25000000000000 : ℝ), (2534825189119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(720384307/1250000000 : ℝ)|^71 ≤ (49093768486829/100000000000000 : ℝ)^55
        have hw : |(720384307/1250000000 : ℝ)|=(720384307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424319179/2500000000 : ℝ)|^71 ≤ (12092851578251/25000000000000 : ℝ)^55
        have hw : |(1424319179/2500000000 : ℝ)|=(1424319179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290129377/5000000000 : ℝ)|^71 ≤ (2534825189119/100000000000000 : ℝ)^55
        have hw : |(-290129377/5000000000 : ℝ)|=(290129377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (921735047/2500000000 : ℝ)*x 0 + (57144969/156250000 : ℝ)*x 1 + (539874491/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921735047/2500000000 : ℝ)^71 ≤ (27580702202569/100000000000000 : ℝ)^55 := by
    have hnat : (921735047 : ℕ)^71*100000000000000^55 ≤ 27580702202569^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921735047 2500000000 27580702202569 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57144969/156250000 : ℝ)^71 ≤ (3411824411293/12500000000000 : ℝ)^55 := by
    have hnat : (57144969 : ℕ)^71*12500000000000^55 ≤ 3411824411293^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57144969 156250000 3411824411293 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539874491/1000000000 : ℝ)^71 ≤ (45124702493527/100000000000000 : ℝ)^55 := by
    have hnat : (539874491 : ℕ)^71*100000000000000^55 ≤ 45124702493527^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539874491 1000000000 45124702493527 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(921735047/2500000000 : ℝ), (57144969/156250000 : ℝ), (539874491/1000000000 : ℝ)] ![(27580702202569/100000000000000 : ℝ), (3411824411293/12500000000000 : ℝ), (45124702493527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(921735047/2500000000 : ℝ)|^71 ≤ (27580702202569/100000000000000 : ℝ)^55
        have hw : |(921735047/2500000000 : ℝ)|=(921735047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57144969/156250000 : ℝ)|^71 ≤ (3411824411293/12500000000000 : ℝ)^55
        have hw : |(57144969/156250000 : ℝ)|=(57144969/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539874491/1000000000 : ℝ)|^71 ≤ (45124702493527/100000000000000 : ℝ)^55
        have hw : |(539874491/1000000000 : ℝ)|=(539874491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-58025873/1000000000 : ℝ)*x 0 + (1152614897/2000000000 : ℝ)*x 1 + (5697276699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58025873/1000000000 : ℝ)^71 ≤ (2534825053777/100000000000000 : ℝ)^55 := by
    have hnat : (58025873 : ℕ)^71*100000000000000^55 ≤ 2534825053777^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58025873 1000000000 2534825053777 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152614897/2000000000 : ℝ)^71 ≤ (49093768805737/100000000000000 : ℝ)^55 := by
    have hnat : (1152614897 : ℕ)^71*100000000000000^55 ≤ 49093768805737^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152614897 2000000000 49093768805737 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5697276699/10000000000 : ℝ)^71 ≤ (48371406126681/100000000000000 : ℝ)^55 := by
    have hnat : (5697276699 : ℕ)^71*100000000000000^55 ≤ 48371406126681^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697276699 10000000000 48371406126681 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58025873/1000000000 : ℝ), (1152614897/2000000000 : ℝ), (5697276699/10000000000 : ℝ)] ![(2534825053777/100000000000000 : ℝ), (49093768805737/100000000000000 : ℝ), (48371406126681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58025873/1000000000 : ℝ)|^71 ≤ (2534825053777/100000000000000 : ℝ)^55
        have hw : |(-58025873/1000000000 : ℝ)|=(58025873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1152614897/2000000000 : ℝ)|^71 ≤ (49093768805737/100000000000000 : ℝ)^55
        have hw : |(1152614897/2000000000 : ℝ)|=(1152614897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5697276699/10000000000 : ℝ)|^71 ≤ (48371406126681/100000000000000 : ℝ)^55
        have hw : |(5697276699/10000000000 : ℝ)|=(5697276699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3564586799/5000000000 : ℝ)*x 0 + (-127522539/2500000000 : ℝ)*x 1 + (4261008971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3564586799/5000000000 : ℝ)^71 ≤ (32304048883851/50000000000000 : ℝ)^55 := by
    have hnat : (3564586799 : ℕ)^71*50000000000000^55 ≤ 32304048883851^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3564586799 5000000000 32304048883851 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127522539/2500000000 : ℝ)^71 ≤ (268287045121/12500000000000 : ℝ)^55 := by
    have hnat : (127522539 : ℕ)^71*12500000000000^55 ≤ 268287045121^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127522539 2500000000 268287045121 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4261008971/10000000000 : ℝ)^71 ≤ (33245605854517/100000000000000 : ℝ)^55 := by
    have hnat : (4261008971 : ℕ)^71*100000000000000^55 ≤ 33245605854517^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261008971 10000000000 33245605854517 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3564586799/5000000000 : ℝ), (-127522539/2500000000 : ℝ), (4261008971/10000000000 : ℝ)] ![(32304048883851/50000000000000 : ℝ), (268287045121/12500000000000 : ℝ), (33245605854517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3564586799/5000000000 : ℝ)|^71 ≤ (32304048883851/50000000000000 : ℝ)^55
        have hw : |(3564586799/5000000000 : ℝ)|=(3564586799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127522539/2500000000 : ℝ)|^71 ≤ (268287045121/12500000000000 : ℝ)^55
        have hw : |(-127522539/2500000000 : ℝ)|=(127522539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4261008971/10000000000 : ℝ)|^71 ≤ (33245605854517/100000000000000 : ℝ)^55
        have hw : |(4261008971/10000000000 : ℝ)|=(4261008971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1087125743/2500000000 : ℝ)*x 0 + (327519199/500000000 : ℝ)*x 1 + (-703443/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087125743/2500000000 : ℝ)^71 ≤ (34129468328771/100000000000000 : ℝ)^55 := by
    have hnat : (1087125743 : ℕ)^71*100000000000000^55 ≤ 34129468328771^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087125743 2500000000 34129468328771 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327519199/500000000 : ℝ)^71 ≤ (5791847104951/10000000000000 : ℝ)^55 := by
    have hnat : (327519199 : ℕ)^71*10000000000000^55 ≤ 5791847104951^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327519199 500000000 5791847104951 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703443/5000000 : ℝ)^71 ≤ (497003787709/6250000000000 : ℝ)^55 := by
    have hnat : (703443 : ℕ)^71*6250000000000^55 ≤ 497003787709^55*5000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703443 5000000 497003787709 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087125743/2500000000 : ℝ), (327519199/500000000 : ℝ), (-703443/5000000 : ℝ)] ![(34129468328771/100000000000000 : ℝ), (5791847104951/10000000000000 : ℝ), (497003787709/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087125743/2500000000 : ℝ)|^71 ≤ (34129468328771/100000000000000 : ℝ)^55
        have hw : |(1087125743/2500000000 : ℝ)|=(1087125743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327519199/500000000 : ℝ)|^71 ≤ (5791847104951/10000000000000 : ℝ)^55
        have hw : |(327519199/500000000 : ℝ)|=(327519199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-703443/5000000 : ℝ)|^71 ≤ (497003787709/6250000000000 : ℝ)^55
        have hw : |(-703443/5000000 : ℝ)|=(703443/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310087_s3_s3_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (674843111/1250000000 : ℝ)*x 0 + (3686940211/10000000000 : ℝ)*x 1 + (3657278017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674843111/1250000000 : ℝ)^71 ≤ (45124702256149/100000000000000 : ℝ)^55 := by
    have hnat : (674843111 : ℕ)^71*100000000000000^55 ≤ 45124702256149^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674843111 1250000000 45124702256149 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3686940211/10000000000 : ℝ)^71 ≤ (6895175606169/25000000000000 : ℝ)^55 := by
    have hnat : (3686940211 : ℕ)^71*25000000000000^55 ≤ 6895175606169^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686940211 10000000000 6895175606169 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3657278017/10000000000 : ℝ)^71 ≤ (13647297649989/50000000000000 : ℝ)^55 := by
    have hnat : (3657278017 : ℕ)^71*50000000000000^55 ≤ 13647297649989^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657278017 10000000000 13647297649989 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674843111/1250000000 : ℝ), (3686940211/10000000000 : ℝ), (3657278017/10000000000 : ℝ)] ![(45124702256149/100000000000000 : ℝ), (6895175606169/25000000000000 : ℝ), (13647297649989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674843111/1250000000 : ℝ)|^71 ≤ (45124702256149/100000000000000 : ℝ)^55
        have hw : |(674843111/1250000000 : ℝ)|=(674843111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3686940211/10000000000 : ℝ)|^71 ≤ (6895175606169/25000000000000 : ℝ)^55
        have hw : |(3686940211/10000000000 : ℝ)|=(3686940211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3657278017/10000000000 : ℝ)|^71 ≤ (13647297649989/50000000000000 : ℝ)^55
        have hw : |(3657278017/10000000000 : ℝ)|=(3657278017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310087_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((13121/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13121/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((13121/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(13121/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13121/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13121/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6929/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6929/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6929/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6929/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (13121/25000 : ℝ) ^ (35/8 : ℝ) ≤ (744779677716454633/12500000000000000000 : ℝ) := by
    have hpowers : (13121/25000 : ℝ)^35 ≤ (744779677716454633/12500000000000000000 : ℝ)^8 := by
      have hnat : (13121 : ℕ)^35*12500000000000000000^8 ≤ 744779677716454633^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13121 25000 744779677716454633 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13121/25000 : ℝ)) (X := (744779677716454633/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (13244779677716454633/12500000000000000000 : ℝ) ≤ (5066582099635721/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13244779677716454633/12500000000000000000 : ℝ)^8 ≤ (5066582099635721/5000000000000000 : ℝ)^35 := by
      have hnat : (13244779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5066582099635721^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13244779677716454633 12500000000000000000 5066582099635721 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5066582099635721/5000000000000000 : ℝ)) (X := (13244779677716454633/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (6994779677716454633/6250000000000000000 : ℝ) ≤ (5130335665108403/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6994779677716454633/6250000000000000000 : ℝ)^8 ≤ (5130335665108403/5000000000000000 : ℝ)^35 := by
      have hnat : (6994779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5130335665108403^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6994779677716454633 6250000000000000000 5130335665108403 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5130335665108403/5000000000000000 : ℝ)) (X := (6994779677716454633/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (13121/25000 : ℝ)) (alpha := (66582099635721/2624200000000000 : ℝ)) (beta := (31876782736341/1312100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13121/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (13121/25000 : ℝ) ^ (35/8 : ℝ) ≤ (744779677716454633/12500000000000000000 : ℝ) := by
    have hpowers : (13121/25000 : ℝ)^35 ≤ (744779677716454633/12500000000000000000 : ℝ)^8 := by
      have hnat : (13121 : ℕ)^35*12500000000000000000^8 ≤ 744779677716454633^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13121 25000 744779677716454633 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13121/25000 : ℝ)) (X := (744779677716454633/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (13244779677716454633/12500000000000000000 : ℝ) ≤ (5066582099635721/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13244779677716454633/12500000000000000000 : ℝ)^8 ≤ (5066582099635721/5000000000000000 : ℝ)^35 := by
      have hnat : (13244779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5066582099635721^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13244779677716454633 12500000000000000000 5066582099635721 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5066582099635721/5000000000000000 : ℝ)) (X := (13244779677716454633/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (6994779677716454633/6250000000000000000 : ℝ) ≤ (5130335665108403/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6994779677716454633/6250000000000000000 : ℝ)^8 ≤ (5130335665108403/5000000000000000 : ℝ)^35 := by
      have hnat : (6994779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5130335665108403^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6994779677716454633 6250000000000000000 5130335665108403 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5130335665108403/5000000000000000 : ℝ)) (X := (6994779677716454633/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (13121/25000 : ℝ)) (alpha := (66582099635721/2624200000000000 : ℝ)) (beta := (31876782736341/1312100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (13121/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (13121/25000 : ℝ) ^ (35/8 : ℝ) ≤ (744779677716454633/12500000000000000000 : ℝ) := by
    have hpowers : (13121/25000 : ℝ)^35 ≤ (744779677716454633/12500000000000000000 : ℝ)^8 := by
      have hnat : (13121 : ℕ)^35*12500000000000000000^8 ≤ 744779677716454633^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13121 25000 744779677716454633 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13121/25000 : ℝ)) (X := (744779677716454633/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (13244779677716454633/12500000000000000000 : ℝ) ≤ (5066582099635721/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13244779677716454633/12500000000000000000 : ℝ)^8 ≤ (5066582099635721/5000000000000000 : ℝ)^35 := by
      have hnat : (13244779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5066582099635721^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13244779677716454633 12500000000000000000 5066582099635721 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5066582099635721/5000000000000000 : ℝ)) (X := (13244779677716454633/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (6994779677716454633/6250000000000000000 : ℝ) ≤ (5130335665108403/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6994779677716454633/6250000000000000000 : ℝ)^8 ≤ (5130335665108403/5000000000000000 : ℝ)^35 := by
      have hnat : (6994779677716454633 : ℕ)^8*5000000000000000^35 ≤ 5130335665108403^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6994779677716454633 6250000000000000000 5130335665108403 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5130335665108403/5000000000000000 : ℝ)) (X := (6994779677716454633/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (13121/25000 : ℝ)) (alpha := (66582099635721/2624200000000000 : ℝ)) (beta := (31876782736341/1312100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13121/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(66582099635721/2624200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(31876782736341/1312100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-765704829/5000000000 : ℝ)*X 0 0+(5435556189/10000000000 : ℝ)*X 0 1+(680407627/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5443261719/10000000000 : ℝ)*X 1 0+(-1531410643/10000000000 : ℝ)*X 1 1+(1358888701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5435556219/10000000000 : ℝ)*X 2 0+(1360815027/2500000000 : ℝ)*X 2 1+(-95713183/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1406885993/10000000000 : ℝ)*X 0 0+(54356287/125000000 : ℝ)*X 0 1+(1310076799/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((5697276703/10000000000 : ℝ)*X 1 0+(-116051747/2000000000 : ℝ)*X 1 1+(5763074479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((532626121/1250000000 : ℝ)*X 2 0+(8911467/12500000 : ℝ)*X 2 1+(-510090159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((3657278017/10000000000 : ℝ)*X 0 0+(1349686223/2500000000 : ℝ)*X 0 1+(1843470103/5000000000 : ℝ)*X 0 2+(3657278017/10000000000 : ℝ)*X 1 0+(1349686223/2500000000 : ℝ)*X 1 1+(1843470103/5000000000 : ℝ)*X 1 2+(3657278017/10000000000 : ℝ)*X 2 0+(1349686223/2500000000 : ℝ)*X 2 1+(1843470103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-127522543/2500000000 : ℝ)*X 0 0+(2130504477/5000000000 : ℝ)*X 0 1+(1425834721/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1637596013/2500000000 : ℝ)*X 1 0+(-87930373/625000000 : ℝ)*X 1 1+(2174251457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((720384307/1250000000 : ℝ)*X 2 0+(1424319179/2500000000 : ℝ)*X 2 1+(-290129377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((921735047/2500000000 : ℝ)*X 0 0+(57144969/156250000 : ℝ)*X 0 1+(539874491/1000000000 : ℝ)*X 0 2+(921735047/2500000000 : ℝ)*X 1 0+(57144969/156250000 : ℝ)*X 1 1+(539874491/1000000000 : ℝ)*X 1 2+(921735047/2500000000 : ℝ)*X 2 0+(57144969/156250000 : ℝ)*X 2 1+(539874491/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-58025873/1000000000 : ℝ)*X 0 0+(1152614897/2000000000 : ℝ)*X 0 1+(5697276699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3564586799/5000000000 : ℝ)*X 1 0+(-127522539/2500000000 : ℝ)*X 1 1+(4261008971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((1087125743/2500000000 : ℝ)*X 2 0+(327519199/500000000 : ℝ)*X 2 1+(-703443/5000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((674843111/1250000000 : ℝ)*X 0 0+(3686940211/10000000000 : ℝ)*X 0 1+(3657278017/10000000000 : ℝ)*X 0 2+(674843111/1250000000 : ℝ)*X 1 0+(3686940211/10000000000 : ℝ)*X 1 1+(3657278017/10000000000 : ℝ)*X 1 2+(674843111/1250000000 : ℝ)*X 2 0+(3686940211/10000000000 : ℝ)*X 2 1+(3657278017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310087_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6929/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1343640357507155145537/262420000000000000000000000 : ℝ) := by norm_num
    linear_combination (241689/62500000000 : ℝ)*(base19) + (91753695597/250000000000 : ℝ)*(base50) + (305548086501/1000000000000 : ℝ)*(base60) + (3407058413197/1000000000000 : ℝ)*(major_s3_0) + (3407058413197/1000000000000 : ℝ)*(major_s3_1) + (3407058413197/1000000000000 : ℝ)*(major_s3_2) + (1091453/50000000000 : ℝ)*(sp_s3_1) + (4708289713661/1000000000000 : ℝ)*(sp_s3_7) + (4708276184933/1000000000000 : ℝ)*(sp_s3_8) + (4708275455143/1000000000000 : ℝ)*(sp_s3_9) + (2105813238643/1000000000000 : ℝ)*(sp_s3_13) + (22557/500000000000 : ℝ)*(sp_s3_14) + (6061121/500000000000 : ℝ)*(sp_s3_21) + (13212937/500000000000 : ℝ)*(sp_s3_23) + (2105813238643/1000000000000 : ℝ)*(f.failure) + (4708301881017/1000000000000 : ℝ)*(f.sum) + (356949537867409/2624200000000000000000000000 : ℝ)*base62 + (1007429812100643/1312100000000000000000000000 : ℝ)*base64 + (211197225050017/2624200000000000000000000000 : ℝ)*base67 + (118924429137363/2624200000000000000000000000 : ℝ)*base68 + (1194716972320429/2624200000000000000000000000 : ℝ)*base70 + (448824934379873/1312100000000000000000000000 : ℝ)*base72 + (986027708266253/1312100000000000000000000000 : ℝ)*base74 + (974703316149883/2624200000000000000000000000 : ℝ)*base76 + (674489534829571/2624200000000000000000000000 : ℝ)*base79 + (66899/100000000000000000 : ℝ)*base87 + (66899/100000000000000000 : ℝ)*base89 + (66899/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6929/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (167921422393234123953/32802500000000000000000000 : ℝ) := by norm_num
    linear_combination (3888477/1000000000000 : ℝ)*(base21) + (38193510639/125000000000 : ℝ)*(base40) + (367014779853/1000000000000 : ℝ)*(base60) + (681411672673/200000000000 : ℝ)*(major_s3_0) + (681411672673/200000000000 : ℝ)*(major_s3_1) + (681411672673/200000000000 : ℝ)*(major_s3_2) + (25571/125000000000 : ℝ)*(sp_s3_1) + (4333269/200000000000 : ℝ)*(sp_s3_2) + (13141781/500000000000 : ℝ)*(sp_s3_7) + (6032863/500000000000 : ℝ)*(sp_s3_8) + (2354137764467/500000000000 : ℝ)*(sp_s3_14) + (2354144771101/500000000000 : ℝ)*(sp_s3_15) + (2354138128837/500000000000 : ℝ)*(sp_s3_16) + (2105813207843/1000000000000 : ℝ)*(sp_s3_20) + (2105813207843/1000000000000 : ℝ)*(f.failure) + (294268863281/62500000000 : ℝ)*(f.sum) + (225799805481461/524840000000000000000000000 : ℝ)*base62 + (11822940567769/52484000000000000000000000 : ℝ)*base65 + (153821614220527/524840000000000000000000000 : ℝ)*base66 + (259412303710639/524840000000000000000000000 : ℝ)*base68 + (15470876037893/524840000000000000000000000 : ℝ)*base70 + (2435866777393/52484000000000000000000000 : ℝ)*base73 + (85361188139193/262420000000000000000000000 : ℝ)*base74 + (20819202552891/104968000000000000000000000 : ℝ)*base76 + (38046604460603/524840000000000000000000000 : ℝ)*base79 + (42499/100000000000000000 : ℝ)*base87 + (42499/100000000000000000 : ℝ)*base89 + (42499/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6929/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6929/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (671786903853869270601/131210000000000000000000000 : ℝ) := by norm_num
    linear_combination (965257/250000000000 : ℝ)*(base11) + (183507391619/500000000000 : ℝ)*(base40) + (152774043427/500000000000 : ℝ)*(base50) + (170352921277/50000000000 : ℝ)*(major_s3_0) + (170352921277/50000000000 : ℝ)*(major_s3_1) + (170352921277/50000000000 : ℝ)*(major_s3_2) + (21871437/1000000000000 : ℝ)*(sp_s3_0) + (12791/125000000000 : ℝ)*(sp_s3_9) + (26458663/1000000000000 : ℝ)*(sp_s3_15) + (6048433/500000000000 : ℝ)*(sp_s3_16) + (4708276165691/1000000000000 : ℝ)*(sp_s3_21) + (2354137719747/500000000000 : ℝ)*(sp_s3_22) + (2354144849481/500000000000 : ℝ)*(sp_s3_23) + (32903331973/15625000000 : ℝ)*(sp_s3_27) + (32903331973/15625000000 : ℝ)*(f.failure) + (4708301898157/1000000000000 : ℝ)*(f.sum) + (4946182836871/131210000000000000000000000 : ℝ)*base63 + (5656573325303/65605000000000000000000000 : ℝ)*base64 + (12275605680227/32802500000000000000000000 : ℝ)*base66 + (94926764686587/131210000000000000000000000 : ℝ)*base68 + (19369588548193/131210000000000000000000000 : ℝ)*base70 + (39677595402983/65605000000000000000000000 : ℝ)*base72 + (7526791574957/65605000000000000000000000 : ℝ)*base75 + (5648929754251/131210000000000000000000000 : ℝ)*base76 + (55181179489837/131210000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (1339/1562500000000000 : ℝ)*base87 + (1339/1562500000000000 : ℝ)*base89 + (1339/1562500000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((13121/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13121/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((13121/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(13121/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13121/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13121/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6929/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6929/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6929/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6929/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6929/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310087_s3 p hpa hpb X hX hprev2

#print axioms solution

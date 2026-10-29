-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:14.324418+00:00
-- url     : https://prove2.me/submissions/40025ecd-554a-469f-a0b2-6733574f09d9

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
theorem collision_support_c310086_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3381129/10000000000 : ℝ)*x 0 + (-3235639311/5000000000 : ℝ)*x 1 + (25994241/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3381129/10000000000 : ℝ)^71 ≤ (165311951/5000000000000 : ℝ)^55 := by
    have hnat : (3381129 : ℕ)^71*5000000000000^55 ≤ 165311951^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381129 10000000000 165311951 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3235639311/5000000000 : ℝ)^71 ≤ (11403427243159/20000000000000 : ℝ)^55 := by
    have hnat : (3235639311 : ℕ)^71*20000000000000^55 ≤ 11403427243159^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3235639311 5000000000 11403427243159 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25994241/50000000 : ℝ)^71 ≤ (4297955753077/10000000000000 : ℝ)^55 := by
    have hnat : (25994241 : ℕ)^71*10000000000000^55 ≤ 4297955753077^55*50000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25994241 50000000 4297955753077 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3381129/10000000000 : ℝ), (-3235639311/5000000000 : ℝ), (25994241/50000000 : ℝ)] ![(165311951/5000000000000 : ℝ), (11403427243159/20000000000000 : ℝ), (4297955753077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3381129/10000000000 : ℝ)|^71 ≤ (165311951/5000000000000 : ℝ)^55
        have hw : |(3381129/10000000000 : ℝ)|=(3381129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3235639311/5000000000 : ℝ)|^71 ≤ (11403427243159/20000000000000 : ℝ)^55
        have hw : |(-3235639311/5000000000 : ℝ)|=(3235639311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25994241/50000000 : ℝ)|^71 ≤ (4297955753077/10000000000000 : ℝ)^55
        have hw : |(25994241/50000000 : ℝ)|=(25994241/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (350060397/1000000000 : ℝ)*x 0 + (-355913193/1250000000 : ℝ)*x 1 + (1248849593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (350060397/1000000000 : ℝ)^71 ≤ (12897336598501/50000000000000 : ℝ)^55 := by
    have hnat : (350060397 : ℕ)^71*50000000000000^55 ≤ 12897336598501^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350060397 1000000000 12897336598501 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355913193/1250000000 : ℝ)^71 ≤ (19757135851201/100000000000000 : ℝ)^55 := by
    have hnat : (355913193 : ℕ)^71*100000000000000^55 ≤ 19757135851201^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355913193 1250000000 19757135851201 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248849593/2000000000 : ℝ)^71 ≤ (43558552749/80000000000 : ℝ)^55 := by
    have hnat : (1248849593 : ℕ)^71*80000000000^55 ≤ 43558552749^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248849593 2000000000 43558552749 80000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(350060397/1000000000 : ℝ), (-355913193/1250000000 : ℝ), (1248849593/2000000000 : ℝ)] ![(12897336598501/50000000000000 : ℝ), (19757135851201/100000000000000 : ℝ), (43558552749/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(350060397/1000000000 : ℝ)|^71 ≤ (12897336598501/50000000000000 : ℝ)^55
        have hw : |(350060397/1000000000 : ℝ)|=(350060397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355913193/1250000000 : ℝ)|^71 ≤ (19757135851201/100000000000000 : ℝ)^55
        have hw : |(-355913193/1250000000 : ℝ)|=(355913193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248849593/2000000000 : ℝ)|^71 ≤ (43558552749/80000000000 : ℝ)^55
        have hw : |(1248849593/2000000000 : ℝ)|=(1248849593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2356141/10000000000 : ℝ)*x 0 + (-4097881709/5000000000 : ℝ)*x 1 + (633033511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2356141/10000000000 : ℝ)^71 ≤ (2074157103/100000000000000 : ℝ)^55 := by
    have hnat : (2356141 : ℕ)^71*100000000000000^55 ≤ 2074157103^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356141 10000000000 2074157103 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4097881709/5000000000 : ℝ)^71 ≤ (15469696162127/20000000000000 : ℝ)^55 := by
    have hnat : (4097881709 : ℕ)^71*20000000000000^55 ≤ 15469696162127^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097881709 5000000000 15469696162127 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633033511/2000000000 : ℝ)^71 ≤ (11324722511303/50000000000000 : ℝ)^55 := by
    have hnat : (633033511 : ℕ)^71*50000000000000^55 ≤ 11324722511303^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633033511 2000000000 11324722511303 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2356141/10000000000 : ℝ), (-4097881709/5000000000 : ℝ), (633033511/2000000000 : ℝ)] ![(2074157103/100000000000000 : ℝ), (15469696162127/20000000000000 : ℝ), (11324722511303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2356141/10000000000 : ℝ)|^71 ≤ (2074157103/100000000000000 : ℝ)^55
        have hw : |(2356141/10000000000 : ℝ)|=(2356141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4097881709/5000000000 : ℝ)|^71 ≤ (15469696162127/20000000000000 : ℝ)^55
        have hw : |(-4097881709/5000000000 : ℝ)|=(4097881709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633033511/2000000000 : ℝ)|^71 ≤ (11324722511303/50000000000000 : ℝ)^55
        have hw : |(633033511/2000000000 : ℝ)|=(633033511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5148845127/10000000000 : ℝ)*x 0 + (956396891/2000000000 : ℝ)*x 1 + (1379497241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5148845127/10000000000 : ℝ)^71 ≤ (42446667289901/100000000000000 : ℝ)^55 := by
    have hnat : (5148845127 : ℕ)^71*100000000000000^55 ≤ 42446667289901^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148845127 10000000000 42446667289901 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956396891/2000000000 : ℝ)^71 ≤ (4822955713999/12500000000000 : ℝ)^55 := by
    have hnat : (956396891 : ℕ)^71*12500000000000^55 ≤ 4822955713999^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956396891 2000000000 4822955713999 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379497241/5000000000 : ℝ)^71 ≤ (1185605436729/6250000000000 : ℝ)^55 := by
    have hnat : (1379497241 : ℕ)^71*6250000000000^55 ≤ 1185605436729^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379497241 5000000000 1185605436729 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5148845127/10000000000 : ℝ), (956396891/2000000000 : ℝ), (1379497241/5000000000 : ℝ)] ![(42446667289901/100000000000000 : ℝ), (4822955713999/12500000000000 : ℝ), (1185605436729/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5148845127/10000000000 : ℝ)|^71 ≤ (42446667289901/100000000000000 : ℝ)^55
        have hw : |(5148845127/10000000000 : ℝ)|=(5148845127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956396891/2000000000 : ℝ)|^71 ≤ (4822955713999/12500000000000 : ℝ)^55
        have hw : |(956396891/2000000000 : ℝ)|=(956396891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379497241/5000000000 : ℝ)|^71 ≤ (1185605436729/6250000000000 : ℝ)^55
        have hw : |(1379497241/5000000000 : ℝ)|=(1379497241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (376946151/625000000 : ℝ)*x 0 + (-1644099771/5000000000 : ℝ)*x 1 + (-831508721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376946151/625000000 : ℝ)^71 ≤ (5206135346663/10000000000000 : ℝ)^55 := by
    have hnat : (376946151 : ℕ)^71*10000000000000^55 ≤ 5206135346663^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376946151 625000000 5206135346663 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1644099771/5000000000 : ℝ)^71 ≤ (38067721723/160000000000 : ℝ)^55 := by
    have hnat : (1644099771 : ℕ)^71*160000000000^55 ≤ 38067721723^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644099771 5000000000 38067721723 160000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831508721/2500000000 : ℝ)^71 ≤ (2414632044369/10000000000000 : ℝ)^55 := by
    have hnat : (831508721 : ℕ)^71*10000000000000^55 ≤ 2414632044369^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831508721 2500000000 2414632044369 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(376946151/625000000 : ℝ), (-1644099771/5000000000 : ℝ), (-831508721/2500000000 : ℝ)] ![(5206135346663/10000000000000 : ℝ), (38067721723/160000000000 : ℝ), (2414632044369/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(376946151/625000000 : ℝ)|^71 ≤ (5206135346663/10000000000000 : ℝ)^55
        have hw : |(376946151/625000000 : ℝ)|=(376946151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1644099771/5000000000 : ℝ)|^71 ≤ (38067721723/160000000000 : ℝ)^55
        have hw : |(-1644099771/5000000000 : ℝ)|=(1644099771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-831508721/2500000000 : ℝ)|^71 ≤ (2414632044369/10000000000000 : ℝ)^55
        have hw : |(-831508721/2500000000 : ℝ)|=(831508721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (712906723/2500000000 : ℝ)*x 0 + (-53499431/500000000 : ℝ)*x 1 + (7970840391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (712906723/2500000000 : ℝ)^71 ≤ (19795852756961/100000000000000 : ℝ)^55 := by
    have hnat : (712906723 : ℕ)^71*100000000000000^55 ≤ 19795852756961^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712906723 2500000000 19795852756961 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53499431/500000000 : ℝ)^71 ≤ (698114639321/12500000000000 : ℝ)^55 := by
    have hnat : (53499431 : ℕ)^71*12500000000000^55 ≤ 698114639321^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53499431 500000000 698114639321 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7970840391/10000000000 : ℝ)^71 ≤ (4663701881973/6250000000000 : ℝ)^55 := by
    have hnat : (7970840391 : ℕ)^71*6250000000000^55 ≤ 4663701881973^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7970840391 10000000000 4663701881973 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(712906723/2500000000 : ℝ), (-53499431/500000000 : ℝ), (7970840391/10000000000 : ℝ)] ![(19795852756961/100000000000000 : ℝ), (698114639321/12500000000000 : ℝ), (4663701881973/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(712906723/2500000000 : ℝ)|^71 ≤ (19795852756961/100000000000000 : ℝ)^55
        have hw : |(712906723/2500000000 : ℝ)|=(712906723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53499431/500000000 : ℝ)|^71 ≤ (698114639321/12500000000000 : ℝ)^55
        have hw : |(-53499431/500000000 : ℝ)|=(53499431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7970840391/10000000000 : ℝ)|^71 ≤ (4663701881973/6250000000000 : ℝ)^55
        have hw : |(7970840391/10000000000 : ℝ)|=(7970840391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951901/10000000000 : ℝ)*x 0 + (-4323857713/10000000000 : ℝ)*x 1 + (145158699/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951901/10000000000 : ℝ)^71 ≤ (162674033/10000000000000 : ℝ)^55 := by
    have hnat : (1951901 : ℕ)^71*10000000000000^55 ≤ 162674033^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951901 10000000000 162674033 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4323857713/10000000000 : ℝ)^71 ≤ (6775994860649/20000000000000 : ℝ)^55 := by
    have hnat : (4323857713 : ℕ)^71*20000000000000^55 ≤ 6775994860649^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323857713 10000000000 6775994860649 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145158699/200000000 : ℝ)^71 ≤ (66118398949373/100000000000000 : ℝ)^55 := by
    have hnat : (145158699 : ℕ)^71*100000000000000^55 ≤ 66118398949373^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145158699 200000000 66118398949373 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951901/10000000000 : ℝ), (-4323857713/10000000000 : ℝ), (145158699/200000000 : ℝ)] ![(162674033/10000000000000 : ℝ), (6775994860649/20000000000000 : ℝ), (66118398949373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951901/10000000000 : ℝ)|^71 ≤ (162674033/10000000000000 : ℝ)^55
        have hw : |(-1951901/10000000000 : ℝ)|=(1951901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4323857713/10000000000 : ℝ)|^71 ≤ (6775994860649/20000000000000 : ℝ)^55
        have hw : |(-4323857713/10000000000 : ℝ)|=(4323857713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145158699/200000000 : ℝ)|^71 ≤ (66118398949373/100000000000000 : ℝ)^55
        have hw : |(145158699/200000000 : ℝ)|=(145158699/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (843103861/1000000000 : ℝ)*x 0 + (195775389/1000000000 : ℝ)*x 1 + (678578581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843103861/1000000000 : ℝ)^71 ≤ (80226751990927/100000000000000 : ℝ)^55 := by
    have hnat : (843103861 : ℕ)^71*100000000000000^55 ≤ 80226751990927^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843103861 1000000000 80226751990927 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195775389/1000000000 : ℝ)^71 ≤ (12182154047709/100000000000000 : ℝ)^55 := by
    have hnat : (195775389 : ℕ)^71*100000000000000^55 ≤ 12182154047709^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195775389 1000000000 12182154047709 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678578581/5000000000 : ℝ)^71 ≤ (7591093947343/100000000000000 : ℝ)^55 := by
    have hnat : (678578581 : ℕ)^71*100000000000000^55 ≤ 7591093947343^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678578581 5000000000 7591093947343 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843103861/1000000000 : ℝ), (195775389/1000000000 : ℝ), (678578581/5000000000 : ℝ)] ![(80226751990927/100000000000000 : ℝ), (12182154047709/100000000000000 : ℝ), (7591093947343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843103861/1000000000 : ℝ)|^71 ≤ (80226751990927/100000000000000 : ℝ)^55
        have hw : |(843103861/1000000000 : ℝ)|=(843103861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195775389/1000000000 : ℝ)|^71 ≤ (12182154047709/100000000000000 : ℝ)^55
        have hw : |(195775389/1000000000 : ℝ)|=(195775389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678578581/5000000000 : ℝ)|^71 ≤ (7591093947343/100000000000000 : ℝ)^55
        have hw : |(678578581/5000000000 : ℝ)|=(678578581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7895325847/10000000000 : ℝ)*x 0 + (-2687616691/10000000000 : ℝ)*x 1 + (-1407088643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7895325847/10000000000 : ℝ)^71 ≤ (9213488294767/12500000000000 : ℝ)^55 := by
    have hnat : (7895325847 : ℕ)^71*12500000000000^55 ≤ 9213488294767^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7895325847 10000000000 9213488294767 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687616691/10000000000 : ℝ)^71 ≤ (18338554409109/100000000000000 : ℝ)^55 := by
    have hnat : (2687616691 : ℕ)^71*100000000000000^55 ≤ 18338554409109^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687616691 10000000000 18338554409109 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1407088643/10000000000 : ℝ)^71 ≤ (7953539225253/100000000000000 : ℝ)^55 := by
    have hnat : (1407088643 : ℕ)^71*100000000000000^55 ≤ 7953539225253^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407088643 10000000000 7953539225253 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7895325847/10000000000 : ℝ), (-2687616691/10000000000 : ℝ), (-1407088643/10000000000 : ℝ)] ![(9213488294767/12500000000000 : ℝ), (18338554409109/100000000000000 : ℝ), (7953539225253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7895325847/10000000000 : ℝ)|^71 ≤ (9213488294767/12500000000000 : ℝ)^55
        have hw : |(7895325847/10000000000 : ℝ)|=(7895325847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2687616691/10000000000 : ℝ)|^71 ≤ (18338554409109/100000000000000 : ℝ)^55
        have hw : |(-2687616691/10000000000 : ℝ)|=(2687616691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1407088643/10000000000 : ℝ)|^71 ≤ (7953539225253/100000000000000 : ℝ)^55
        have hw : |(-1407088643/10000000000 : ℝ)|=(1407088643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1096896707/5000000000 : ℝ)*x 0 + (-752910247/5000000000 : ℝ)*x 1 + (8184251457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096896707/5000000000 : ℝ)^71 ≤ (14110538128377/100000000000000 : ℝ)^55 := by
    have hnat : (1096896707 : ℕ)^71*100000000000000^55 ≤ 14110538128377^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096896707 5000000000 14110538128377 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752910247/5000000000 : ℝ)^71 ≤ (8681203836123/100000000000000 : ℝ)^55 := by
    have hnat : (752910247 : ℕ)^71*100000000000000^55 ≤ 8681203836123^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752910247 5000000000 8681203836123 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8184251457/10000000000 : ℝ)^71 ≤ (3860412901501/5000000000000 : ℝ)^55 := by
    have hnat : (8184251457 : ℕ)^71*5000000000000^55 ≤ 3860412901501^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8184251457 10000000000 3860412901501 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1096896707/5000000000 : ℝ), (-752910247/5000000000 : ℝ), (8184251457/10000000000 : ℝ)] ![(14110538128377/100000000000000 : ℝ), (8681203836123/100000000000000 : ℝ), (3860412901501/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1096896707/5000000000 : ℝ)|^71 ≤ (14110538128377/100000000000000 : ℝ)^55
        have hw : |(1096896707/5000000000 : ℝ)|=(1096896707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-752910247/5000000000 : ℝ)|^71 ≤ (8681203836123/100000000000000 : ℝ)^55
        have hw : |(-752910247/5000000000 : ℝ)|=(752910247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8184251457/10000000000 : ℝ)|^71 ≤ (3860412901501/5000000000000 : ℝ)^55
        have hw : |(8184251457/10000000000 : ℝ)|=(8184251457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2000949/1000000000 : ℝ)*x 0 + (-8185827839/10000000000 : ℝ)*x 1 + (198433513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000949/1000000000 : ℝ)^71 ≤ (32820186409/100000000000000 : ℝ)^55 := by
    have hnat : (2000949 : ℕ)^71*100000000000000^55 ≤ 32820186409^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000949 1000000000 32820186409 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8185827839/10000000000 : ℝ)^71 ≤ (77227455945823/100000000000000 : ℝ)^55 := by
    have hnat : (8185827839 : ℕ)^71*100000000000000^55 ≤ 77227455945823^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8185827839 10000000000 77227455945823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198433513/625000000 : ℝ)^71 ≤ (22739723864239/100000000000000 : ℝ)^55 := by
    have hnat : (198433513 : ℕ)^71*100000000000000^55 ≤ 22739723864239^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198433513 625000000 22739723864239 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2000949/1000000000 : ℝ), (-8185827839/10000000000 : ℝ), (198433513/625000000 : ℝ)] ![(32820186409/100000000000000 : ℝ), (77227455945823/100000000000000 : ℝ), (22739723864239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2000949/1000000000 : ℝ)|^71 ≤ (32820186409/100000000000000 : ℝ)^55
        have hw : |(2000949/1000000000 : ℝ)|=(2000949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8185827839/10000000000 : ℝ)|^71 ≤ (77227455945823/100000000000000 : ℝ)^55
        have hw : |(-8185827839/10000000000 : ℝ)|=(8185827839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198433513/625000000 : ℝ)|^71 ≤ (22739723864239/100000000000000 : ℝ)^55
        have hw : |(198433513/625000000 : ℝ)|=(198433513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8027094307/10000000000 : ℝ)*x 0 + (441420481/2000000000 : ℝ)*x 1 + (1742193301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8027094307/10000000000 : ℝ)^71 ≤ (4706234286841/6250000000000 : ℝ)^55 := by
    have hnat : (8027094307 : ℕ)^71*6250000000000^55 ≤ 4706234286841^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8027094307 10000000000 4706234286841 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441420481/2000000000 : ℝ)^71 ≤ (14221142209881/100000000000000 : ℝ)^55 := by
    have hnat : (441420481 : ℕ)^71*100000000000000^55 ≤ 14221142209881^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441420481 2000000000 14221142209881 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742193301/10000000000 : ℝ)^71 ≤ (1309888648371/12500000000000 : ℝ)^55 := by
    have hnat : (1742193301 : ℕ)^71*12500000000000^55 ≤ 1309888648371^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742193301 10000000000 1309888648371 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8027094307/10000000000 : ℝ), (441420481/2000000000 : ℝ), (1742193301/10000000000 : ℝ)] ![(4706234286841/6250000000000 : ℝ), (14221142209881/100000000000000 : ℝ), (1309888648371/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8027094307/10000000000 : ℝ)|^71 ≤ (4706234286841/6250000000000 : ℝ)^55
        have hw : |(8027094307/10000000000 : ℝ)|=(8027094307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441420481/2000000000 : ℝ)|^71 ≤ (14221142209881/100000000000000 : ℝ)^55
        have hw : |(441420481/2000000000 : ℝ)|=(441420481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1742193301/10000000000 : ℝ)|^71 ≤ (1309888648371/12500000000000 : ℝ)^55
        have hw : |(1742193301/10000000000 : ℝ)|=(1742193301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1001508231/2500000000 : ℝ)*x 0 + (-5437119621/10000000000 : ℝ)*x 1 + (-410601069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001508231/2500000000 : ℝ)^71 ≤ (30700154053967/100000000000000 : ℝ)^55 := by
    have hnat : (1001508231 : ℕ)^71*100000000000000^55 ≤ 30700154053967^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001508231 2500000000 30700154053967 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437119621/10000000000 : ℝ)^71 ≤ (22769594480537/50000000000000 : ℝ)^55 := by
    have hnat : (5437119621 : ℕ)^71*50000000000000^55 ≤ 22769594480537^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437119621 10000000000 22769594480537 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410601069/1250000000 : ℝ)^71 ≤ (23760656975413/100000000000000 : ℝ)^55 := by
    have hnat : (410601069 : ℕ)^71*100000000000000^55 ≤ 23760656975413^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410601069 1250000000 23760656975413 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001508231/2500000000 : ℝ), (-5437119621/10000000000 : ℝ), (-410601069/1250000000 : ℝ)] ![(30700154053967/100000000000000 : ℝ), (22769594480537/50000000000000 : ℝ), (23760656975413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001508231/2500000000 : ℝ)|^71 ≤ (30700154053967/100000000000000 : ℝ)^55
        have hw : |(1001508231/2500000000 : ℝ)|=(1001508231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5437119621/10000000000 : ℝ)|^71 ≤ (22769594480537/50000000000000 : ℝ)^55
        have hw : |(-5437119621/10000000000 : ℝ)|=(5437119621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410601069/1250000000 : ℝ)|^71 ≤ (23760656975413/100000000000000 : ℝ)^55
        have hw : |(-410601069/1250000000 : ℝ)|=(410601069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6491976439/10000000000 : ℝ)*x 0 + (-1445195369/10000000000 : ℝ)*x 1 + (4386472293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6491976439/10000000000 : ℝ)^71 ≤ (28626330698911/50000000000000 : ℝ)^55 := by
    have hnat : (6491976439 : ℕ)^71*50000000000000^55 ≤ 28626330698911^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6491976439 10000000000 28626330698911 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445195369/10000000000 : ℝ)^71 ≤ (8232686178577/100000000000000 : ℝ)^55 := by
    have hnat : (1445195369 : ℕ)^71*100000000000000^55 ≤ 8232686178577^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445195369 10000000000 8232686178577 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386472293/10000000000 : ℝ)^71 ≤ (34514652413251/100000000000000 : ℝ)^55 := by
    have hnat : (4386472293 : ℕ)^71*100000000000000^55 ≤ 34514652413251^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386472293 10000000000 34514652413251 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6491976439/10000000000 : ℝ), (-1445195369/10000000000 : ℝ), (4386472293/10000000000 : ℝ)] ![(28626330698911/50000000000000 : ℝ), (8232686178577/100000000000000 : ℝ), (34514652413251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6491976439/10000000000 : ℝ)|^71 ≤ (28626330698911/50000000000000 : ℝ)^55
        have hw : |(6491976439/10000000000 : ℝ)|=(6491976439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1445195369/10000000000 : ℝ)|^71 ≤ (8232686178577/100000000000000 : ℝ)^55
        have hw : |(-1445195369/10000000000 : ℝ)|=(1445195369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386472293/10000000000 : ℝ)|^71 ≤ (34514652413251/100000000000000 : ℝ)^55
        have hw : |(4386472293/10000000000 : ℝ)|=(4386472293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310086_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((81221/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(81221/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-17857/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-17857/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2772/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2772/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28259/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28259/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-37731/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-37731/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74177/100000 : ℝ)*X 1 2) := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (81221/100000 : ℝ) ^ (35/8 : ℝ) ≤ (20126532456670529241/50000000000000000000 : ℝ) := by
    have hpowers : (81221/100000 : ℝ)^35 ≤ (20126532456670529241/50000000000000000000 : ℝ)^8 := by
      have hnat : (81221 : ℕ)^35*50000000000000000000^8 ≤ 20126532456670529241^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81221 100000 20126532456670529241 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81221/100000 : ℝ)) (X := (20126532456670529241/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (70126532456670529241/50000000000000000000 : ℝ) ≤ (2160777076401377/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (70126532456670529241/50000000000000000000 : ℝ)^8 ≤ (2160777076401377/2000000000000000 : ℝ)^35 := by
      have hnat : (70126532456670529241 : ℕ)^8*2000000000000000^35 ≤ 2160777076401377^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70126532456670529241 50000000000000000000 2160777076401377 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2160777076401377/2000000000000000 : ℝ)) (X := (70126532456670529241/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (45126532456670529241/25000000000000000000 : ℝ) ≤ (2289057637573501/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (45126532456670529241/25000000000000000000 : ℝ)^8 ≤ (2289057637573501/2000000000000000 : ℝ)^35 := by
      have hnat : (45126532456670529241 : ℕ)^8*2000000000000000^35 ≤ 2289057637573501^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45126532456670529241 25000000000000000000 2289057637573501 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2289057637573501/2000000000000000 : ℝ)) (X := (45126532456670529241/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(160777076401377/1624420000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(32070140293031/406105000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (81221/100000 : ℝ)) (alpha := (160777076401377/1624420000000000 : ℝ)) (beta := (32070140293031/406105000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (81221/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(160777076401377/1624420000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(32070140293031/406105000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17857/20000 : ℝ) ^ (35/8 : ℝ) ≤ (6090542112774032339/10000000000000000000 : ℝ) := by
    have hpowers : (17857/20000 : ℝ)^35 ≤ (6090542112774032339/10000000000000000000 : ℝ)^8 := by
      have hnat : (17857 : ℕ)^35*10000000000000000000^8 ≤ 6090542112774032339^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17857 20000 6090542112774032339 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17857/20000 : ℝ)) (X := (6090542112774032339/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (16090542112774032339/10000000000000000000 : ℝ) ≤ (11148492719957373/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (16090542112774032339/10000000000000000000 : ℝ)^8 ≤ (11148492719957373/10000000000000000 : ℝ)^35 := by
      have hnat : (16090542112774032339 : ℕ)^8*10000000000000000^35 ≤ 11148492719957373^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16090542112774032339 10000000000000000000 11148492719957373 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11148492719957373/10000000000000000 : ℝ)) (X := (16090542112774032339/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11090542112774032339/5000000000000000000 : ℝ) ≤ (5998625930785463/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (11090542112774032339/5000000000000000000 : ℝ)^8 ≤ (5998625930785463/5000000000000000 : ℝ)^35 := by
      have hnat : (11090542112774032339 : ℕ)^8*5000000000000000^35 ≤ 5998625930785463^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11090542112774032339 5000000000000000000 5998625930785463 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5998625930785463/5000000000000000 : ℝ)) (X := (11090542112774032339/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(164070388565339/1275500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(848759141613553/8928500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (17857/20000 : ℝ)) (alpha := (164070388565339/1275500000000000 : ℝ)) (beta := (848759141613553/8928500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (17857/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(164070388565339/1275500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(848759141613553/8928500000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2772/3125 : ℝ) ^ (35/8 : ℝ) ≤ (7398804152721209239/12500000000000000000 : ℝ) := by
    have hpowers : (2772/3125 : ℝ)^35 ≤ (7398804152721209239/12500000000000000000 : ℝ)^8 := by
      have hnat : (2772 : ℕ)^35*12500000000000000000^8 ≤ 7398804152721209239^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2772 3125 7398804152721209239 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2772/3125 : ℝ)) (X := (7398804152721209239/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (19898804152721209239/12500000000000000000 : ℝ) ≤ (11121220435597423/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (19898804152721209239/12500000000000000000 : ℝ)^8 ≤ (11121220435597423/10000000000000000 : ℝ)^35 := by
      have hnat : (19898804152721209239 : ℕ)^8*10000000000000000^35 ≤ 11121220435597423^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19898804152721209239 12500000000000000000 11121220435597423 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11121220435597423/10000000000000000 : ℝ)) (X := (19898804152721209239/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13648804152721209239/6250000000000000000 : ℝ) ≤ (11954592099768531/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13648804152721209239/6250000000000000000 : ℝ)^8 ≤ (11954592099768531/10000000000000000 : ℝ)^35 := by
      have hnat : (13648804152721209239 : ℕ)^8*10000000000000000^35 ≤ 11954592099768531^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13648804152721209239 6250000000000000000 11954592099768531 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11954592099768531/10000000000000000 : ℝ)) (X := (13648804152721209239/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(53391449314163/422400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(208342916042777/2217600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2772/3125 : ℝ)) (alpha := (53391449314163/422400000000000 : ℝ)) (beta := (208342916042777/2217600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2772/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(53391449314163/422400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(208342916042777/2217600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((3381129/10000000000 : ℝ)*X 0 0+(-3235639311/5000000000 : ℝ)*X 0 1+(25994241/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((350060397/1000000000 : ℝ)*X 0 0+(-355913193/1250000000 : ℝ)*X 0 1+(1248849593/2000000000 : ℝ)*X 0 2+(350060397/1000000000 : ℝ)*X 1 0+(-355913193/1250000000 : ℝ)*X 1 1+(1248849593/2000000000 : ℝ)*X 1 2+(350060397/1000000000 : ℝ)*X 2 0+(-355913193/1250000000 : ℝ)*X 2 1+(1248849593/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((2356141/10000000000 : ℝ)*X 0 0+(-4097881709/5000000000 : ℝ)*X 0 1+(633033511/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5148845127/10000000000 : ℝ)*X 1 0+(956396891/2000000000 : ℝ)*X 1 1+(1379497241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((376946151/625000000 : ℝ)*X 2 0+(-1644099771/5000000000 : ℝ)*X 2 1+(-831508721/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((712906723/2500000000 : ℝ)*X 0 0+(-53499431/500000000 : ℝ)*X 0 1+(7970840391/10000000000 : ℝ)*X 0 2+(712906723/2500000000 : ℝ)*X 1 0+(-53499431/500000000 : ℝ)*X 1 1+(7970840391/10000000000 : ℝ)*X 1 2+(712906723/2500000000 : ℝ)*X 2 0+(-53499431/500000000 : ℝ)*X 2 1+(7970840391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1951901/10000000000 : ℝ)*X 0 0+(-4323857713/10000000000 : ℝ)*X 0 1+(145158699/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((843103861/1000000000 : ℝ)*X 1 0+(195775389/1000000000 : ℝ)*X 1 1+(678578581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7895325847/10000000000 : ℝ)*X 2 0+(-2687616691/10000000000 : ℝ)*X 2 1+(-1407088643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1096896707/5000000000 : ℝ)*X 0 0+(-752910247/5000000000 : ℝ)*X 0 1+(8184251457/10000000000 : ℝ)*X 0 2+(1096896707/5000000000 : ℝ)*X 1 0+(-752910247/5000000000 : ℝ)*X 1 1+(8184251457/10000000000 : ℝ)*X 1 2+(1096896707/5000000000 : ℝ)*X 2 0+(-752910247/5000000000 : ℝ)*X 2 1+(8184251457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((2000949/1000000000 : ℝ)*X 0 0+(-8185827839/10000000000 : ℝ)*X 0 1+(198433513/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8027094307/10000000000 : ℝ)*X 1 0+(441420481/2000000000 : ℝ)*X 1 1+(1742193301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1001508231/2500000000 : ℝ)*X 2 0+(-5437119621/10000000000 : ℝ)*X 2 1+(-410601069/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6491976439/10000000000 : ℝ)*X 0 0+(-1445195369/10000000000 : ℝ)*X 0 1+(4386472293/10000000000 : ℝ)*X 0 2+(6491976439/10000000000 : ℝ)*X 1 0+(-1445195369/10000000000 : ℝ)*X 1 1+(4386472293/10000000000 : ℝ)*X 1 2+(6491976439/10000000000 : ℝ)*X 2 0+(-1445195369/10000000000 : ℝ)*X 2 1+(4386472293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((28259/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28259/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (76523539501367325650312595871/6630232672000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27037698031/50000000000 : ℝ)*(base7) + (2024089/500000000000 : ℝ)*(base40) + (391219114313/1000000000000 : ℝ)*(base54) + (14129/1000000000000 : ℝ)*(base60) + (1025032478863/500000000000 : ℝ)*(major_s1_0) + (1025032478863/500000000000 : ℝ)*(major_s1_1) + (1658845843413/1000000000000 : ℝ)*(major_s1_2) + (5133163/1000000000000 : ℝ)*(sp_s1_6) + (2502413557193/1000000000000 : ℝ)*(sp_s1_7) + (1253290822521/500000000000 : ℝ)*(sp_s1_8) + (2115362530729/1000000000000 : ℝ)*(sp_s1_9) + (1416531676827/1000000000000 : ℝ)*(sp_s1_13) + (11161687/125000000000 : ℝ)*(sp_s1_20) + (4168087849/1000000000000 : ℝ)*(sp_s1_21) + (633545628589/500000000000 : ℝ)*(f.failure) + (1253290822521/500000000000 : ℝ)*(f.sum) + (433583751264231861/1142848000000000000000000000000 : ℝ)*base62 + (15122701936877/67200000000000000000000000 : ℝ)*base64 + (67102065736867/159437500000000000000000000 : ℝ)*base66 + (4494429664817/12800000000000000000000000 : ℝ)*base68 + (408723405412922071/779721600000000000000000000000 : ℝ)*base70 + (21092280440629/203052500000000000000000000 : ℝ)*base72 + (76260322042389/4464250000000000000000000000 : ℝ)*base75 + (52718908754443/162442000000000000000000000 : ℝ)*base76 + (2122246673843601803/51798692750000000000000000000000 : ℝ)*base78 + (77/50000000000000000 : ℝ)*base87 + (77/50000000000000000 : ℝ)*base89 + (77/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-37731/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-37731/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44137325490743625696209797519/9945349008000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43461227/48828125 : ℝ)*(base7) + (463227/62500000000 : ℝ)*(base33) + (1915846103/125000000000 : ℝ)*(base40) + (45496658511/1000000000000 : ℝ)*(base60) + (173991969917/100000000000 : ℝ)*(major_s1_0) + (869963555401/500000000000 : ℝ)*(major_s1_1) + (869963555401/500000000000 : ℝ)*(major_s1_2) + (14326327/1000000000000 : ℝ)*(sp_s1_9) + (4245643/250000000000 : ℝ)*(sp_s1_13) + (933552329947/500000000000 : ℝ)*(sp_s1_14) + (933521196489/500000000000 : ℝ)*(sp_s1_15) + (373416584387/200000000000 : ℝ)*(sp_s1_16) + (1965472153449/1000000000000 : ℝ)*(sp_s1_20) + (13713821/250000000000 : ℝ)*(sp_s1_22) + (537701603531/500000000000 : ℝ)*(f.failure) + (933552329947/500000000000 : ℝ)*(f.sum) + (10832006516945599927/18856992000000000000000000000000 : ℝ)*base63 + (484035029735263/1108800000000000000000000000 : ℝ)*base65 + (109561402112141/159437500000000000000000000 : ℝ)*base67 + (129316215821003/211200000000000000000000000 : ℝ)*base69 + (3909414858885817709/12865406400000000000000000000000 : ℝ)*base71 + (17574789826539/32488400000000000000000000 : ℝ)*base73 + (448816632667889/2232125000000000000000000000 : ℝ)*base75 + (3653209334561/81221000000000000000000000 : ℝ)*base77 + (35895597376246299719/51798692750000000000000000000000 : ℝ)*base79 + (8917/50000000000000000 : ℝ)*base86 + (8917/50000000000000000 : ℝ)*base88 + (8917/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74177/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3206413501781415465815969/171427200000000000000000000000 : ℝ) := by norm_num
    linear_combination (892985050193/1000000000000 : ℝ)*(base7) + (8789649351/40000000000 : ℝ)*(base40) + (34319716641/200000000000 : ℝ)*(base43) + (852267/200000000000 : ℝ)*(base50) + (1110298842727/500000000000 : ℝ)*(major_s1_0) + (2048999102249/1000000000000 : ℝ)*(major_s1_1) + (1110298842727/500000000000 : ℝ)*(major_s1_2) + (13915267/1000000000000 : ℝ)*(sp_s1_0) + (100762227/1000000000000 : ℝ)*(sp_s1_15) + (21476873/1000000000000 : ℝ)*(sp_s1_16) + (294748563719/125000000000 : ℝ)*(sp_s1_21) + (1264750122999/500000000000 : ℝ)*(sp_s1_22) + (2357980948147/1000000000000 : ℝ)*(sp_s1_23) + (1132739051663/500000000000 : ℝ)*(sp_s1_27) + (343123263283/250000000000 : ℝ)*(f.failure) + (79050031507/31250000000 : ℝ)*(f.sum) + (12393955968078336551/18856992000000000000000000000000 : ℝ)*base62 + (16611916112399/1108800000000000000000000000 : ℝ)*base64 + (406684169945711/1275500000000000000000000000 : ℝ)*base67 + (187049157203899/211200000000000000000000000 : ℝ)*base68 + (2640334943041976317/12865406400000000000000000000000 : ℝ)*base70 + (99220600962671/406105000000000000000000000 : ℝ)*base72 + (8254978699252353/8928500000000000000000000000 : ℝ)*base74 + (355071174157183/812210000000000000000000000 : ℝ)*base77 + (29381317601298196981/103597385500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (3581/25000000000000000 : ℝ)*base86 + (3581/25000000000000000 : ℝ)*base88 + (3581/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((81221/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(81221/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-17857/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-17857/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2772/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2772/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28259/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28259/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-37731/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-37731/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74177/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310086_s1 p hpa hpb X hX hprev0

#print axioms solution

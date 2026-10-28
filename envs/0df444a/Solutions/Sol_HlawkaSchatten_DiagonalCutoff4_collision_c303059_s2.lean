-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:57:00.284242+00:00
-- url     : https://prove2.me/submissions/68e75138-cda2-4f3c-8be4-e15e444ab192

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
theorem collision_support_c303059_s2_s2_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3127556313/10000000000 : ℝ)*x 0 + (781802233/2500000000 : ℝ)*x 1 + (6521822259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3127556313/10000000000 : ℝ)^33 ≤ (21561093469261/100000000000000 : ℝ)^25 := by
    have hnat : (3127556313 : ℕ)^33*100000000000000^25 ≤ 21561093469261^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127556313 10000000000 21561093469261 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781802233/2500000000 : ℝ)^33 ≤ (10778966185783/50000000000000 : ℝ)^25 := by
    have hnat : (781802233 : ℕ)^33*50000000000000^25 ≤ 10778966185783^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781802233 2500000000 10778966185783 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6521822259/10000000000 : ℝ)^33 ≤ (11376194827453/20000000000000 : ℝ)^25 := by
    have hnat : (6521822259 : ℕ)^33*20000000000000^25 ≤ 11376194827453^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6521822259 10000000000 11376194827453 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3127556313/10000000000 : ℝ), (781802233/2500000000 : ℝ), (6521822259/10000000000 : ℝ)] ![(21561093469261/100000000000000 : ℝ), (10778966185783/50000000000000 : ℝ), (11376194827453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3127556313/10000000000 : ℝ)|^33 ≤ (21561093469261/100000000000000 : ℝ)^25
        have hw : |(-3127556313/10000000000 : ℝ)|=(3127556313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781802233/2500000000 : ℝ)|^33 ≤ (10778966185783/50000000000000 : ℝ)^25
        have hw : |(781802233/2500000000 : ℝ)|=(781802233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6521822259/10000000000 : ℝ)|^33 ≤ (11376194827453/20000000000000 : ℝ)^25
        have hw : |(6521822259/10000000000 : ℝ)|=(6521822259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3127372231/10000000000 : ℝ)*x 0 + (-156342453/500000000 : ℝ)*x 1 + (32611261/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3127372231/10000000000 : ℝ)^33 ≤ (4311883669169/20000000000000 : ℝ)^25 := by
    have hnat : (3127372231 : ℕ)^33*20000000000000^25 ≤ 4311883669169^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127372231 10000000000 4311883669169 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156342453/500000000 : ℝ)^33 ≤ (5388664431691/25000000000000 : ℝ)^25 := by
    have hnat : (156342453 : ℕ)^33*25000000000000^25 ≤ 5388664431691^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156342453 500000000 5388664431691 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32611261/50000000 : ℝ)^33 ≤ (56885923912073/100000000000000 : ℝ)^25 := by
    have hnat : (32611261 : ℕ)^33*100000000000000^25 ≤ 56885923912073^25*50000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32611261 50000000 56885923912073 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3127372231/10000000000 : ℝ), (-156342453/500000000 : ℝ), (32611261/50000000 : ℝ)] ![(4311883669169/20000000000000 : ℝ), (5388664431691/25000000000000 : ℝ), (56885923912073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3127372231/10000000000 : ℝ)|^33 ≤ (4311883669169/20000000000000 : ℝ)^25
        have hw : |(3127372231/10000000000 : ℝ)|=(3127372231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156342453/500000000 : ℝ)|^33 ≤ (5388664431691/25000000000000 : ℝ)^25
        have hw : |(-156342453/500000000 : ℝ)|=(156342453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32611261/50000000 : ℝ)|^33 ≤ (56885923912073/100000000000000 : ℝ)^25
        have hw : |(32611261/50000000 : ℝ)|=(32611261/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873000489/10000000000 : ℝ)*x 0 + (91356593/625000000 : ℝ)*x 1 + (1707165863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873000489/10000000000 : ℝ)^33 ≤ (2739618085167/25000000000000 : ℝ)^25 := by
    have hnat : (1873000489 : ℕ)^33*25000000000000^25 ≤ 2739618085167^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873000489 10000000000 2739618085167 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91356593/625000000 : ℝ)^33 ≤ (7899780754831/100000000000000 : ℝ)^25 := by
    have hnat : (91356593 : ℕ)^33*100000000000000^25 ≤ 7899780754831^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91356593 625000000 7899780754831 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707165863/2000000000 : ℝ)^33 ≤ (40570873444397/50000000000000 : ℝ)^25 := by
    have hnat : (1707165863 : ℕ)^33*50000000000000^25 ≤ 40570873444397^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707165863 2000000000 40570873444397 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873000489/10000000000 : ℝ), (91356593/625000000 : ℝ), (1707165863/2000000000 : ℝ)] ![(2739618085167/25000000000000 : ℝ), (7899780754831/100000000000000 : ℝ), (40570873444397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873000489/10000000000 : ℝ)|^33 ≤ (2739618085167/25000000000000 : ℝ)^25
        have hw : |(-1873000489/10000000000 : ℝ)|=(1873000489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91356593/625000000 : ℝ)|^33 ≤ (7899780754831/100000000000000 : ℝ)^25
        have hw : |(91356593/625000000 : ℝ)|=(91356593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1707165863/2000000000 : ℝ)|^33 ≤ (40570873444397/50000000000000 : ℝ)^25
        have hw : |(1707165863/2000000000 : ℝ)|=(1707165863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (991102219/5000000000 : ℝ)*x 0 + (-669872061/5000000000 : ℝ)*x 1 + (8536392983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991102219/5000000000 : ℝ)^33 ≤ (11809620620163/100000000000000 : ℝ)^25 := by
    have hnat : (991102219 : ℕ)^33*100000000000000^25 ≤ 11809620620163^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991102219 5000000000 11809620620163 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669872061/5000000000 : ℝ)^33 ≤ (1760389884063/25000000000000 : ℝ)^25 := by
    have hnat : (669872061 : ℕ)^33*25000000000000^25 ≤ 1760389884063^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669872061 5000000000 1760389884063 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8536392983/10000000000 : ℝ)^33 ≤ (81148819837867/100000000000000 : ℝ)^25 := by
    have hnat : (8536392983 : ℕ)^33*100000000000000^25 ≤ 81148819837867^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8536392983 10000000000 81148819837867 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(991102219/5000000000 : ℝ), (-669872061/5000000000 : ℝ), (8536392983/10000000000 : ℝ)] ![(11809620620163/100000000000000 : ℝ), (1760389884063/25000000000000 : ℝ), (81148819837867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(991102219/5000000000 : ℝ)|^33 ≤ (11809620620163/100000000000000 : ℝ)^25
        have hw : |(991102219/5000000000 : ℝ)|=(991102219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669872061/5000000000 : ℝ)|^33 ≤ (1760389884063/25000000000000 : ℝ)^25
        have hw : |(-669872061/5000000000 : ℝ)|=(669872061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8536392983/10000000000 : ℝ)|^33 ≤ (81148819837867/100000000000000 : ℝ)^25
        have hw : |(8536392983/10000000000 : ℝ)|=(8536392983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4263343713/10000000000 : ℝ)*x 0 + (7427777301/10000000000 : ℝ)*x 1 + (-2346623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263343713/10000000000 : ℝ)^33 ≤ (16227083185863/50000000000000 : ℝ)^25 := by
    have hnat : (4263343713 : ℕ)^33*50000000000000^25 ≤ 16227083185863^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263343713 10000000000 16227083185863 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7427777301/10000000000 : ℝ)^33 ≤ (6753574796061/10000000000000 : ℝ)^25 := by
    have hnat : (7427777301 : ℕ)^33*10000000000000^25 ≤ 6753574796061^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7427777301 10000000000 6753574796061 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2346623/2500000000 : ℝ)^33 ≤ (2521415299/25000000000000 : ℝ)^25 := by
    have hnat : (2346623 : ℕ)^33*25000000000000^25 ≤ 2521415299^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346623 2500000000 2521415299 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263343713/10000000000 : ℝ), (7427777301/10000000000 : ℝ), (-2346623/2500000000 : ℝ)] ![(16227083185863/50000000000000 : ℝ), (6753574796061/10000000000000 : ℝ), (2521415299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263343713/10000000000 : ℝ)|^33 ≤ (16227083185863/50000000000000 : ℝ)^25
        have hw : |(4263343713/10000000000 : ℝ)|=(4263343713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7427777301/10000000000 : ℝ)|^33 ≤ (6753574796061/10000000000000 : ℝ)^25
        have hw : |(7427777301/10000000000 : ℝ)|=(7427777301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2346623/2500000000 : ℝ)|^33 ≤ (2521415299/25000000000000 : ℝ)^25
        have hw : |(-2346623/2500000000 : ℝ)|=(2346623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2096092593/10000000000 : ℝ)*x 0 + (1633702781/2000000000 : ℝ)*x 1 + (460570359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096092593/10000000000 : ℝ)^33 ≤ (6356701466683/50000000000000 : ℝ)^25 := by
    have hnat : (2096092593 : ℕ)^33*50000000000000^25 ≤ 6356701466683^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096092593 10000000000 6356701466683 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1633702781/2000000000 : ℝ)^33 ≤ (15312948615231/20000000000000 : ℝ)^25 := by
    have hnat : (1633702781 : ℕ)^33*20000000000000^25 ≤ 15312948615231^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633702781 2000000000 15312948615231 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460570359/2500000000 : ℝ)^33 ≤ (10721853976853/100000000000000 : ℝ)^25 := by
    have hnat : (460570359 : ℕ)^33*100000000000000^25 ≤ 10721853976853^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460570359 2500000000 10721853976853 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096092593/10000000000 : ℝ), (1633702781/2000000000 : ℝ), (460570359/2500000000 : ℝ)] ![(6356701466683/50000000000000 : ℝ), (15312948615231/20000000000000 : ℝ), (10721853976853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096092593/10000000000 : ℝ)|^33 ≤ (6356701466683/50000000000000 : ℝ)^25
        have hw : |(2096092593/10000000000 : ℝ)|=(2096092593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1633702781/2000000000 : ℝ)|^33 ≤ (15312948615231/20000000000000 : ℝ)^25
        have hw : |(1633702781/2000000000 : ℝ)|=(1633702781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460570359/2500000000 : ℝ)|^33 ≤ (10721853976853/100000000000000 : ℝ)^25
        have hw : |(460570359/2500000000 : ℝ)|=(460570359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-886626459/5000000000 : ℝ)*x 0 + (2132325741/10000000000 : ℝ)*x 1 + (1023449663/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886626459/5000000000 : ℝ)^33 ≤ (127434586711/1250000000000 : ℝ)^25 := by
    have hnat : (886626459 : ℕ)^33*1250000000000^25 ≤ 127434586711^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886626459 5000000000 127434586711 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132325741/10000000000 : ℝ)^33 ≤ (650214559443/5000000000000 : ℝ)^25 := by
    have hnat : (2132325741 : ℕ)^33*5000000000000^25 ≤ 650214559443^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132325741 10000000000 650214559443 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023449663/1250000000 : ℝ)^33 ≤ (15360188372243/20000000000000 : ℝ)^25 := by
    have hnat : (1023449663 : ℕ)^33*20000000000000^25 ≤ 15360188372243^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023449663 1250000000 15360188372243 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886626459/5000000000 : ℝ), (2132325741/10000000000 : ℝ), (1023449663/1250000000 : ℝ)] ![(127434586711/1250000000000 : ℝ), (650214559443/5000000000000 : ℝ), (15360188372243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886626459/5000000000 : ℝ)|^33 ≤ (127434586711/1250000000000 : ℝ)^25
        have hw : |(-886626459/5000000000 : ℝ)|=(886626459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2132325741/10000000000 : ℝ)|^33 ≤ (650214559443/5000000000000 : ℝ)^25
        have hw : |(2132325741/10000000000 : ℝ)|=(2132325741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023449663/1250000000 : ℝ)|^33 ≤ (15360188372243/20000000000000 : ℝ)^25
        have hw : |(1023449663/1250000000 : ℝ)|=(1023449663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (842150701/5000000000 : ℝ)*x 0 + (-1729821/7812500 : ℝ)*x 1 + (2047034279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842150701/5000000000 : ℝ)^33 ≤ (4762600505599/50000000000000 : ℝ)^25 := by
    have hnat : (842150701 : ℕ)^33*50000000000000^25 ≤ 4762600505599^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842150701 5000000000 4762600505599 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729821/7812500 : ℝ)^33 ≤ (3416793298201/25000000000000 : ℝ)^25 := by
    have hnat : (1729821 : ℕ)^33*25000000000000^25 ≤ 3416793298201^25*7812500^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729821 7812500 3416793298201 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047034279/2500000000 : ℝ)^33 ≤ (38403812889651/50000000000000 : ℝ)^25 := by
    have hnat : (2047034279 : ℕ)^33*50000000000000^25 ≤ 38403812889651^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047034279 2500000000 38403812889651 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842150701/5000000000 : ℝ), (-1729821/7812500 : ℝ), (2047034279/2500000000 : ℝ)] ![(4762600505599/50000000000000 : ℝ), (3416793298201/25000000000000 : ℝ), (38403812889651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842150701/5000000000 : ℝ)|^33 ≤ (4762600505599/50000000000000 : ℝ)^25
        have hw : |(842150701/5000000000 : ℝ)|=(842150701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729821/7812500 : ℝ)|^33 ≤ (3416793298201/25000000000000 : ℝ)^25
        have hw : |(-1729821/7812500 : ℝ)|=(1729821/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2047034279/2500000000 : ℝ)|^33 ≤ (38403812889651/50000000000000 : ℝ)^25
        have hw : |(2047034279/2500000000 : ℝ)|=(2047034279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8435217619/10000000000 : ℝ)*x 0 + (2967687859/10000000000 : ℝ)*x 1 + (-147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8435217619/10000000000 : ℝ)^33 ≤ (79881664296397/100000000000000 : ℝ)^25 := by
    have hnat : (8435217619 : ℕ)^33*100000000000000^25 ≤ 79881664296397^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8435217619 10000000000 79881664296397 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2967687859/10000000000 : ℝ)^33 ≤ (4023667137583/20000000000000 : ℝ)^25 := by
    have hnat : (2967687859 : ℕ)^33*20000000000000^25 ≤ 4023667137583^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967687859 10000000000 4023667137583 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147/10000000000 : ℝ)^33 ≤ (229/5000000000000 : ℝ)^25 := by
    have hnat : (147 : ℕ)^33*5000000000000^25 ≤ 229^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147 10000000000 229 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8435217619/10000000000 : ℝ), (2967687859/10000000000 : ℝ), (-147/10000000000 : ℝ)] ![(79881664296397/100000000000000 : ℝ), (4023667137583/20000000000000 : ℝ), (229/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8435217619/10000000000 : ℝ)|^33 ≤ (79881664296397/100000000000000 : ℝ)^25
        have hw : |(8435217619/10000000000 : ℝ)|=(8435217619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2967687859/10000000000 : ℝ)|^33 ≤ (4023667137583/20000000000000 : ℝ)^25
        have hw : |(2967687859/10000000000 : ℝ)|=(2967687859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147/10000000000 : ℝ)|^33 ≤ (229/5000000000000 : ℝ)^25
        have hw : |(-147/10000000000 : ℝ)|=(147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6545327029/10000000000 : ℝ)*x 0 + (819884299/2000000000 : ℝ)*x 1 + (402058811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6545327029/10000000000 : ℝ)^33 ≤ (28575865090749/50000000000000 : ℝ)^25 := by
    have hnat : (6545327029 : ℕ)^33*50000000000000^25 ≤ 28575865090749^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6545327029 10000000000 28575865090749 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819884299/2000000000 : ℝ)^33 ≤ (7704311012031/25000000000000 : ℝ)^25 := by
    have hnat : (819884299 : ℕ)^33*25000000000000^25 ≤ 7704311012031^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819884299 2000000000 7704311012031 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402058811/2000000000 : ℝ)^33 ≤ (150387821971/1250000000000 : ℝ)^25 := by
    have hnat : (402058811 : ℕ)^33*1250000000000^25 ≤ 150387821971^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402058811 2000000000 150387821971 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6545327029/10000000000 : ℝ), (819884299/2000000000 : ℝ), (402058811/2000000000 : ℝ)] ![(28575865090749/50000000000000 : ℝ), (7704311012031/25000000000000 : ℝ), (150387821971/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6545327029/10000000000 : ℝ)|^33 ≤ (28575865090749/50000000000000 : ℝ)^25
        have hw : |(6545327029/10000000000 : ℝ)|=(6545327029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(819884299/2000000000 : ℝ)|^33 ≤ (7704311012031/25000000000000 : ℝ)^25
        have hw : |(819884299/2000000000 : ℝ)|=(819884299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402058811/2000000000 : ℝ)|^33 ≤ (150387821971/1250000000000 : ℝ)^25
        have hw : |(402058811/2000000000 : ℝ)|=(402058811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2725085019/5000000000 : ℝ)*x 0 + (2615626603/10000000000 : ℝ)*x 1 + (4813156747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725085019/5000000000 : ℝ)^33 ≤ (22440435078699/50000000000000 : ℝ)^25 := by
    have hnat : (2725085019 : ℕ)^33*50000000000000^25 ≤ 22440435078699^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725085019 5000000000 22440435078699 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615626603/10000000000 : ℝ)^33 ≤ (8514712505489/50000000000000 : ℝ)^25 := by
    have hnat : (2615626603 : ℕ)^33*50000000000000^25 ≤ 8514712505489^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615626603 10000000000 8514712505489 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813156747/10000000000 : ℝ)^33 ≤ (119030327543/312500000000 : ℝ)^25 := by
    have hnat : (4813156747 : ℕ)^33*312500000000^25 ≤ 119030327543^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813156747 10000000000 119030327543 312500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2725085019/5000000000 : ℝ), (2615626603/10000000000 : ℝ), (4813156747/10000000000 : ℝ)] ![(22440435078699/50000000000000 : ℝ), (8514712505489/50000000000000 : ℝ), (119030327543/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2725085019/5000000000 : ℝ)|^33 ≤ (22440435078699/50000000000000 : ℝ)^25
        have hw : |(-2725085019/5000000000 : ℝ)|=(2725085019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615626603/10000000000 : ℝ)|^33 ≤ (8514712505489/50000000000000 : ℝ)^25
        have hw : |(2615626603/10000000000 : ℝ)|=(2615626603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813156747/10000000000 : ℝ)|^33 ≤ (119030327543/312500000000 : ℝ)^25
        have hw : |(4813156747/10000000000 : ℝ)|=(4813156747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2509707027/10000000000 : ℝ)*x 0 + (-366859443/1250000000 : ℝ)*x 1 + (1783864519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2509707027/10000000000 : ℝ)^33 ≤ (8062549602757/50000000000000 : ℝ)^25 := by
    have hnat : (2509707027 : ℕ)^33*50000000000000^25 ≤ 8062549602757^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509707027 10000000000 8062549602757 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366859443/1250000000 : ℝ)^33 ≤ (19825237097733/100000000000000 : ℝ)^25 := by
    have hnat : (366859443 : ℕ)^33*100000000000000^25 ≤ 19825237097733^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366859443 1250000000 19825237097733 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783864519/2500000000 : ℝ)^33 ≤ (2001551989951/3125000000000 : ℝ)^25 := by
    have hnat : (1783864519 : ℕ)^33*3125000000000^25 ≤ 2001551989951^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783864519 2500000000 2001551989951 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2509707027/10000000000 : ℝ), (-366859443/1250000000 : ℝ), (1783864519/2500000000 : ℝ)] ![(8062549602757/50000000000000 : ℝ), (19825237097733/100000000000000 : ℝ), (2001551989951/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2509707027/10000000000 : ℝ)|^33 ≤ (8062549602757/50000000000000 : ℝ)^25
        have hw : |(2509707027/10000000000 : ℝ)|=(2509707027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366859443/1250000000 : ℝ)|^33 ≤ (19825237097733/100000000000000 : ℝ)^25
        have hw : |(-366859443/1250000000 : ℝ)|=(366859443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1783864519/2500000000 : ℝ)|^33 ≤ (2001551989951/3125000000000 : ℝ)^25
        have hw : |(1783864519/2500000000 : ℝ)|=(1783864519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1037730371/1250000000 : ℝ)*x 0 + (63003777/200000000 : ℝ)*x 1 + (12069849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037730371/1250000000 : ℝ)^33 ≤ (7821865771233/10000000000000 : ℝ)^25 := by
    have hnat : (1037730371 : ℕ)^33*10000000000000^25 ≤ 7821865771233^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037730371 1250000000 7821865771233 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63003777/200000000 : ℝ)^33 ≤ (21767286767303/100000000000000 : ℝ)^25 := by
    have hnat : (63003777 : ℕ)^33*100000000000000^25 ≤ 21767286767303^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63003777 200000000 21767286767303 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12069849/10000000000 : ℝ)^33 ≤ (3513876013/25000000000000 : ℝ)^25 := by
    have hnat : (12069849 : ℕ)^33*25000000000000^25 ≤ 3513876013^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12069849 10000000000 3513876013 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037730371/1250000000 : ℝ), (63003777/200000000 : ℝ), (12069849/10000000000 : ℝ)] ![(7821865771233/10000000000000 : ℝ), (21767286767303/100000000000000 : ℝ), (3513876013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037730371/1250000000 : ℝ)|^33 ≤ (7821865771233/10000000000000 : ℝ)^25
        have hw : |(1037730371/1250000000 : ℝ)|=(1037730371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63003777/200000000 : ℝ)|^33 ≤ (21767286767303/100000000000000 : ℝ)^25
        have hw : |(63003777/200000000 : ℝ)|=(63003777/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12069849/10000000000 : ℝ)|^33 ≤ (3513876013/25000000000000 : ℝ)^25
        have hw : |(12069849/10000000000 : ℝ)|=(12069849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s2_s2_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2114546701/10000000000 : ℝ)*x 0 + (7698881343/10000000000 : ℝ)*x 1 + (2533864171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114546701/10000000000 : ℝ)^33 ≤ (12861357529371/100000000000000 : ℝ)^25 := by
    have hnat : (2114546701 : ℕ)^33*100000000000000^25 ≤ 12861357529371^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114546701 10000000000 12861357529371 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7698881343/10000000000 : ℝ)^33 ≤ (17702087181877/25000000000000 : ℝ)^25 := by
    have hnat : (7698881343 : ℕ)^33*25000000000000^25 ≤ 17702087181877^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7698881343 10000000000 17702087181877 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2533864171/10000000000 : ℝ)^33 ≤ (4082573432693/25000000000000 : ℝ)^25 := by
    have hnat : (2533864171 : ℕ)^33*25000000000000^25 ≤ 4082573432693^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533864171 10000000000 4082573432693 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114546701/10000000000 : ℝ), (7698881343/10000000000 : ℝ), (2533864171/10000000000 : ℝ)] ![(12861357529371/100000000000000 : ℝ), (17702087181877/25000000000000 : ℝ), (4082573432693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114546701/10000000000 : ℝ)|^33 ≤ (12861357529371/100000000000000 : ℝ)^25
        have hw : |(2114546701/10000000000 : ℝ)|=(2114546701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7698881343/10000000000 : ℝ)|^33 ≤ (17702087181877/25000000000000 : ℝ)^25
        have hw : |(7698881343/10000000000 : ℝ)|=(7698881343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2533864171/10000000000 : ℝ)|^33 ≤ (4082573432693/25000000000000 : ℝ)^25
        have hw : |(2533864171/10000000000 : ℝ)|=(2533864171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303059_s2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8897/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8897/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88939/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(88939/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77511/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77511/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (8897/10000 : ℝ) ^ (131/32 : ℝ) ≤ (61974916297635152561/100000000000000000000 : ℝ) := by
    have hpowers : (8897/10000 : ℝ)^131 ≤ (61974916297635152561/100000000000000000000 : ℝ)^32 := by
      have hnat : (8897 : ℕ)^131*100000000000000000000^32 ≤ 61974916297635152561^32*10000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8897 10000 61974916297635152561 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8897/10000 : ℝ)) (X := (61974916297635152561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (161974916297635152561/100000000000000000000 : ℝ) ≤ (2812566640202933/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (161974916297635152561/100000000000000000000 : ℝ)^32 ≤ (2812566640202933/2500000000000000 : ℝ)^131 := by
      have hnat : (161974916297635152561 : ℕ)^32*2500000000000000^131 ≤ 2812566640202933^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        161974916297635152561 100000000000000000000 2812566640202933 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2812566640202933/2500000000000000 : ℝ)) (X := (161974916297635152561/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (111974916297635152561/50000000000000000000 : ℝ) ≤ (12176795311038917/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (111974916297635152561/50000000000000000000 : ℝ)^32 ≤ (12176795311038917/10000000000000000 : ℝ)^131 := by
      have hnat : (111974916297635152561 : ℕ)^32*10000000000000000^131 ≤ 12176795311038917^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111974916297635152561 50000000000000000000 12176795311038917 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12176795311038917/10000000000000000 : ℝ)) (X := (111974916297635152561/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(312566640202933/2224250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26472250006491/254200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (8897/10000 : ℝ)) (alpha := (312566640202933/2224250000000000 : ℝ)) (beta := (26472250006491/254200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8897/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(312566640202933/2224250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26472250006491/254200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (88939/100000 : ℝ) ^ (131/32 : ℝ) ≤ (7735820412547778513/12500000000000000000 : ℝ) := by
    have hpowers : (88939/100000 : ℝ)^131 ≤ (7735820412547778513/12500000000000000000 : ℝ)^32 := by
      have hnat : (88939 : ℕ)^131*12500000000000000000^32 ≤ 7735820412547778513^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88939 100000 7735820412547778513 12500000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88939/100000 : ℝ)) (X := (7735820412547778513/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (20235820412547778513/12500000000000000000 : ℝ) ≤ (1406095900692253/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (20235820412547778513/12500000000000000000 : ℝ)^32 ≤ (1406095900692253/1250000000000000 : ℝ)^131 := by
      have hnat : (20235820412547778513 : ℕ)^32*1250000000000000^131 ≤ 1406095900692253^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20235820412547778513 12500000000000000000 1406095900692253 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1406095900692253/1250000000000000 : ℝ)) (X := (20235820412547778513/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (13985820412547778513/6250000000000000000 : ℝ) ≤ (2434889523122253/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (13985820412547778513/6250000000000000000 : ℝ)^32 ≤ (2434889523122253/2000000000000000 : ℝ)^131 := by
      have hnat : (13985820412547778513 : ℕ)^32*2000000000000000^131 ≤ 2434889523122253^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13985820412547778513 6250000000000000000 2434889523122253 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2434889523122253/2000000000000000 : ℝ)) (X := (13985820412547778513/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(156095900692253/1111737500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(925680410073241/8893900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (88939/100000 : ℝ)) (alpha := (156095900692253/1111737500000000 : ℝ)) (beta := (925680410073241/8893900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (88939/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(156095900692253/1111737500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(925680410073241/8893900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (77511/100000 : ℝ) ^ (131/32 : ℝ) ≤ (17621836895418262067/50000000000000000000 : ℝ) := by
    have hpowers : (77511/100000 : ℝ)^131 ≤ (17621836895418262067/50000000000000000000 : ℝ)^32 := by
      have hnat : (77511 : ℕ)^131*50000000000000000000^32 ≤ 17621836895418262067^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77511 100000 17621836895418262067 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77511/100000 : ℝ)) (X := (17621836895418262067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (67621836895418262067/50000000000000000000 : ℝ) ≤ (5382680158652413/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (67621836895418262067/50000000000000000000 : ℝ)^32 ≤ (5382680158652413/5000000000000000 : ℝ)^131 := by
      have hnat : (67621836895418262067 : ℕ)^32*5000000000000000^131 ≤ 5382680158652413^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67621836895418262067 50000000000000000000 5382680158652413 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5382680158652413/5000000000000000 : ℝ)) (X := (67621836895418262067/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (42621836895418262067/25000000000000000000 : ℝ) ≤ (2847977575425319/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (42621836895418262067/25000000000000000000 : ℝ)^32 ≤ (2847977575425319/2500000000000000 : ℝ)^131 := by
      have hnat : (42621836895418262067 : ℕ)^32*2500000000000000^131 ≤ 2847977575425319^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42621836895418262067 25000000000000000000 2847977575425319 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2847977575425319/2500000000000000 : ℝ)) (X := (42621836895418262067/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(382680158652413/3875550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12530999687929/155022000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (77511/100000 : ℝ)) (alpha := (382680158652413/3875550000000000 : ℝ)) (beta := (12530999687929/155022000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (77511/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(382680158652413/3875550000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12530999687929/155022000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3127556313/10000000000 : ℝ)*X 0 0+(781802233/2500000000 : ℝ)*X 0 1+(6521822259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3127372231/10000000000 : ℝ)*X 1 0+(-156342453/500000000 : ℝ)*X 1 1+(32611261/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1873000489/10000000000 : ℝ)*X 0 0+(91356593/625000000 : ℝ)*X 0 1+(1707165863/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((991102219/5000000000 : ℝ)*X 1 0+(-669872061/5000000000 : ℝ)*X 1 1+(8536392983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4263343713/10000000000 : ℝ)*X 2 0+(7427777301/10000000000 : ℝ)*X 2 1+(-2346623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2096092593/10000000000 : ℝ)*X 0 0+(1633702781/2000000000 : ℝ)*X 0 1+(460570359/2500000000 : ℝ)*X 0 2+(2096092593/10000000000 : ℝ)*X 1 0+(1633702781/2000000000 : ℝ)*X 1 1+(460570359/2500000000 : ℝ)*X 1 2+(2096092593/10000000000 : ℝ)*X 2 0+(1633702781/2000000000 : ℝ)*X 2 1+(460570359/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-886626459/5000000000 : ℝ)*X 0 0+(2132325741/10000000000 : ℝ)*X 0 1+(1023449663/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((842150701/5000000000 : ℝ)*X 1 0+(-1729821/7812500 : ℝ)*X 1 1+(2047034279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((8435217619/10000000000 : ℝ)*X 2 0+(2967687859/10000000000 : ℝ)*X 2 1+(-147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6545327029/10000000000 : ℝ)*X 0 0+(819884299/2000000000 : ℝ)*X 0 1+(402058811/2000000000 : ℝ)*X 0 2+(6545327029/10000000000 : ℝ)*X 1 0+(819884299/2000000000 : ℝ)*X 1 1+(402058811/2000000000 : ℝ)*X 1 2+(6545327029/10000000000 : ℝ)*X 2 0+(819884299/2000000000 : ℝ)*X 2 1+(402058811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-2725085019/5000000000 : ℝ)*X 0 0+(2615626603/10000000000 : ℝ)*X 0 1+(4813156747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2509707027/10000000000 : ℝ)*X 1 0+(-366859443/1250000000 : ℝ)*X 1 1+(1783864519/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1037730371/1250000000 : ℝ)*X 2 0+(63003777/200000000 : ℝ)*X 2 1+(12069849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2114546701/10000000000 : ℝ)*X 0 0+(7698881343/10000000000 : ℝ)*X 0 1+(2533864171/10000000000 : ℝ)*X 0 2+(2114546701/10000000000 : ℝ)*X 1 0+(7698881343/10000000000 : ℝ)*X 1 1+(2533864171/10000000000 : ℝ)*X 1 2+(2114546701/10000000000 : ℝ)*X 2 0+(7698881343/10000000000 : ℝ)*X 2 1+(2533864171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2298146136472826169740811/182324950000000000000000000000 : ℝ) := by norm_num
    linear_combination (208016208031/250000000000 : ℝ)*(base7) + (6559/50000000000 : ℝ)*(base39) + (930263/500000000000 : ℝ)*(base50) + (5081067/500000000000 : ℝ)*(base53) + (159211/62500000000 : ℝ)*(base60) + (883747972633/500000000000 : ℝ)*(major_s2_0) + (883747972633/500000000000 : ℝ)*(major_s2_1) + (441871445783/250000000000 : ℝ)*(major_s2_2) + (1852904284459/1000000000000 : ℝ)*(sp_s2_7) + (926480561789/500000000000 : ℝ)*(sp_s2_8) + (1853003352617/1000000000000 : ℝ)*(sp_s2_9) + (1003552674427/500000000000 : ℝ)*(sp_s2_13) + (11113253/125000000000 : ℝ)*(sp_s2_14) + (6413381/200000000000 : ℝ)*(sp_s2_15) + (117504051673/100000000000 : ℝ)*(f.failure) + (1853003352617/1000000000000 : ℝ)*(f.sum) + (205312520952765523567/344687541450000000000000000000000 : ℝ)*base62 + (58973158108517/387555000000000000000000000 : ℝ)*base65 + (1925433514001089/2223475000000000000000000000 : ℝ)*base67 + (1734419936017/7569433593750000000000000 : ℝ)*base69 + (306059988079817227/879611437500000000000000000000 : ℝ)*base70 + (100932758201223/127100000000000000000000000 : ℝ)*base73 + (612552658291807/4446950000000000000000000000 : ℝ)*base75 + (985357424676703/2224250000000000000000000000 : ℝ)*base77 + (242316250123002953/364649900000000000000000000000 : ℝ)*base79 + (367/500000000000000 : ℝ)*base86 + (367/500000000000000 : ℝ)*base88 + (367/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1214263073630479574304205761/123966571925000000000000000000000 : ℝ) := by norm_num
    linear_combination (51197381943/1000000000000 : ℝ)*(base5) + (821986266837/1000000000000 : ℝ)*(base7) + (47821/20000000000 : ℝ)*(base33) + (40539683653/500000000000 : ℝ)*(base60) + (25972586193/12500000000 : ℝ)*(major_s2_0) + (2077809286491/1000000000000 : ℝ)*(major_s2_1) + (2077809286491/1000000000000 : ℝ)*(major_s2_2) + (371189/62500000000 : ℝ)*(sp_s2_0) + (17378653/500000000000 : ℝ)*(sp_s2_8) + (2273467572639/1000000000000 : ℝ)*(sp_s2_14) + (2273432129827/1000000000000 : ℝ)*(sp_s2_15) + (581167125639/250000000000 : ℝ)*(sp_s2_16) + (1076063664123/500000000000 : ℝ)*(sp_s2_20) + (105837/25000000000 : ℝ)*(sp_s2_22) + (172667305419/125000000000 : ℝ)*(f.failure) + (2273473511663/1000000000000 : ℝ)*(f.sum) + (42743262931168991/4595833886000000000000000000000 : ℝ)*base62 + (21263420887599/64592500000000000000000000 : ℝ)*base65 + (3423146445688551/8893900000000000000000000000 : ℝ)*base67 + (438362952104821/1291850000000000000000000000 : ℝ)*base68 + (29824104018117109/1641941350000000000000000000000 : ℝ)*base71 + (7825886907/794375000000000000000000 : ℝ)*base73 + (484112355263609/2223475000000000000000000000 : ℝ)*base74 + (104248849526357/222425000000000000000000000 : ℝ)*base77 + (39982664531170431/364649900000000000000000000000 : ℝ)*base79 + (49/625000000000000 : ℝ)*base87 + (9/9765625000000 : ℝ)*base88 + (9/9765625000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1024064223288813374536934483/114895847150000000000000000000000 : ℝ) := by norm_num
    linear_combination (1751163/250000000000 : ℝ)*(base5) + (28972501317/62500000000 : ℝ)*(base7) + (7780702453/200000000000 : ℝ)*(base33) + (559722176271/1000000000000 : ℝ)*(base44) + (33945113717/1000000000000 : ℝ)*(base50) + (1834907156183/1000000000000 : ℝ)*(major_s2_0) + (1314088492177/1000000000000 : ℝ)*(major_s2_1) + (58556583389/31250000000 : ℝ)*(major_s2_2) + (33579749/100000000000 : ℝ)*(sp_s2_1) + (133148697/500000000000 : ℝ)*(sp_s2_16) + (2219470688639/1000000000000 : ℝ)*(sp_s2_21) + (405127300653/250000000000 : ℝ)*(sp_s2_22) + (2180307883631/1000000000000 : ℝ)*(sp_s2_23) + (1149549938971/1000000000000 : ℝ)*(sp_s2_27) + (622859549411/500000000000 : ℝ)*(f.failure) + (2219470688639/1000000000000 : ℝ)*(f.sum) + (103730977862101081577/344687541450000000000000000000000 : ℝ)*base62 + (4714982894911/77511000000000000000000000 : ℝ)*base64 + (358278531953797/8893900000000000000000000000 : ℝ)*base67 + (1095373677981301/3875550000000000000000000000 : ℝ)*base69 + (3072650433362762089/12314560125000000000000000000000 : ℝ)*base70 + (35488408873407/254200000000000000000000000 : ℝ)*base72 + (1364826963635449/4446950000000000000000000000 : ℝ)*base75 + (134227581085457/1112125000000000000000000000 : ℝ)*base77 + (191952229546394971/729299800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (131/2500000000000000 : ℝ)*base87 + (131/2500000000000000 : ℝ)*base89 + (131/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8897/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8897/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88939/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(88939/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77511/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77511/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303059_s2 p hpa hpb X hX hprev1

#print axioms solution

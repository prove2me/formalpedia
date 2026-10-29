-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:47.045991+00:00
-- url     : https://prove2.me/submissions/95b45762-5b26-413e-acf2-686f0f3fa9f9

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
theorem collision_support_c320046_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-238471431/2500000000 : ℝ)*x 0 + (-5474144927/10000000000 : ℝ)*x 1 + (-5474144927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238471431/2500000000 : ℝ)^41 ≤ (2698183791051/50000000000000 : ℝ)^33 := by
    have hnat : (238471431 : ℕ)^41*50000000000000^33 ≤ 2698183791051^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238471431 2500000000 2698183791051 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474144927/10000000000 : ℝ)^41 ≤ (9460363239657/20000000000000 : ℝ)^33 := by
    have hnat : (5474144927 : ℕ)^41*20000000000000^33 ≤ 9460363239657^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474144927 10000000000 9460363239657 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474144927/10000000000 : ℝ)^41 ≤ (9460363239657/20000000000000 : ℝ)^33 := by
    have hnat : (5474144927 : ℕ)^41*20000000000000^33 ≤ 9460363239657^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474144927 10000000000 9460363239657 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-238471431/2500000000 : ℝ), (-5474144927/10000000000 : ℝ), (-5474144927/10000000000 : ℝ)] ![(2698183791051/50000000000000 : ℝ), (9460363239657/20000000000000 : ℝ), (9460363239657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-238471431/2500000000 : ℝ)|^41 ≤ (2698183791051/50000000000000 : ℝ)^33
        have hw : |(-238471431/2500000000 : ℝ)|=(238471431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5474144927/10000000000 : ℝ)|^41 ≤ (9460363239657/20000000000000 : ℝ)^33
        have hw : |(-5474144927/10000000000 : ℝ)|=(5474144927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5474144927/10000000000 : ℝ)|^41 ≤ (9460363239657/20000000000000 : ℝ)^33
        have hw : |(-5474144927/10000000000 : ℝ)|=(5474144927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2419578627/5000000000 : ℝ)*x 0 + (3764695861/10000000000 : ℝ)*x 1 + (-3764695861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2419578627/5000000000 : ℝ)^41 ≤ (40583572739251/100000000000000 : ℝ)^33 := by
    have hnat : (2419578627 : ℕ)^41*100000000000000^33 ≤ 40583572739251^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419578627 5000000000 40583572739251 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3764695861/10000000000 : ℝ)^41 ≤ (29708213622641/100000000000000 : ℝ)^33 := by
    have hnat : (3764695861 : ℕ)^41*100000000000000^33 ≤ 29708213622641^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764695861 10000000000 29708213622641 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3764695861/10000000000 : ℝ)^41 ≤ (29708213622641/100000000000000 : ℝ)^33 := by
    have hnat : (3764695861 : ℕ)^41*100000000000000^33 ≤ 29708213622641^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764695861 10000000000 29708213622641 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2419578627/5000000000 : ℝ), (3764695861/10000000000 : ℝ), (-3764695861/10000000000 : ℝ)] ![(40583572739251/100000000000000 : ℝ), (29708213622641/100000000000000 : ℝ), (29708213622641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2419578627/5000000000 : ℝ)|^41 ≤ (40583572739251/100000000000000 : ℝ)^33
        have hw : |(2419578627/5000000000 : ℝ)|=(2419578627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3764695861/10000000000 : ℝ)|^41 ≤ (29708213622641/100000000000000 : ℝ)^33
        have hw : |(3764695861/10000000000 : ℝ)|=(3764695861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3764695861/10000000000 : ℝ)|^41 ≤ (29708213622641/100000000000000 : ℝ)^33
        have hw : |(-3764695861/10000000000 : ℝ)|=(3764695861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (256691019/312500000 : ℝ)*x 0 + (-334516661/2000000000 : ℝ)*x 1 + (-334516661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256691019/312500000 : ℝ)^41 ≤ (7831556459563/10000000000000 : ℝ)^33 := by
    have hnat : (256691019 : ℕ)^41*10000000000000^33 ≤ 7831556459563^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256691019 312500000 7831556459563 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334516661/2000000000 : ℝ)^41 ≤ (5421108847483/50000000000000 : ℝ)^33 := by
    have hnat : (334516661 : ℕ)^41*50000000000000^33 ≤ 5421108847483^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334516661 2000000000 5421108847483 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334516661/2000000000 : ℝ)^41 ≤ (5421108847483/50000000000000 : ℝ)^33 := by
    have hnat : (334516661 : ℕ)^41*50000000000000^33 ≤ 5421108847483^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334516661 2000000000 5421108847483 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256691019/312500000 : ℝ), (-334516661/2000000000 : ℝ), (-334516661/2000000000 : ℝ)] ![(7831556459563/10000000000000 : ℝ), (5421108847483/50000000000000 : ℝ), (5421108847483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256691019/312500000 : ℝ)|^41 ≤ (7831556459563/10000000000000 : ℝ)^33
        have hw : |(256691019/312500000 : ℝ)|=(256691019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334516661/2000000000 : ℝ)|^41 ≤ (5421108847483/50000000000000 : ℝ)^33
        have hw : |(-334516661/2000000000 : ℝ)|=(334516661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334516661/2000000000 : ℝ)|^41 ≤ (5421108847483/50000000000000 : ℝ)^33
        have hw : |(-334516661/2000000000 : ℝ)|=(334516661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1203187/12500000 : ℝ)*x 0 + (-1396335703/2500000000 : ℝ)*x 1 + (-1071337801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1203187/12500000 : ℝ)^41 ≤ (5457330268497/100000000000000 : ℝ)^33 := by
    have hnat : (1203187 : ℕ)^41*100000000000000^33 ≤ 5457330268497^33*12500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203187 12500000 5457330268497 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396335703/2500000000 : ℝ)^41 ≤ (2424926535617/5000000000000 : ℝ)^33 := by
    have hnat : (1396335703 : ℕ)^41*5000000000000^33 ≤ 2424926535617^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396335703 2500000000 2424926535617 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071337801/2000000000 : ℝ)^41 ≤ (23022069500031/50000000000000 : ℝ)^33 := by
    have hnat : (1071337801 : ℕ)^41*50000000000000^33 ≤ 23022069500031^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071337801 2000000000 23022069500031 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1203187/12500000 : ℝ), (-1396335703/2500000000 : ℝ), (-1071337801/2000000000 : ℝ)] ![(5457330268497/100000000000000 : ℝ), (2424926535617/5000000000000 : ℝ), (23022069500031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1203187/12500000 : ℝ)|^41 ≤ (5457330268497/100000000000000 : ℝ)^33
        have hw : |(-1203187/12500000 : ℝ)|=(1203187/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1396335703/2500000000 : ℝ)|^41 ≤ (2424926535617/5000000000000 : ℝ)^33
        have hw : |(-1396335703/2500000000 : ℝ)|=(1396335703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071337801/2000000000 : ℝ)|^41 ≤ (23022069500031/50000000000000 : ℝ)^33
        have hw : |(-1071337801/2000000000 : ℝ)|=(1071337801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4811031841/10000000000 : ℝ)*x 0 + (776320589/2000000000 : ℝ)*x 1 + (-3676972279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4811031841/10000000000 : ℝ)^41 ≤ (5036340542671/12500000000000 : ℝ)^33 := by
    have hnat : (4811031841 : ℕ)^41*12500000000000^33 ≤ 5036340542671^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811031841 10000000000 5036340542671 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776320589/2000000000 : ℝ)^41 ≤ (15429343310123/50000000000000 : ℝ)^33 := by
    have hnat : (776320589 : ℕ)^41*50000000000000^33 ≤ 15429343310123^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776320589 2000000000 15429343310123 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3676972279/10000000000 : ℝ)^41 ≤ (28850589027899/100000000000000 : ℝ)^33 := by
    have hnat : (3676972279 : ℕ)^41*100000000000000^33 ≤ 28850589027899^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3676972279 10000000000 28850589027899 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4811031841/10000000000 : ℝ), (776320589/2000000000 : ℝ), (-3676972279/10000000000 : ℝ)] ![(5036340542671/12500000000000 : ℝ), (15429343310123/50000000000000 : ℝ), (28850589027899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4811031841/10000000000 : ℝ)|^41 ≤ (5036340542671/12500000000000 : ℝ)^33
        have hw : |(4811031841/10000000000 : ℝ)|=(4811031841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776320589/2000000000 : ℝ)|^41 ≤ (15429343310123/50000000000000 : ℝ)^33
        have hw : |(776320589/2000000000 : ℝ)|=(776320589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3676972279/10000000000 : ℝ)|^41 ≤ (28850589027899/100000000000000 : ℝ)^33
        have hw : |(-3676972279/10000000000 : ℝ)|=(3676972279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1202757963/2500000000 : ℝ)*x 0 + (-3594978409/10000000000 : ℝ)*x 1 + (396210601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1202757963/2500000000 : ℝ)^41 ≤ (20145362227911/50000000000000 : ℝ)^33 := by
    have hnat : (1202757963 : ℕ)^41*50000000000000^33 ≤ 20145362227911^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202757963 2500000000 20145362227911 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3594978409/10000000000 : ℝ)^41 ≤ (14026725549931/50000000000000 : ℝ)^33 := by
    have hnat : (3594978409 : ℕ)^41*50000000000000^33 ≤ 14026725549931^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594978409 10000000000 14026725549931 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396210601/1000000000 : ℝ)^41 ≤ (31655824433427/100000000000000 : ℝ)^33 := by
    have hnat : (396210601 : ℕ)^41*100000000000000^33 ≤ 31655824433427^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396210601 1000000000 31655824433427 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1202757963/2500000000 : ℝ), (-3594978409/10000000000 : ℝ), (396210601/1000000000 : ℝ)] ![(20145362227911/50000000000000 : ℝ), (14026725549931/50000000000000 : ℝ), (31655824433427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1202757963/2500000000 : ℝ)|^41 ≤ (20145362227911/50000000000000 : ℝ)^33
        have hw : |(1202757963/2500000000 : ℝ)|=(1202757963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3594978409/10000000000 : ℝ)|^41 ≤ (14026725549931/50000000000000 : ℝ)^33
        have hw : |(-3594978409/10000000000 : ℝ)|=(3594978409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396210601/1000000000 : ℝ)|^41 ≤ (31655824433427/100000000000000 : ℝ)^33
        have hw : |(396210601/1000000000 : ℝ)|=(396210601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8233977653/10000000000 : ℝ)*x 0 + (-391559017/2500000000 : ℝ)*x 1 + (-1748458557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8233977653/10000000000 : ℝ)^41 ≤ (613679273941/781250000000 : ℝ)^33 := by
    have hnat : (8233977653 : ℕ)^41*781250000000^33 ≤ 613679273941^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8233977653 10000000000 613679273941 781250000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391559017/2500000000 : ℝ)^41 ≤ (9992429494463/100000000000000 : ℝ)^33 := by
    have hnat : (391559017 : ℕ)^41*100000000000000^33 ≤ 9992429494463^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391559017 2500000000 9992429494463 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748458557/10000000000 : ℝ)^41 ≤ (11456623421677/100000000000000 : ℝ)^33 := by
    have hnat : (1748458557 : ℕ)^41*100000000000000^33 ≤ 11456623421677^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748458557 10000000000 11456623421677 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8233977653/10000000000 : ℝ), (-391559017/2500000000 : ℝ), (-1748458557/10000000000 : ℝ)] ![(613679273941/781250000000 : ℝ), (9992429494463/100000000000000 : ℝ), (11456623421677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8233977653/10000000000 : ℝ)|^41 ≤ (613679273941/781250000000 : ℝ)^33
        have hw : |(8233977653/10000000000 : ℝ)|=(8233977653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391559017/2500000000 : ℝ)|^41 ≤ (9992429494463/100000000000000 : ℝ)^33
        have hw : |(-391559017/2500000000 : ℝ)|=(391559017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748458557/10000000000 : ℝ)|^41 ≤ (11456623421677/100000000000000 : ℝ)^33
        have hw : |(-1748458557/10000000000 : ℝ)|=(1748458557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-486558917/10000000000 : ℝ)*x 0 + (-1381713303/2500000000 : ℝ)*x 1 + (-5705073961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486558917/10000000000 : ℝ)^41 ≤ (1169055806129/50000000000000 : ℝ)^33 := by
    have hnat : (486558917 : ℕ)^41*50000000000000^33 ≤ 1169055806129^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486558917 10000000000 1169055806129 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381713303/2500000000 : ℝ)^41 ≤ (9573667350649/20000000000000 : ℝ)^33 := by
    have hnat : (1381713303 : ℕ)^41*20000000000000^33 ≤ 9573667350649^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381713303 2500000000 9573667350649 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705073961/10000000000 : ℝ)^41 ≤ (1556048488019/3125000000000 : ℝ)^33 := by
    have hnat : (5705073961 : ℕ)^41*3125000000000^33 ≤ 1556048488019^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705073961 10000000000 1556048488019 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486558917/10000000000 : ℝ), (-1381713303/2500000000 : ℝ), (-5705073961/10000000000 : ℝ)] ![(1169055806129/50000000000000 : ℝ), (9573667350649/20000000000000 : ℝ), (1556048488019/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486558917/10000000000 : ℝ)|^41 ≤ (1169055806129/50000000000000 : ℝ)^33
        have hw : |(-486558917/10000000000 : ℝ)|=(486558917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1381713303/2500000000 : ℝ)|^41 ≤ (9573667350649/20000000000000 : ℝ)^33
        have hw : |(-1381713303/2500000000 : ℝ)|=(1381713303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5705073961/10000000000 : ℝ)|^41 ≤ (1556048488019/3125000000000 : ℝ)^33
        have hw : |(-5705073961/10000000000 : ℝ)|=(5705073961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4631541193/10000000000 : ℝ)*x 0 + (955880643/2500000000 : ℝ)*x 1 + (-1962215281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4631541193/10000000000 : ℝ)^41 ≤ (38431673497889/100000000000000 : ℝ)^33 := by
    have hnat : (4631541193 : ℕ)^41*100000000000000^33 ≤ 38431673497889^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631541193 10000000000 38431673497889 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955880643/2500000000 : ℝ)^41 ≤ (30286056420339/100000000000000 : ℝ)^33 := by
    have hnat : (955880643 : ℕ)^41*100000000000000^33 ≤ 30286056420339^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955880643 2500000000 30286056420339 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962215281/5000000000 : ℝ)^41 ≤ (31282270069157/100000000000000 : ℝ)^33 := by
    have hnat : (1962215281 : ℕ)^41*100000000000000^33 ≤ 31282270069157^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962215281 5000000000 31282270069157 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4631541193/10000000000 : ℝ), (955880643/2500000000 : ℝ), (-1962215281/5000000000 : ℝ)] ![(38431673497889/100000000000000 : ℝ), (30286056420339/100000000000000 : ℝ), (31282270069157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4631541193/10000000000 : ℝ)|^41 ≤ (38431673497889/100000000000000 : ℝ)^33
        have hw : |(4631541193/10000000000 : ℝ)|=(4631541193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955880643/2500000000 : ℝ)|^41 ≤ (30286056420339/100000000000000 : ℝ)^33
        have hw : |(955880643/2500000000 : ℝ)|=(955880643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1962215281/5000000000 : ℝ)|^41 ≤ (31282270069157/100000000000000 : ℝ)^33
        have hw : |(-1962215281/5000000000 : ℝ)|=(1962215281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1063059473/2000000000 : ℝ)*x 0 + (-3460815937/10000000000 : ℝ)*x 1 + (3552151603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063059473/2000000000 : ℝ)^41 ≤ (45602514947639/100000000000000 : ℝ)^33 := by
    have hnat : (1063059473 : ℕ)^41*100000000000000^33 ≤ 45602514947639^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063059473 2000000000 45602514947639 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3460815937/10000000000 : ℝ)^41 ≤ (13379325012613/50000000000000 : ℝ)^33 := by
    have hnat : (3460815937 : ℕ)^41*50000000000000^33 ≤ 13379325012613^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3460815937 10000000000 13379325012613 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3552151603/10000000000 : ℝ)^41 ≤ (2763883502047/10000000000000 : ℝ)^33 := by
    have hnat : (3552151603 : ℕ)^41*10000000000000^33 ≤ 2763883502047^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552151603 10000000000 2763883502047 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063059473/2000000000 : ℝ), (-3460815937/10000000000 : ℝ), (3552151603/10000000000 : ℝ)] ![(45602514947639/100000000000000 : ℝ), (13379325012613/50000000000000 : ℝ), (2763883502047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063059473/2000000000 : ℝ)|^41 ≤ (45602514947639/100000000000000 : ℝ)^33
        have hw : |(1063059473/2000000000 : ℝ)|=(1063059473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3460815937/10000000000 : ℝ)|^41 ≤ (13379325012613/50000000000000 : ℝ)^33
        have hw : |(-3460815937/10000000000 : ℝ)|=(3460815937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3552151603/10000000000 : ℝ)|^41 ≤ (2763883502047/10000000000000 : ℝ)^33
        have hw : |(3552151603/10000000000 : ℝ)|=(3552151603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_19 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1100781137/1250000000 : ℝ)*x 0 + (-299456349/2500000000 : ℝ)*x 1 + (-154556359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100781137/1250000000 : ℝ)^41 ≤ (42694994498733/50000000000000 : ℝ)^33 := by
    have hnat : (1100781137 : ℕ)^41*50000000000000^33 ≤ 42694994498733^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100781137 1250000000 42694994498733 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299456349/2500000000 : ℝ)^41 ≤ (111890648029/1562500000000 : ℝ)^33 := by
    have hnat : (299456349 : ℕ)^41*1562500000000^33 ≤ 111890648029^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299456349 2500000000 111890648029 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154556359/1250000000 : ℝ)^41 ≤ (7449009522701/100000000000000 : ℝ)^33 := by
    have hnat : (154556359 : ℕ)^41*100000000000000^33 ≤ 7449009522701^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154556359 1250000000 7449009522701 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100781137/1250000000 : ℝ), (-299456349/2500000000 : ℝ), (-154556359/1250000000 : ℝ)] ![(42694994498733/50000000000000 : ℝ), (111890648029/1562500000000 : ℝ), (7449009522701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100781137/1250000000 : ℝ)|^41 ≤ (42694994498733/50000000000000 : ℝ)^33
        have hw : |(1100781137/1250000000 : ℝ)|=(1100781137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299456349/2500000000 : ℝ)|^41 ≤ (111890648029/1562500000000 : ℝ)^33
        have hw : |(-299456349/2500000000 : ℝ)|=(299456349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154556359/1250000000 : ℝ)|^41 ≤ (7449009522701/100000000000000 : ℝ)^33
        have hw : |(-154556359/1250000000 : ℝ)|=(154556359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-12163979/250000000 : ℝ)*x 0 + (-2852535743/5000000000 : ℝ)*x 1 + (-1381713893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12163979/250000000 : ℝ)^41 ≤ (2338113063053/100000000000000 : ℝ)^33 := by
    have hnat : (12163979 : ℕ)^41*100000000000000^33 ≤ 2338113063053^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12163979 250000000 2338113063053 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852535743/5000000000 : ℝ)^41 ≤ (49793524778189/100000000000000 : ℝ)^33 := by
    have hnat : (2852535743 : ℕ)^41*100000000000000^33 ≤ 49793524778189^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852535743 5000000000 49793524778189 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381713893/2500000000 : ℝ)^41 ≤ (47868362148487/100000000000000 : ℝ)^33 := by
    have hnat : (1381713893 : ℕ)^41*100000000000000^33 ≤ 47868362148487^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381713893 2500000000 47868362148487 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12163979/250000000 : ℝ), (-2852535743/5000000000 : ℝ), (-1381713893/2500000000 : ℝ)] ![(2338113063053/100000000000000 : ℝ), (49793524778189/100000000000000 : ℝ), (47868362148487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12163979/250000000 : ℝ)|^41 ≤ (2338113063053/100000000000000 : ℝ)^33
        have hw : |(-12163979/250000000 : ℝ)|=(12163979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2852535743/5000000000 : ℝ)|^41 ≤ (49793524778189/100000000000000 : ℝ)^33
        have hw : |(-2852535743/5000000000 : ℝ)|=(2852535743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1381713893/2500000000 : ℝ)|^41 ≤ (47868362148487/100000000000000 : ℝ)^33
        have hw : |(-1381713893/2500000000 : ℝ)|=(1381713893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5315298213/10000000000 : ℝ)*x 0 + (3552150303/10000000000 : ℝ)*x 1 + (-3460816303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5315298213/10000000000 : ℝ)^41 ≤ (45602523986777/100000000000000 : ℝ)^33 := by
    have hnat : (5315298213 : ℕ)^41*100000000000000^33 ≤ 45602523986777^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5315298213 10000000000 45602523986777 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3552150303/10000000000 : ℝ)^41 ≤ (431856600831/1562500000000 : ℝ)^33 := by
    have hnat : (3552150303 : ℕ)^41*1562500000000^33 ≤ 431856600831^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552150303 10000000000 431856600831 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3460816303/10000000000 : ℝ)^41 ≤ (26758653541127/100000000000000 : ℝ)^33 := by
    have hnat : (3460816303 : ℕ)^41*100000000000000^33 ≤ 26758653541127^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3460816303 10000000000 26758653541127 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5315298213/10000000000 : ℝ), (3552150303/10000000000 : ℝ), (-3460816303/10000000000 : ℝ)] ![(45602523986777/100000000000000 : ℝ), (431856600831/1562500000000 : ℝ), (26758653541127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5315298213/10000000000 : ℝ)|^41 ≤ (45602523986777/100000000000000 : ℝ)^33
        have hw : |(5315298213/10000000000 : ℝ)|=(5315298213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3552150303/10000000000 : ℝ)|^41 ≤ (431856600831/1562500000000 : ℝ)^33
        have hw : |(3552150303/10000000000 : ℝ)|=(3552150303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3460816303/10000000000 : ℝ)|^41 ≤ (26758653541127/100000000000000 : ℝ)^33
        have hw : |(-3460816303/10000000000 : ℝ)|=(3460816303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2315771253/5000000000 : ℝ)*x 0 + (-3924428957/10000000000 : ℝ)*x 1 + (3823522811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2315771253/5000000000 : ℝ)^41 ≤ (38431687034141/100000000000000 : ℝ)^33 := by
    have hnat : (2315771253 : ℕ)^41*100000000000000^33 ≤ 38431687034141^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315771253 5000000000 38431687034141 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3924428957/10000000000 : ℝ)^41 ≤ (31282254173937/100000000000000 : ℝ)^33 := by
    have hnat : (3924428957 : ℕ)^41*100000000000000^33 ≤ 31282254173937^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3924428957 10000000000 31282254173937 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3823522811/10000000000 : ℝ)^41 ≤ (30286058772391/100000000000000 : ℝ)^33 := by
    have hnat : (3823522811 : ℕ)^41*100000000000000^33 ≤ 30286058772391^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3823522811 10000000000 30286058772391 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2315771253/5000000000 : ℝ), (-3924428957/10000000000 : ℝ), (3823522811/10000000000 : ℝ)] ![(38431687034141/100000000000000 : ℝ), (31282254173937/100000000000000 : ℝ), (30286058772391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2315771253/5000000000 : ℝ)|^41 ≤ (38431687034141/100000000000000 : ℝ)^33
        have hw : |(2315771253/5000000000 : ℝ)|=(2315771253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3924428957/10000000000 : ℝ)|^41 ≤ (31282254173937/100000000000000 : ℝ)^33
        have hw : |(-3924428957/10000000000 : ℝ)|=(3924428957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3823522811/10000000000 : ℝ)|^41 ≤ (30286058772391/100000000000000 : ℝ)^33
        have hw : |(3823522811/10000000000 : ℝ)|=(3823522811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s0_25 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8806249819/10000000000 : ℝ)*x 0 + (-309112439/2500000000 : ℝ)*x 1 + (-598912673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8806249819/10000000000 : ℝ)^41 ≤ (85389997707587/100000000000000 : ℝ)^33 := by
    have hnat : (8806249819 : ℕ)^41*100000000000000^33 ≤ 85389997707587^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8806249819 10000000000 85389997707587 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309112439/2500000000 : ℝ)^41 ≤ (7449001169447/100000000000000 : ℝ)^33 := by
    have hnat : (309112439 : ℕ)^41*100000000000000^33 ≤ 7449001169447^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309112439 2500000000 7449001169447 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598912673/5000000000 : ℝ)^41 ≤ (286440044099/4000000000000 : ℝ)^33 := by
    have hnat : (598912673 : ℕ)^41*4000000000000^33 ≤ 286440044099^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598912673 5000000000 286440044099 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8806249819/10000000000 : ℝ), (-309112439/2500000000 : ℝ), (-598912673/5000000000 : ℝ)] ![(85389997707587/100000000000000 : ℝ), (7449001169447/100000000000000 : ℝ), (286440044099/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8806249819/10000000000 : ℝ)|^41 ≤ (85389997707587/100000000000000 : ℝ)^33
        have hw : |(8806249819/10000000000 : ℝ)|=(8806249819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309112439/2500000000 : ℝ)|^41 ≤ (7449001169447/100000000000000 : ℝ)^33
        have hw : |(-309112439/2500000000 : ℝ)|=(309112439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-598912673/5000000000 : ℝ)|^41 ≤ (286440044099/4000000000000 : ℝ)^33
        have hw : |(-598912673/5000000000 : ℝ)|=(598912673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-7471829/31250000 : ℝ)*x 0 + (-154113013/312500000 : ℝ)*x 1 + (-154113013/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7471829/31250000 : ℝ)^41 ≤ (3380328246173/20000000000000 : ℝ)^33 := by
    have hnat : (7471829 : ℕ)^41*20000000000000^33 ≤ 3380328246173^33*31250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7471829 31250000 3380328246173 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154113013/312500000 : ℝ)^41 ≤ (41549179382259/100000000000000 : ℝ)^33 := by
    have hnat : (154113013 : ℕ)^41*100000000000000^33 ≤ 41549179382259^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154113013 312500000 41549179382259 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154113013/312500000 : ℝ)^41 ≤ (41549179382259/100000000000000 : ℝ)^33 := by
    have hnat : (154113013 : ℕ)^41*100000000000000^33 ≤ 41549179382259^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154113013 312500000 41549179382259 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7471829/31250000 : ℝ), (-154113013/312500000 : ℝ), (-154113013/312500000 : ℝ)] ![(3380328246173/20000000000000 : ℝ), (41549179382259/100000000000000 : ℝ), (41549179382259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7471829/31250000 : ℝ)|^41 ≤ (3380328246173/20000000000000 : ℝ)^33
        have hw : |(-7471829/31250000 : ℝ)|=(7471829/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154113013/312500000 : ℝ)|^41 ≤ (41549179382259/100000000000000 : ℝ)^33
        have hw : |(-154113013/312500000 : ℝ)|=(154113013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154113013/312500000 : ℝ)|^41 ≤ (41549179382259/100000000000000 : ℝ)^33
        have hw : |(-154113013/312500000 : ℝ)|=(154113013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2257634971/5000000000 : ℝ)*x 0 + (9836161/25000000 : ℝ)*x 1 + (-9836161/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257634971/5000000000 : ℝ)^41 ≤ (1861832838513/5000000000000 : ℝ)^33 := by
    have hnat : (2257634971 : ℕ)^41*5000000000000^33 ≤ 1861832838513^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257634971 5000000000 1861832838513 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9836161/25000000 : ℝ)^41 ≤ (31381671605877/100000000000000 : ℝ)^33 := by
    have hnat : (9836161 : ℕ)^41*100000000000000^33 ≤ 31381671605877^33*25000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9836161 25000000 31381671605877 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9836161/25000000 : ℝ)^41 ≤ (31381671605877/100000000000000 : ℝ)^33 := by
    have hnat : (9836161 : ℕ)^41*100000000000000^33 ≤ 31381671605877^33*25000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9836161 25000000 31381671605877 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257634971/5000000000 : ℝ), (9836161/25000000 : ℝ), (-9836161/25000000 : ℝ)] ![(1861832838513/5000000000000 : ℝ), (31381671605877/100000000000000 : ℝ), (31381671605877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257634971/5000000000 : ℝ)|^41 ≤ (1861832838513/5000000000000 : ℝ)^33
        have hw : |(2257634971/5000000000 : ℝ)|=(2257634971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9836161/25000000 : ℝ)|^41 ≤ (31381671605877/100000000000000 : ℝ)^33
        have hw : |(9836161/25000000 : ℝ)|=(9836161/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9836161/25000000 : ℝ)|^41 ≤ (31381671605877/100000000000000 : ℝ)^33
        have hw : |(-9836161/25000000 : ℝ)|=(9836161/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2257634971/5000000000 : ℝ)*x 0 + (-9836161/25000000 : ℝ)*x 1 + (9836161/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257634971/5000000000 : ℝ)^41 ≤ (1861832838513/5000000000000 : ℝ)^33 := by
    have hnat : (2257634971 : ℕ)^41*5000000000000^33 ≤ 1861832838513^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257634971 5000000000 1861832838513 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9836161/25000000 : ℝ)^41 ≤ (31381671605877/100000000000000 : ℝ)^33 := by
    have hnat : (9836161 : ℕ)^41*100000000000000^33 ≤ 31381671605877^33*25000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9836161 25000000 31381671605877 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9836161/25000000 : ℝ)^41 ≤ (31381671605877/100000000000000 : ℝ)^33 := by
    have hnat : (9836161 : ℕ)^41*100000000000000^33 ≤ 31381671605877^33*25000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9836161 25000000 31381671605877 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257634971/5000000000 : ℝ), (-9836161/25000000 : ℝ), (9836161/25000000 : ℝ)] ![(1861832838513/5000000000000 : ℝ), (31381671605877/100000000000000 : ℝ), (31381671605877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257634971/5000000000 : ℝ)|^41 ≤ (1861832838513/5000000000000 : ℝ)^33
        have hw : |(2257634971/5000000000 : ℝ)|=(2257634971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9836161/25000000 : ℝ)|^41 ≤ (31381671605877/100000000000000 : ℝ)^33
        have hw : |(-9836161/25000000 : ℝ)|=(9836161/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9836161/25000000 : ℝ)|^41 ≤ (31381671605877/100000000000000 : ℝ)^33
        have hw : |(9836161/25000000 : ℝ)|=(9836161/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320046_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3268873883/5000000000 : ℝ)*x 0 + (-2794093317/10000000000 : ℝ)*x 1 + (-2794093317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3268873883/5000000000 : ℝ)^41 ≤ (29488554002899/50000000000000 : ℝ)^33 := by
    have hnat : (3268873883 : ℕ)^41*50000000000000^33 ≤ 29488554002899^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3268873883 5000000000 29488554002899 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794093317/10000000000 : ℝ)^41 ≤ (2051144599309/10000000000000 : ℝ)^33 := by
    have hnat : (2794093317 : ℕ)^41*10000000000000^33 ≤ 2051144599309^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794093317 10000000000 2051144599309 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2794093317/10000000000 : ℝ)^41 ≤ (2051144599309/10000000000000 : ℝ)^33 := by
    have hnat : (2794093317 : ℕ)^41*10000000000000^33 ≤ 2051144599309^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794093317 10000000000 2051144599309 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3268873883/5000000000 : ℝ), (-2794093317/10000000000 : ℝ), (-2794093317/10000000000 : ℝ)] ![(29488554002899/50000000000000 : ℝ), (2051144599309/10000000000000 : ℝ), (2051144599309/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3268873883/5000000000 : ℝ)|^41 ≤ (29488554002899/50000000000000 : ℝ)^33
        have hw : |(3268873883/5000000000 : ℝ)|=(3268873883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2794093317/10000000000 : ℝ)|^41 ≤ (2051144599309/10000000000000 : ℝ)^33
        have hw : |(-2794093317/10000000000 : ℝ)|=(2794093317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2794093317/10000000000 : ℝ)|^41 ≤ (2051144599309/10000000000000 : ℝ)^33
        have hw : |(-2794093317/10000000000 : ℝ)|=(2794093317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320046 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-238471431/2500000000 : ℝ)*X 0 0+(-5474144927/10000000000 : ℝ)*X 0 1+(-5474144927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2419578627/5000000000 : ℝ)*X 1 0+(3764695861/10000000000 : ℝ)*X 1 1+(-3764695861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((256691019/312500000 : ℝ)*X 0 0+(-334516661/2000000000 : ℝ)*X 0 1+(-334516661/2000000000 : ℝ)*X 0 2+(256691019/312500000 : ℝ)*X 1 0+(-334516661/2000000000 : ℝ)*X 1 1+(-334516661/2000000000 : ℝ)*X 1 2+(256691019/312500000 : ℝ)*X 2 0+(-334516661/2000000000 : ℝ)*X 2 1+(-334516661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1203187/12500000 : ℝ)*X 0 0+(-1396335703/2500000000 : ℝ)*X 0 1+(-1071337801/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4811031841/10000000000 : ℝ)*X 1 0+(776320589/2000000000 : ℝ)*X 1 1+(-3676972279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1202757963/2500000000 : ℝ)*X 2 0+(-3594978409/10000000000 : ℝ)*X 2 1+(396210601/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((8233977653/10000000000 : ℝ)*X 0 0+(-391559017/2500000000 : ℝ)*X 0 1+(-1748458557/10000000000 : ℝ)*X 0 2+(8233977653/10000000000 : ℝ)*X 1 0+(-391559017/2500000000 : ℝ)*X 1 1+(-1748458557/10000000000 : ℝ)*X 1 2+(8233977653/10000000000 : ℝ)*X 2 0+(-391559017/2500000000 : ℝ)*X 2 1+(-1748458557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-486558917/10000000000 : ℝ)*X 0 0+(-1381713303/2500000000 : ℝ)*X 0 1+(-5705073961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4631541193/10000000000 : ℝ)*X 1 0+(955880643/2500000000 : ℝ)*X 1 1+(-1962215281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1063059473/2000000000 : ℝ)*X 2 0+(-3460815937/10000000000 : ℝ)*X 2 1+(3552151603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1100781137/1250000000 : ℝ)*X 0 0+(-299456349/2500000000 : ℝ)*X 0 1+(-154556359/1250000000 : ℝ)*X 0 2+(1100781137/1250000000 : ℝ)*X 1 0+(-299456349/2500000000 : ℝ)*X 1 1+(-154556359/1250000000 : ℝ)*X 1 2+(1100781137/1250000000 : ℝ)*X 2 0+(-299456349/2500000000 : ℝ)*X 2 1+(-154556359/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-12163979/250000000 : ℝ)*X 0 0+(-2852535743/5000000000 : ℝ)*X 0 1+(-1381713893/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5315298213/10000000000 : ℝ)*X 1 0+(3552150303/10000000000 : ℝ)*X 1 1+(-3460816303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2315771253/5000000000 : ℝ)*X 2 0+(-3924428957/10000000000 : ℝ)*X 2 1+(3823522811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8806249819/10000000000 : ℝ)*X 0 0+(-309112439/2500000000 : ℝ)*X 0 1+(-598912673/5000000000 : ℝ)*X 0 2+(8806249819/10000000000 : ℝ)*X 1 0+(-309112439/2500000000 : ℝ)*X 1 1+(-598912673/5000000000 : ℝ)*X 1 2+(8806249819/10000000000 : ℝ)*X 2 0+(-309112439/2500000000 : ℝ)*X 2 1+(-598912673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17682369320073265796721/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (562253387921/500000000000 : ℝ)*(base39) + (24799031619/250000000000 : ℝ)*(base49) + (52751/200000000000 : ℝ)*(base59) + (4160157501127/1000000000000 : ℝ)*(major_s0_0) + (4160157501127/1000000000000 : ℝ)*(major_s0_1) + (4160157501127/1000000000000 : ℝ)*(major_s0_2) + (224814889/500000000000 : ℝ)*(sp_s0_1) + (142505583/500000000000 : ℝ)*(sp_s0_6) + (244166348959/40000000000 : ℝ)*(sp_s0_7) + (1525814557547/250000000000 : ℝ)*(sp_s0_8) + (6103777938167/1000000000000 : ℝ)*(sp_s0_9) + (443173074597/200000000000 : ℝ)*(sp_s0_13) + (450864009/1000000000000 : ℝ)*(sp_s0_15) + (23799113/62500000000 : ℝ)*(sp_s0_22) + (2216150384151/1000000000000 : ℝ)*(f.failure) + (244166348959/40000000000 : ℝ)*(f.sum) + (2596361467414423/5000000000000000000000000000 : ℝ)*base62 + (3423342582795521/10000000000000000000000000000 : ℝ)*base65 + (1482520577204479/10000000000000000000000000000 : ℝ)*base66 + (7173482490914423/10000000000000000000000000000 : ℝ)*base68 + (707206157940549/5000000000000000000000000000 : ℝ)*base71 + (7126434915795521/10000000000000000000000000000 : ℝ)*base73 + (7207384165914423/10000000000000000000000000000 : ℝ)*base74 + (3212836268085577/10000000000000000000000000000 : ℝ)*base77 + (63976431295521/5000000000000000000000000000 : ℝ)*base79 + (3143/2500000000000000 : ℝ)*base87 + (3143/2500000000000000 : ℝ)*base89 + (3143/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7029/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-7029/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30246448413424580428767/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1022172467393/200000000000 : ℝ)*(base39) + (2506638800519/1000000000000 : ℝ)*(base40) + (2723/781250000 : ℝ)*(base49) + (498123/500000000000 : ℝ)*(base59) + (9967467838827/1000000000000 : ℝ)*(major_s0_0) + (9967467838827/1000000000000 : ℝ)*(major_s0_1) + (9967467838827/1000000000000 : ℝ)*(major_s0_2) + (76639079/500000000000 : ℝ)*(sp_s0_0) + (102667339/1000000000000 : ℝ)*(sp_s0_9) + (2925005529113/200000000000 : ℝ)*(sp_s0_14) + (14625172219441/1000000000000 : ℝ)*(sp_s0_15) + (14625078256383/1000000000000 : ℝ)*(sp_s0_16) + (663719092187/125000000000 : ℝ)*(sp_s0_19) + (8704281/1000000000000 : ℝ)*(sp_s0_21) + (663719092187/125000000000 : ℝ)*(f.failure) + (7312590461861/500000000000 : ℝ)*(f.sum) + (621075162881723/5000000000000000000000000000 : ℝ)*base62 + (3801388679522621/10000000000000000000000000000 : ℝ)*base65 + (10188264960522621/10000000000000000000000000000 : ℝ)*base67 + (2872144685381723/10000000000000000000000000000 : ℝ)*base68 + (3534724032429551/5000000000000000000000000000 : ℝ)*base70 + (6355676514522621/10000000000000000000000000000 : ℝ)*base73 + (2843874342381723/10000000000000000000000000000 : ℝ)*base74 + (3022050165381723/10000000000000000000000000000 : ℝ)*base76 + (4375359604022621/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (307/625000000000000 : ℝ)*base87 + (307/625000000000000 : ℝ)*base89 + (307/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7029/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7029/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (518828258412866481777/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1022184439319/200000000000 : ℝ)*(base39) + (2089273666817/1000000000000 : ℝ)*(base40) + (497347/100000000000 : ℝ)*(base49) + (7106261/1000000000000 : ℝ)*(base59) + (398703669109/40000000000 : ℝ)*(major_s0_0) + (398703669109/40000000000 : ℝ)*(major_s0_1) + (398703669109/40000000000 : ℝ)*(major_s0_2) + (1944207/62500000000 : ℝ)*(sp_s0_6) + (186611643/500000000000 : ℝ)*(sp_s0_7) + (43482139/125000000000 : ℝ)*(sp_s0_8) + (14624989768593/1000000000000 : ℝ)*(sp_s0_20) + (14625015134767/1000000000000 : ℝ)*(sp_s0_21) + (14625362991879/1000000000000 : ℝ)*(sp_s0_22) + (5309787626827/1000000000000 : ℝ)*(sp_s0_25) + (5309818734139/1000000000000 : ℝ)*(f.failure) + (14625362991879/1000000000000 : ℝ)*(f.sum) + (46088865992741/200000000000000000000000000 : ℝ)*base62 + (70963041812707/400000000000000000000000000 : ℝ)*base65 + (185043606852707/400000000000000000000000000 : ℝ)*base67 + (268930478292741/400000000000000000000000000 : ℝ)*base68 + (51163320220017/200000000000000000000000000 : ℝ)*base70 + (85598967772707/400000000000000000000000000 : ℝ)*base73 + (268199846732741/400000000000000000000000000 : ℝ)*base74 + (260242687587259/400000000000000000000000000 : ℝ)*base77 + (81489921607293/200000000000000000000000000 : ℝ)*base78 + (1827/2500000000000000 : ℝ)*base87 + (1827/2500000000000000 : ℝ)*base89 + (1827/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1727/100000 : ℝ) ^ (5 : ℝ) ≤ (153624926403/100000000000000000000 : ℝ) := by
    have hpowers : (1727/100000 : ℝ)^5 ≤ (153624926403/100000000000000000000 : ℝ)^1 := by
      have hnat : (1727 : ℕ)^5*100000000000000000000^1 ≤ 153624926403^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1727 100000 153624926403 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1727/100000 : ℝ)) (X := (153624926403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (100000000153624926403/100000000000000000000 : ℝ) ≤ (10000000003072499/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100000000153624926403/100000000000000000000 : ℝ)^1 ≤ (10000000003072499/10000000000000000 : ℝ)^5 := by
      have hnat : (100000000153624926403 : ℕ)^1*10000000000000000^5 ≤ 10000000003072499^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000000153624926403 100000000000000000000 10000000003072499 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000003072499/10000000000000000 : ℝ)) (X := (100000000153624926403/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (50000000153624926403/50000000000000000000 : ℝ) ≤ (5000000003072499/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50000000153624926403/50000000000000000000 : ℝ)^1 ≤ (5000000003072499/5000000000000000 : ℝ)^5 := by
      have hnat : (50000000153624926403 : ℕ)^1*5000000000000000^5 ≤ 5000000003072499^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000153624926403 50000000000000000000 5000000003072499 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003072499/5000000000000000 : ℝ)) (X := (50000000153624926403/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3072499/172700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3072499/172700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1727/100000 : ℝ)) (alpha := (3072499/172700000000000 : ℝ)) (beta := (3072499/172700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1727/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3072499/172700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3072499/172700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7029/25000 : ℝ) ^ (5 : ℝ) ≤ (35139669207829189/20000000000000000000 : ℝ) := by
    have hpowers : (7029/25000 : ℝ)^5 ≤ (35139669207829189/20000000000000000000 : ℝ)^1 := by
      have hnat : (7029 : ℕ)^5*20000000000000000000^1 ≤ 35139669207829189^1*25000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 25000 35139669207829189 20000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/25000 : ℝ)) (X := (35139669207829189/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (20035139669207829189/20000000000000000000 : ℝ) ≤ (5001755749964151/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (20035139669207829189/20000000000000000000 : ℝ)^1 ≤ (5001755749964151/5000000000000000 : ℝ)^5 := by
      have hnat : (20035139669207829189 : ℕ)^1*5000000000000000^5 ≤ 5001755749964151^5*20000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20035139669207829189 20000000000000000000 5001755749964151 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001755749964151/5000000000000000 : ℝ)) (X := (20035139669207829189/20000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (10035139669207829189/10000000000000000000 : ℝ) ≤ (10007018076247017/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (10035139669207829189/10000000000000000000 : ℝ)^1 ≤ (10007018076247017/10000000000000000 : ℝ)^5 := by
      have hnat : (10035139669207829189 : ℕ)^1*10000000000000000^5 ≤ 10007018076247017^5*10000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10035139669207829189 10000000000000000000 10007018076247017 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007018076247017/10000000000000000 : ℝ)) (X := (10035139669207829189/10000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1755749964151/1405800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(233771754581/187440000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (7029/25000 : ℝ)) (alpha := (1755749964151/1405800000000000 : ℝ)) (beta := (233771754581/187440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7029/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1755749964151/1405800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(233771754581/187440000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7029/25000 : ℝ) ^ (5 : ℝ) ≤ (35139669207829189/20000000000000000000 : ℝ) := by
    have hpowers : (7029/25000 : ℝ)^5 ≤ (35139669207829189/20000000000000000000 : ℝ)^1 := by
      have hnat : (7029 : ℕ)^5*20000000000000000000^1 ≤ 35139669207829189^1*25000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 25000 35139669207829189 20000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/25000 : ℝ)) (X := (35139669207829189/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (20035139669207829189/20000000000000000000 : ℝ) ≤ (5001755749964151/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (20035139669207829189/20000000000000000000 : ℝ)^1 ≤ (5001755749964151/5000000000000000 : ℝ)^5 := by
      have hnat : (20035139669207829189 : ℕ)^1*5000000000000000^5 ≤ 5001755749964151^5*20000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20035139669207829189 20000000000000000000 5001755749964151 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001755749964151/5000000000000000 : ℝ)) (X := (20035139669207829189/20000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (10035139669207829189/10000000000000000000 : ℝ) ≤ (10007018076247017/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (10035139669207829189/10000000000000000000 : ℝ)^1 ≤ (10007018076247017/10000000000000000 : ℝ)^5 := by
      have hnat : (10035139669207829189 : ℕ)^1*10000000000000000^5 ≤ 10007018076247017^5*10000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10035139669207829189 10000000000000000000 10007018076247017 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007018076247017/10000000000000000 : ℝ)) (X := (10035139669207829189/10000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1755749964151/1405800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(233771754581/187440000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (7029/25000 : ℝ)) (alpha := (1755749964151/1405800000000000 : ℝ)) (beta := (233771754581/187440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7029/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1755749964151/1405800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(233771754581/187440000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-7471829/31250000 : ℝ)*X 0 0+(-154113013/312500000 : ℝ)*X 0 1+(-154113013/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2257634971/5000000000 : ℝ)*X 1 0+(9836161/25000000 : ℝ)*X 1 1+(-9836161/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2257634971/5000000000 : ℝ)*X 2 0+(-9836161/25000000 : ℝ)*X 2 1+(9836161/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3268873883/5000000000 : ℝ)*X 0 0+(-2794093317/10000000000 : ℝ)*X 0 1+(-2794093317/10000000000 : ℝ)*X 0 2+(3268873883/5000000000 : ℝ)*X 1 0+(-2794093317/10000000000 : ℝ)*X 1 1+(-2794093317/10000000000 : ℝ)*X 1 2+(3268873883/5000000000 : ℝ)*X 2 0+(-2794093317/10000000000 : ℝ)*X 2 1+(-2794093317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-1872398944989653282273888777/229906875000000000000000000 : ℝ) := by norm_num
    linear_combination (239/500000000000 : ℝ)*(base8) + (529693390217/500000000000 : ℝ)*(base39) + (529693390217/1000000000000 : ℝ)*(base40) + (128326647063/500000000000 : ℝ)*(base49) + (14409/1000000000000 : ℝ)*(base50) + (128326647063/500000000000 : ℝ)*(base59) + (14409/1000000000000 : ℝ)*(base60) + (4693/2500 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (1357360412891/500000000000 : ℝ)*(sp_s1_0) + (135736041313/50000000000 : ℝ)*(sp_s1_1) + (135736041313/50000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (135736041313/50000000000 : ℝ)*(f.sum) + (47786142031/109828125000000000000000 : ℝ)*base63 + (65414797219/366093750000000000000000 : ℝ)*base65 + (65414797219/366093750000000000000000 : ℝ)*base67 + (332115888233/1757250000000000000000000 : ℝ)*base69 + (72107051807/459813750000000000000000 : ℝ)*base71 + (103376711/2158750000000000000000 : ℝ)*base73 + (332115888233/1757250000000000000000000 : ℝ)*base75 + (103376711/2158750000000000000000 : ℝ)*base77 + (72107051807/459813750000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b025 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 := by omega
  rcases hc with rfl
  · exact collision_c320046 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

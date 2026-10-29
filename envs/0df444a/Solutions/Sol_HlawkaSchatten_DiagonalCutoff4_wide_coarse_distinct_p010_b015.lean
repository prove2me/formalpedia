-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:36.132199+00:00
-- url     : https://prove2.me/submissions/03977b26-39af-4587-92eb-b5241e761994

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
theorem collision_support_c310027_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4367889917/10000000000 : ℝ)*x 0 + (-1507279963/10000000000 : ℝ)*x 1 + (643618309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367889917/10000000000 : ℝ)^9 ≤ (34474038766537/100000000000000 : ℝ)^7 := by
    have hnat : (4367889917 : ℕ)^9*100000000000000^7 ≤ 34474038766537^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367889917 10000000000 34474038766537 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507279963/10000000000 : ℝ)^9 ≤ (1755586312159/20000000000000 : ℝ)^7 := by
    have hnat : (1507279963 : ℕ)^9*20000000000000^7 ≤ 1755586312159^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507279963 10000000000 1755586312159 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643618309/1000000000 : ℝ)^9 ≤ (886687963547/1562500000000 : ℝ)^7 := by
    have hnat : (643618309 : ℕ)^9*1562500000000^7 ≤ 886687963547^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643618309 1000000000 886687963547 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367889917/10000000000 : ℝ), (-1507279963/10000000000 : ℝ), (643618309/1000000000 : ℝ)] ![(34474038766537/100000000000000 : ℝ), (1755586312159/20000000000000 : ℝ), (886687963547/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367889917/10000000000 : ℝ)|^9 ≤ (34474038766537/100000000000000 : ℝ)^7
        have hw : |(4367889917/10000000000 : ℝ)|=(4367889917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1507279963/10000000000 : ℝ)|^9 ≤ (1755586312159/20000000000000 : ℝ)^7
        have hw : |(-1507279963/10000000000 : ℝ)|=(1507279963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643618309/1000000000 : ℝ)|^9 ≤ (886687963547/1562500000000 : ℝ)^7
        have hw : |(643618309/1000000000 : ℝ)|=(643618309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2063424119/5000000000 : ℝ)*x 0 + (3233264369/5000000000 : ℝ)*x 1 + (-71146697/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063424119/5000000000 : ℝ)^9 ≤ (16023788957819/50000000000000 : ℝ)^7 := by
    have hnat : (2063424119 : ℕ)^9*50000000000000^7 ≤ 16023788957819^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063424119 5000000000 16023788957819 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3233264369/5000000000 : ℝ)^9 ≤ (57092264944879/100000000000000 : ℝ)^7 := by
    have hnat : (3233264369 : ℕ)^9*100000000000000^7 ≤ 57092264944879^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233264369 5000000000 57092264944879 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71146697/400000000 : ℝ)^9 ≤ (10860157129947/100000000000000 : ℝ)^7 := by
    have hnat : (71146697 : ℕ)^9*100000000000000^7 ≤ 10860157129947^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71146697 400000000 10860157129947 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063424119/5000000000 : ℝ), (3233264369/5000000000 : ℝ), (-71146697/400000000 : ℝ)] ![(16023788957819/50000000000000 : ℝ), (57092264944879/100000000000000 : ℝ), (10860157129947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063424119/5000000000 : ℝ)|^9 ≤ (16023788957819/50000000000000 : ℝ)^7
        have hw : |(2063424119/5000000000 : ℝ)|=(2063424119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3233264369/5000000000 : ℝ)|^9 ≤ (57092264944879/100000000000000 : ℝ)^7
        have hw : |(3233264369/5000000000 : ℝ)|=(3233264369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71146697/400000000 : ℝ)|^9 ≤ (10860157129947/100000000000000 : ℝ)^7
        have hw : |(-71146697/400000000 : ℝ)|=(71146697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-16275361/1000000000 : ℝ)*x 0 + (402521767/625000000 : ℝ)*x 1 + (5159151241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16275361/1000000000 : ℝ)^9 ≤ (501810081149/100000000000000 : ℝ)^7 := by
    have hnat : (16275361 : ℕ)^9*100000000000000^7 ≤ 501810081149^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16275361 1000000000 501810081149 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402521767/625000000 : ℝ)^9 ≤ (14198812824741/25000000000000 : ℝ)^7 := by
    have hnat : (402521767 : ℕ)^9*25000000000000^7 ≤ 14198812824741^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402521767 625000000 14198812824741 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5159151241/10000000000 : ℝ)^9 ≤ (533786732673/1250000000000 : ℝ)^7 := by
    have hnat : (5159151241 : ℕ)^9*1250000000000^7 ≤ 533786732673^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159151241 10000000000 533786732673 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16275361/1000000000 : ℝ), (402521767/625000000 : ℝ), (5159151241/10000000000 : ℝ)] ![(501810081149/100000000000000 : ℝ), (14198812824741/25000000000000 : ℝ), (533786732673/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16275361/1000000000 : ℝ)|^9 ≤ (501810081149/100000000000000 : ℝ)^7
        have hw : |(-16275361/1000000000 : ℝ)|=(16275361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402521767/625000000 : ℝ)|^9 ≤ (14198812824741/25000000000000 : ℝ)^7
        have hw : |(402521767/625000000 : ℝ)|=(402521767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5159151241/10000000000 : ℝ)|^9 ≤ (533786732673/1250000000000 : ℝ)^7
        have hw : |(5159151241/10000000000 : ℝ)|=(5159151241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055723343/2000000000 : ℝ)*x 0 + (639928487/2500000000 : ℝ)*x 1 + (2388474281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055723343/2000000000 : ℝ)^9 ≤ (43978474972631/100000000000000 : ℝ)^7 := by
    have hnat : (1055723343 : ℕ)^9*100000000000000^7 ≤ 43978474972631^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055723343 2000000000 43978474972631 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639928487/2500000000 : ℝ)^9 ≤ (86710816923/500000000000 : ℝ)^7 := by
    have hnat : (639928487 : ℕ)^9*500000000000^7 ≤ 86710816923^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639928487 2500000000 86710816923 500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388474281/5000000000 : ℝ)^9 ≤ (9669840404059/25000000000000 : ℝ)^7 := by
    have hnat : (2388474281 : ℕ)^9*25000000000000^7 ≤ 9669840404059^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388474281 5000000000 9669840404059 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055723343/2000000000 : ℝ), (639928487/2500000000 : ℝ), (2388474281/5000000000 : ℝ)] ![(43978474972631/100000000000000 : ℝ), (86710816923/500000000000 : ℝ), (9669840404059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055723343/2000000000 : ℝ)|^9 ≤ (43978474972631/100000000000000 : ℝ)^7
        have hw : |(-1055723343/2000000000 : ℝ)|=(1055723343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639928487/2500000000 : ℝ)|^9 ≤ (86710816923/500000000000 : ℝ)^7
        have hw : |(639928487/2500000000 : ℝ)|=(639928487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388474281/5000000000 : ℝ)|^9 ≤ (9669840404059/25000000000000 : ℝ)^7
        have hw : |(2388474281/5000000000 : ℝ)|=(2388474281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (978626793/2500000000 : ℝ)*x 0 + (-150751451/10000000000 : ℝ)*x 1 + (7543877877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978626793/2500000000 : ℝ)^9 ≤ (14971631322237/50000000000000 : ℝ)^7 := by
    have hnat : (978626793 : ℕ)^9*50000000000000^7 ≤ 14971631322237^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978626793 2500000000 14971631322237 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150751451/10000000000 : ℝ)^9 ≤ (28421356639/6250000000000 : ℝ)^7 := by
    have hnat : (150751451 : ℕ)^9*6250000000000^7 ≤ 28421356639^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150751451 10000000000 28421356639 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7543877877/10000000000 : ℝ)^9 ≤ (17400498908703/25000000000000 : ℝ)^7 := by
    have hnat : (7543877877 : ℕ)^9*25000000000000^7 ≤ 17400498908703^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7543877877 10000000000 17400498908703 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(978626793/2500000000 : ℝ), (-150751451/10000000000 : ℝ), (7543877877/10000000000 : ℝ)] ![(14971631322237/50000000000000 : ℝ), (28421356639/6250000000000 : ℝ), (17400498908703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(978626793/2500000000 : ℝ)|^9 ≤ (14971631322237/50000000000000 : ℝ)^7
        have hw : |(978626793/2500000000 : ℝ)|=(978626793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150751451/10000000000 : ℝ)|^9 ≤ (28421356639/6250000000000 : ℝ)^7
        have hw : |(-150751451/10000000000 : ℝ)|=(150751451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7543877877/10000000000 : ℝ)|^9 ≤ (17400498908703/25000000000000 : ℝ)^7
        have hw : |(7543877877/10000000000 : ℝ)|=(7543877877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2417272291/10000000000 : ℝ)*x 0 + (3884443143/5000000000 : ℝ)*x 1 + (-1872994449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2417272291/10000000000 : ℝ)^9 ≤ (16111385179913/100000000000000 : ℝ)^7 := by
    have hnat : (2417272291 : ℕ)^9*100000000000000^7 ≤ 16111385179913^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417272291 10000000000 16111385179913 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3884443143/5000000000 : ℝ)^9 ≤ (72282422201629/100000000000000 : ℝ)^7 := by
    have hnat : (3884443143 : ℕ)^9*100000000000000^7 ≤ 72282422201629^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884443143 5000000000 72282422201629 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872994449/10000000000 : ℝ)^9 ≤ (5803096299477/50000000000000 : ℝ)^7 := by
    have hnat : (1872994449 : ℕ)^9*50000000000000^7 ≤ 5803096299477^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872994449 10000000000 5803096299477 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2417272291/10000000000 : ℝ), (3884443143/5000000000 : ℝ), (-1872994449/10000000000 : ℝ)] ![(16111385179913/100000000000000 : ℝ), (72282422201629/100000000000000 : ℝ), (5803096299477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2417272291/10000000000 : ℝ)|^9 ≤ (16111385179913/100000000000000 : ℝ)^7
        have hw : |(2417272291/10000000000 : ℝ)|=(2417272291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3884443143/5000000000 : ℝ)|^9 ≤ (72282422201629/100000000000000 : ℝ)^7
        have hw : |(3884443143/5000000000 : ℝ)|=(3884443143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1872994449/10000000000 : ℝ)|^9 ≤ (5803096299477/50000000000000 : ℝ)^7
        have hw : |(-1872994449/10000000000 : ℝ)|=(1872994449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-49161007/10000000000 : ℝ)*x 0 + (4020753593/5000000000 : ℝ)*x 1 + (66622299/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49161007/10000000000 : ℝ)^9 ≤ (107667306251/100000000000000 : ℝ)^7 := by
    have hnat : (49161007 : ℕ)^9*100000000000000^7 ≤ 107667306251^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49161007 10000000000 107667306251 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4020753593/5000000000 : ℝ)^9 ≤ (15111967413479/20000000000000 : ℝ)^7 := by
    have hnat : (4020753593 : ℕ)^9*20000000000000^7 ≤ 15111967413479^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020753593 5000000000 15111967413479 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66622299/200000000 : ℝ)^9 ≤ (24332495612133/100000000000000 : ℝ)^7 := by
    have hnat : (66622299 : ℕ)^9*100000000000000^7 ≤ 24332495612133^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66622299 200000000 24332495612133 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49161007/10000000000 : ℝ), (4020753593/5000000000 : ℝ), (66622299/200000000 : ℝ)] ![(107667306251/100000000000000 : ℝ), (15111967413479/20000000000000 : ℝ), (24332495612133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49161007/10000000000 : ℝ)|^9 ≤ (107667306251/100000000000000 : ℝ)^7
        have hw : |(-49161007/10000000000 : ℝ)|=(49161007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4020753593/5000000000 : ℝ)|^9 ≤ (15111967413479/20000000000000 : ℝ)^7
        have hw : |(4020753593/5000000000 : ℝ)|=(4020753593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66622299/200000000 : ℝ)|^9 ≤ (24332495612133/100000000000000 : ℝ)^7
        have hw : |(66622299/200000000 : ℝ)|=(66622299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2973046869/5000000000 : ℝ)*x 0 + (112915231/500000000 : ℝ)*x 1 + (4319523969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2973046869/5000000000 : ℝ)^9 ≤ (2562692759547/5000000000000 : ℝ)^7 := by
    have hnat : (2973046869 : ℕ)^9*5000000000000^7 ≤ 2562692759547^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973046869 5000000000 2562692759547 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112915231/500000000 : ℝ)^9 ≤ (590485108363/4000000000000 : ℝ)^7 := by
    have hnat : (112915231 : ℕ)^9*4000000000000^7 ≤ 590485108363^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112915231 500000000 590485108363 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319523969/10000000000 : ℝ)^9 ≤ (33984017089313/100000000000000 : ℝ)^7 := by
    have hnat : (4319523969 : ℕ)^9*100000000000000^7 ≤ 33984017089313^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319523969 10000000000 33984017089313 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2973046869/5000000000 : ℝ), (112915231/500000000 : ℝ), (4319523969/10000000000 : ℝ)] ![(2562692759547/5000000000000 : ℝ), (590485108363/4000000000000 : ℝ), (33984017089313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2973046869/5000000000 : ℝ)|^9 ≤ (2562692759547/5000000000000 : ℝ)^7
        have hw : |(-2973046869/5000000000 : ℝ)|=(2973046869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112915231/500000000 : ℝ)|^9 ≤ (590485108363/4000000000000 : ℝ)^7
        have hw : |(112915231/500000000 : ℝ)|=(112915231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319523969/10000000000 : ℝ)|^9 ≤ (33984017089313/100000000000000 : ℝ)^7
        have hw : |(4319523969/10000000000 : ℝ)|=(4319523969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1530486559/2500000000 : ℝ)*x 0 + (-178835511/10000000000 : ℝ)*x 1 + (5486955421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530486559/2500000000 : ℝ)^9 ≤ (53210923963171/100000000000000 : ℝ)^7 := by
    have hnat : (1530486559 : ℕ)^9*100000000000000^7 ≤ 53210923963171^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530486559 2500000000 53210923963171 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178835511/10000000000 : ℝ)^9 ≤ (283220600069/50000000000000 : ℝ)^7 := by
    have hnat : (178835511 : ℕ)^9*50000000000000^7 ≤ 283220600069^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178835511 10000000000 283220600069 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486955421/10000000000 : ℝ)^9 ≤ (11555658708507/25000000000000 : ℝ)^7 := by
    have hnat : (5486955421 : ℕ)^9*25000000000000^7 ≤ 11555658708507^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486955421 10000000000 11555658708507 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1530486559/2500000000 : ℝ), (-178835511/10000000000 : ℝ), (5486955421/10000000000 : ℝ)] ![(53210923963171/100000000000000 : ℝ), (283220600069/50000000000000 : ℝ), (11555658708507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1530486559/2500000000 : ℝ)|^9 ≤ (53210923963171/100000000000000 : ℝ)^7
        have hw : |(1530486559/2500000000 : ℝ)|=(1530486559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178835511/10000000000 : ℝ)|^9 ≤ (283220600069/50000000000000 : ℝ)^7
        have hw : |(-178835511/10000000000 : ℝ)|=(178835511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486955421/10000000000 : ℝ)|^9 ≤ (11555658708507/25000000000000 : ℝ)^7
        have hw : |(5486955421/10000000000 : ℝ)|=(5486955421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (689665999/2000000000 : ℝ)*x 0 + (1605073277/2500000000 : ℝ)*x 1 + (-105365907/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689665999/2000000000 : ℝ)^9 ≤ (317985317167/1250000000000 : ℝ)^7 := by
    have hnat : (689665999 : ℕ)^9*1250000000000^7 ≤ 317985317167^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689665999 2000000000 317985317167 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1605073277/2500000000 : ℝ)^9 ≤ (1131359229683/2000000000000 : ℝ)^7 := by
    have hnat : (1605073277 : ℕ)^9*2000000000000^7 ≤ 1131359229683^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605073277 2500000000 1131359229683 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105365907/400000000 : ℝ)^9 ≤ (17993213119109/100000000000000 : ℝ)^7 := by
    have hnat : (105365907 : ℕ)^9*100000000000000^7 ≤ 17993213119109^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105365907 400000000 17993213119109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689665999/2000000000 : ℝ), (1605073277/2500000000 : ℝ), (-105365907/400000000 : ℝ)] ![(317985317167/1250000000000 : ℝ), (1131359229683/2000000000000 : ℝ), (17993213119109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689665999/2000000000 : ℝ)|^9 ≤ (317985317167/1250000000000 : ℝ)^7
        have hw : |(689665999/2000000000 : ℝ)|=(689665999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1605073277/2500000000 : ℝ)|^9 ≤ (1131359229683/2000000000000 : ℝ)^7
        have hw : |(1605073277/2500000000 : ℝ)|=(1605073277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105365907/400000000 : ℝ)|^9 ≤ (17993213119109/100000000000000 : ℝ)^7
        have hw : |(-105365907/400000000 : ℝ)|=(105365907/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-323811/16000000 : ℝ)*x 0 + (524935169/1250000000 : ℝ)*x 1 + (7286282223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323811/16000000 : ℝ)^9 ≤ (664080378057/100000000000000 : ℝ)^7 := by
    have hnat : (323811 : ℕ)^9*100000000000000^7 ≤ 664080378057^7*16000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323811 16000000 664080378057 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524935169/1250000000 : ℝ)^9 ≤ (32774590445351/100000000000000 : ℝ)^7 := by
    have hnat : (524935169 : ℕ)^9*100000000000000^7 ≤ 32774590445351^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524935169 1250000000 32774590445351 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7286282223/10000000000 : ℝ)^9 ≤ (33280664582781/50000000000000 : ℝ)^7 := by
    have hnat : (7286282223 : ℕ)^9*50000000000000^7 ≤ 33280664582781^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7286282223 10000000000 33280664582781 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323811/16000000 : ℝ), (524935169/1250000000 : ℝ), (7286282223/10000000000 : ℝ)] ![(664080378057/100000000000000 : ℝ), (32774590445351/100000000000000 : ℝ), (33280664582781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323811/16000000 : ℝ)|^9 ≤ (664080378057/100000000000000 : ℝ)^7
        have hw : |(-323811/16000000 : ℝ)|=(323811/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524935169/1250000000 : ℝ)|^9 ≤ (32774590445351/100000000000000 : ℝ)^7
        have hw : |(524935169/1250000000 : ℝ)|=(524935169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7286282223/10000000000 : ℝ)|^9 ≤ (33280664582781/50000000000000 : ℝ)^7
        have hw : |(7286282223/10000000000 : ℝ)|=(7286282223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-6298860169/10000000000 : ℝ)*x 0 + (1683732461/5000000000 : ℝ)*x 1 + (1437165831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6298860169/10000000000 : ℝ)^9 ≤ (2759804052967/5000000000000 : ℝ)^7 := by
    have hnat : (6298860169 : ℕ)^9*5000000000000^7 ≤ 2759804052967^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6298860169 10000000000 2759804052967 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683732461/5000000000 : ℝ)^9 ≤ (96384423139/390625000000 : ℝ)^7 := by
    have hnat : (1683732461 : ℕ)^9*390625000000^7 ≤ 96384423139^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683732461 5000000000 96384423139 390625000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437165831/5000000000 : ℝ)^9 ≤ (15726177033/78125000000 : ℝ)^7 := by
    have hnat : (1437165831 : ℕ)^9*78125000000^7 ≤ 15726177033^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437165831 5000000000 15726177033 78125000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6298860169/10000000000 : ℝ), (1683732461/5000000000 : ℝ), (1437165831/5000000000 : ℝ)] ![(2759804052967/5000000000000 : ℝ), (96384423139/390625000000 : ℝ), (15726177033/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6298860169/10000000000 : ℝ)|^9 ≤ (2759804052967/5000000000000 : ℝ)^7
        have hw : |(-6298860169/10000000000 : ℝ)|=(6298860169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1683732461/5000000000 : ℝ)|^9 ≤ (96384423139/390625000000 : ℝ)^7
        have hw : |(1683732461/5000000000 : ℝ)|=(1683732461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1437165831/5000000000 : ℝ)|^9 ≤ (15726177033/78125000000 : ℝ)^7
        have hw : |(1437165831/5000000000 : ℝ)|=(1437165831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (499759487/1250000000 : ℝ)*x 0 + (-162221019/1000000000 : ℝ)*x 1 + (3342524747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499759487/1250000000 : ℝ)^9 ≤ (30767640093659/100000000000000 : ℝ)^7 := by
    have hnat : (499759487 : ℕ)^9*100000000000000^7 ≤ 30767640093659^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499759487 1250000000 30767640093659 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162221019/1000000000 : ℝ)^9 ≤ (4823846181027/50000000000000 : ℝ)^7 := by
    have hnat : (162221019 : ℕ)^9*50000000000000^7 ≤ 4823846181027^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162221019 1000000000 4823846181027 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3342524747/5000000000 : ℝ)^9 ≤ (11916933505993/20000000000000 : ℝ)^7 := by
    have hnat : (3342524747 : ℕ)^9*20000000000000^7 ≤ 11916933505993^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342524747 5000000000 11916933505993 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(499759487/1250000000 : ℝ), (-162221019/1000000000 : ℝ), (3342524747/5000000000 : ℝ)] ![(30767640093659/100000000000000 : ℝ), (4823846181027/50000000000000 : ℝ), (11916933505993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(499759487/1250000000 : ℝ)|^9 ≤ (30767640093659/100000000000000 : ℝ)^7
        have hw : |(499759487/1250000000 : ℝ)|=(499759487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162221019/1000000000 : ℝ)|^9 ≤ (4823846181027/50000000000000 : ℝ)^7
        have hw : |(-162221019/1000000000 : ℝ)|=(162221019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3342524747/5000000000 : ℝ)|^9 ≤ (11916933505993/20000000000000 : ℝ)^7
        have hw : |(3342524747/5000000000 : ℝ)|=(3342524747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1275811299/2000000000 : ℝ)*x 0 + (2477945677/5000000000 : ℝ)*x 1 + (-355992413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1275811299/2000000000 : ℝ)^9 ≤ (56101254986181/100000000000000 : ℝ)^7 := by
    have hnat : (1275811299 : ℕ)^9*100000000000000^7 ≤ 56101254986181^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275811299 2000000000 56101254986181 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2477945677/5000000000 : ℝ)^9 ≤ (40552133992649/100000000000000 : ℝ)^7 := by
    have hnat : (2477945677 : ℕ)^9*100000000000000^7 ≤ 40552133992649^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477945677 5000000000 40552133992649 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355992413/5000000000 : ℝ)^9 ≤ (3346611002237/100000000000000 : ℝ)^7 := by
    have hnat : (355992413 : ℕ)^9*100000000000000^7 ≤ 3346611002237^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355992413 5000000000 3346611002237 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1275811299/2000000000 : ℝ), (2477945677/5000000000 : ℝ), (-355992413/5000000000 : ℝ)] ![(56101254986181/100000000000000 : ℝ), (40552133992649/100000000000000 : ℝ), (3346611002237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1275811299/2000000000 : ℝ)|^9 ≤ (56101254986181/100000000000000 : ℝ)^7
        have hw : |(1275811299/2000000000 : ℝ)|=(1275811299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2477945677/5000000000 : ℝ)|^9 ≤ (40552133992649/100000000000000 : ℝ)^7
        have hw : |(2477945677/5000000000 : ℝ)|=(2477945677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355992413/5000000000 : ℝ)|^9 ≤ (3346611002237/100000000000000 : ℝ)^7
        have hw : |(-355992413/5000000000 : ℝ)|=(355992413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-193335131/10000000000 : ℝ)*x 0 + (8344872857/10000000000 : ℝ)*x 1 + (1437165831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193335131/10000000000 : ℝ)^9 ≤ (313079973991/50000000000000 : ℝ)^7 := by
    have hnat : (193335131 : ℕ)^9*50000000000000^7 ≤ 313079973991^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193335131 10000000000 313079973991 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8344872857/10000000000 : ℝ)^9 ≤ (792443334447/1000000000000 : ℝ)^7 := by
    have hnat : (8344872857 : ℕ)^9*1000000000000^7 ≤ 792443334447^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8344872857 10000000000 792443334447 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437165831/5000000000 : ℝ)^9 ≤ (15726177033/78125000000 : ℝ)^7 := by
    have hnat : (1437165831 : ℕ)^9*78125000000^7 ≤ 15726177033^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437165831 5000000000 15726177033 78125000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193335131/10000000000 : ℝ), (8344872857/10000000000 : ℝ), (1437165831/5000000000 : ℝ)] ![(313079973991/50000000000000 : ℝ), (792443334447/1000000000000 : ℝ), (15726177033/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193335131/10000000000 : ℝ)|^9 ≤ (313079973991/50000000000000 : ℝ)^7
        have hw : |(-193335131/10000000000 : ℝ)|=(193335131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8344872857/10000000000 : ℝ)|^9 ≤ (792443334447/1000000000000 : ℝ)^7
        have hw : |(8344872857/10000000000 : ℝ)|=(8344872857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1437165831/5000000000 : ℝ)|^9 ≤ (15726177033/78125000000 : ℝ)^7
        have hw : |(1437165831/5000000000 : ℝ)|=(1437165831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-316915579/625000000 : ℝ)*x 0 + (1919003289/5000000000 : ℝ)*x 1 + (955679669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316915579/625000000 : ℝ)^9 ≤ (2088170830513/5000000000000 : ℝ)^7 := by
    have hnat : (316915579 : ℕ)^9*5000000000000^7 ≤ 2088170830513^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316915579 625000000 2088170830513 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919003289/5000000000 : ℝ)^9 ≤ (29193003281679/100000000000000 : ℝ)^7 := by
    have hnat : (1919003289 : ℕ)^9*100000000000000^7 ≤ 29193003281679^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919003289 5000000000 29193003281679 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955679669/2500000000 : ℝ)^9 ≤ (29043580098523/100000000000000 : ℝ)^7 := by
    have hnat : (955679669 : ℕ)^9*100000000000000^7 ≤ 29043580098523^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955679669 2500000000 29043580098523 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316915579/625000000 : ℝ), (1919003289/5000000000 : ℝ), (955679669/2500000000 : ℝ)] ![(2088170830513/5000000000000 : ℝ), (29193003281679/100000000000000 : ℝ), (29043580098523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316915579/625000000 : ℝ)|^9 ≤ (2088170830513/5000000000000 : ℝ)^7
        have hw : |(-316915579/625000000 : ℝ)|=(316915579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1919003289/5000000000 : ℝ)|^9 ≤ (29193003281679/100000000000000 : ℝ)^7
        have hw : |(1919003289/5000000000 : ℝ)|=(1919003289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955679669/2500000000 : ℝ)|^9 ≤ (29043580098523/100000000000000 : ℝ)^7
        have hw : |(955679669/2500000000 : ℝ)|=(955679669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (431613161/1000000000 : ℝ)*x 0 + (-1569213841/5000000000 : ℝ)*x 1 + (1047008817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431613161/1000000000 : ℝ)^9 ≤ (33949705853279/100000000000000 : ℝ)^7 := by
    have hnat : (431613161 : ℕ)^9*100000000000000^7 ≤ 33949705853279^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431613161 1000000000 33949705853279 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569213841/5000000000 : ℝ)^9 ≤ (22538011194597/100000000000000 : ℝ)^7 := by
    have hnat : (1569213841 : ℕ)^9*100000000000000^7 ≤ 22538011194597^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569213841 5000000000 22538011194597 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047008817/2000000000 : ℝ)^9 ≤ (43512282950381/100000000000000 : ℝ)^7 := by
    have hnat : (1047008817 : ℕ)^9*100000000000000^7 ≤ 43512282950381^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047008817 2000000000 43512282950381 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431613161/1000000000 : ℝ), (-1569213841/5000000000 : ℝ), (1047008817/2000000000 : ℝ)] ![(33949705853279/100000000000000 : ℝ), (22538011194597/100000000000000 : ℝ), (43512282950381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431613161/1000000000 : ℝ)|^9 ≤ (33949705853279/100000000000000 : ℝ)^7
        have hw : |(431613161/1000000000 : ℝ)|=(431613161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1569213841/5000000000 : ℝ)|^9 ≤ (22538011194597/100000000000000 : ℝ)^7
        have hw : |(-1569213841/5000000000 : ℝ)|=(1569213841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047008817/2000000000 : ℝ)|^9 ≤ (43512282950381/100000000000000 : ℝ)^7
        have hw : |(1047008817/2000000000 : ℝ)|=(1047008817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4373399781/10000000000 : ℝ)*x 0 + (1286435067/2500000000 : ℝ)*x 1 + (-635723549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373399781/10000000000 : ℝ)^9 ≤ (3452996094257/10000000000000 : ℝ)^7 := by
    have hnat : (4373399781 : ℕ)^9*10000000000000^7 ≤ 3452996094257^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373399781 10000000000 3452996094257 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286435067/2500000000 : ℝ)^9 ≤ (10640067958821/25000000000000 : ℝ)^7 := by
    have hnat : (1286435067 : ℕ)^9*25000000000000^7 ≤ 10640067958821^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286435067 2500000000 10640067958821 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635723549/2000000000 : ℝ)^9 ≤ (178982556219/781250000000 : ℝ)^7 := by
    have hnat : (635723549 : ℕ)^9*781250000000^7 ≤ 178982556219^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635723549 2000000000 178982556219 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373399781/10000000000 : ℝ), (1286435067/2500000000 : ℝ), (-635723549/2000000000 : ℝ)] ![(3452996094257/10000000000000 : ℝ), (10640067958821/25000000000000 : ℝ), (178982556219/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373399781/10000000000 : ℝ)|^9 ≤ (3452996094257/10000000000000 : ℝ)^7
        have hw : |(4373399781/10000000000 : ℝ)|=(4373399781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286435067/2500000000 : ℝ)|^9 ≤ (10640067958821/25000000000000 : ℝ)^7
        have hw : |(1286435067/2500000000 : ℝ)|=(1286435067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-635723549/2000000000 : ℝ)|^9 ≤ (178982556219/781250000000 : ℝ)^7
        have hw : |(-635723549/2000000000 : ℝ)|=(635723549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310027_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1811692497/10000000000 : ℝ)*x 0 + (5447979307/10000000000 : ℝ)*x 1 + (5194453009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811692497/10000000000 : ℝ)^9 ≤ (2780024563159/25000000000000 : ℝ)^7 := by
    have hnat : (1811692497 : ℕ)^9*25000000000000^7 ≤ 2780024563159^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811692497 10000000000 2780024563159 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447979307/10000000000 : ℝ)^9 ≤ (9160182890671/20000000000000 : ℝ)^7 := by
    have hnat : (5447979307 : ℕ)^9*20000000000000^7 ≤ 9160182890671^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447979307 10000000000 9160182890671 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194453009/10000000000 : ℝ)^9 ≤ (4307898728511/10000000000000 : ℝ)^7 := by
    have hnat : (5194453009 : ℕ)^9*10000000000000^7 ≤ 4307898728511^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194453009 10000000000 4307898728511 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1811692497/10000000000 : ℝ), (5447979307/10000000000 : ℝ), (5194453009/10000000000 : ℝ)] ![(2780024563159/25000000000000 : ℝ), (9160182890671/20000000000000 : ℝ), (4307898728511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1811692497/10000000000 : ℝ)|^9 ≤ (2780024563159/25000000000000 : ℝ)^7
        have hw : |(1811692497/10000000000 : ℝ)|=(1811692497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447979307/10000000000 : ℝ)|^9 ≤ (9160182890671/20000000000000 : ℝ)^7
        have hw : |(5447979307/10000000000 : ℝ)|=(5447979307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194453009/10000000000 : ℝ)|^9 ≤ (4307898728511/10000000000000 : ℝ)^7
        have hw : |(5194453009/10000000000 : ℝ)|=(5194453009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310027 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4367889917/10000000000 : ℝ)*X 1 0+(-1507279963/10000000000 : ℝ)*X 1 1+(643618309/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2063424119/5000000000 : ℝ)*X 2 0+(3233264369/5000000000 : ℝ)*X 2 1+(-71146697/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-16275361/1000000000 : ℝ)*X 0 0+(402521767/625000000 : ℝ)*X 0 1+(5159151241/10000000000 : ℝ)*X 0 2+(-16275361/1000000000 : ℝ)*X 1 0+(402521767/625000000 : ℝ)*X 1 1+(5159151241/10000000000 : ℝ)*X 1 2+(-16275361/1000000000 : ℝ)*X 2 0+(402521767/625000000 : ℝ)*X 2 1+(5159151241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1055723343/2000000000 : ℝ)*X 0 0+(639928487/2500000000 : ℝ)*X 0 1+(2388474281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((978626793/2500000000 : ℝ)*X 1 0+(-150751451/10000000000 : ℝ)*X 1 1+(7543877877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2417272291/10000000000 : ℝ)*X 2 0+(3884443143/5000000000 : ℝ)*X 2 1+(-1872994449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-49161007/10000000000 : ℝ)*X 0 0+(4020753593/5000000000 : ℝ)*X 0 1+(66622299/200000000 : ℝ)*X 0 2+(-49161007/10000000000 : ℝ)*X 1 0+(4020753593/5000000000 : ℝ)*X 1 1+(66622299/200000000 : ℝ)*X 1 2+(-49161007/10000000000 : ℝ)*X 2 0+(4020753593/5000000000 : ℝ)*X 2 1+(66622299/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2973046869/5000000000 : ℝ)*X 0 0+(112915231/500000000 : ℝ)*X 0 1+(4319523969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1530486559/2500000000 : ℝ)*X 1 0+(-178835511/10000000000 : ℝ)*X 1 1+(5486955421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((689665999/2000000000 : ℝ)*X 2 0+(1605073277/2500000000 : ℝ)*X 2 1+(-105365907/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-323811/16000000 : ℝ)*X 0 0+(524935169/1250000000 : ℝ)*X 0 1+(7286282223/10000000000 : ℝ)*X 0 2+(-323811/16000000 : ℝ)*X 1 0+(524935169/1250000000 : ℝ)*X 1 1+(7286282223/10000000000 : ℝ)*X 1 2+(-323811/16000000 : ℝ)*X 2 0+(524935169/1250000000 : ℝ)*X 2 1+(7286282223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-6298860169/10000000000 : ℝ)*X 0 0+(1683732461/5000000000 : ℝ)*X 0 1+(1437165831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((499759487/1250000000 : ℝ)*X 1 0+(-162221019/1000000000 : ℝ)*X 1 1+(3342524747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1275811299/2000000000 : ℝ)*X 2 0+(2477945677/5000000000 : ℝ)*X 2 1+(-355992413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-193335131/10000000000 : ℝ)*X 0 0+(8344872857/10000000000 : ℝ)*X 0 1+(1437165831/5000000000 : ℝ)*X 0 2+(-193335131/10000000000 : ℝ)*X 1 0+(8344872857/10000000000 : ℝ)*X 1 1+(1437165831/5000000000 : ℝ)*X 1 2+(-193335131/10000000000 : ℝ)*X 2 0+(8344872857/10000000000 : ℝ)*X 2 1+(1437165831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((30833/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30833/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (346435330396543860651/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (19733085457/31250000000 : ℝ)*(base7) + (94390189923/500000000000 : ℝ)*(base39) + (230669469399/500000000000 : ℝ)*(base50) + (778411/200000000000 : ℝ)*(base53) + (109548557371/1000000000000 : ℝ)*(base60) + (61753173431/31250000000 : ℝ)*(major_s0_0) + (61753173431/31250000000 : ℝ)*(major_s0_1) + (1976097657737/1000000000000 : ℝ)*(major_s0_2) + (1307329/1000000000000 : ℝ)*(sp_s0_6) + (146850650703/62500000000 : ℝ)*(sp_s0_7) + (469919115587/200000000000 : ℝ)*(sp_s0_8) + (2349614303303/1000000000000 : ℝ)*(sp_s0_9) + (926416923209/500000000000 : ℝ)*(sp_s0_13) + (14833313/1000000000000 : ℝ)*(sp_s0_22) + (1221376419123/1000000000000 : ℝ)*(f.failure) + (2349614303303/1000000000000 : ℝ)*(f.sum) + (2718653063450813/10000000000000000000000000000 : ℝ)*base62 + (831414364055783/10000000000000000000000000000 : ℝ)*base65 + (85819276682079/312500000000000000000000000 : ℝ)*base67 + (204784834063011/10000000000000000000000000000 : ℝ)*base69 + (1416183891430393/10000000000000000000000000000 : ℝ)*base70 + (52112644150829/312500000000000000000000000 : ℝ)*base73 + (82779123671443/312500000000000000000000000 : ℝ)*base75 + (102849174734807/312500000000000000000000000 : ℝ)*base77 + (43355373369579/156250000000000000000000000 : ℝ)*base79 + (32461/100000000000000000 : ℝ)*base86 + (32461/100000000000000000 : ℝ)*base88 + (32461/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18221/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(18221/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (87553123974622787732541/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1154649071661/1000000000000 : ℝ)*(base1) + (519450745321/500000000000 : ℝ)*(base7) + (223864105999/1000000000000 : ℝ)*(base40) + (1049937/500000000000 : ℝ)*(base50) + (3010579/250000000000 : ℝ)*(base54) + (92614822201/250000000000 : ℝ)*(base60) + (2157755717167/1000000000000 : ℝ)*(major_s0_0) + (2157755717167/1000000000000 : ℝ)*(major_s0_1) + (43154873497/20000000000 : ℝ)*(major_s0_2) + (107844809/1000000000000 : ℝ)*(sp_s0_2) + (1754658877329/500000000000 : ℝ)*(sp_s0_14) + (2354668682997/1000000000000 : ℝ)*(sp_s0_15) + (73579649871/31250000000 : ℝ)*(sp_s0_16) + (1217892461221/1000000000000 : ℝ)*(sp_s0_20) + (1333652084557/1000000000000 : ℝ)*(f.failure) + (2354668682997/1000000000000 : ℝ)*(f.sum) + (3219375888222149/10000000000000000000000000000 : ℝ)*base62 + (77137252209623/200000000000000000000000000 : ℝ)*base65 + (313256414410847/10000000000000000000000000000 : ℝ)*base66 + (96338113274291/200000000000000000000000000 : ℝ)*base69 + (1737948514582151/10000000000000000000000000000 : ℝ)*base70 + (2859464450589153/10000000000000000000000000000 : ℝ)*base73 + (970129745063301/10000000000000000000000000000 : ℝ)*base75 + (436040437936699/10000000000000000000000000000 : ℝ)*base77 + (1824750541589153/5000000000000000000000000000 : ℝ)*base79 + (30701/100000000000000000 : ℝ)*base87 + (30701/100000000000000000 : ℝ)*base89 + (130701/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77783/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77783/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (55633263374421448332993/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761035609349/1000000000000 : ℝ)*(base1) + (949099824673/1000000000000 : ℝ)*(base7) + (48309847747/1000000000000 : ℝ)*(base39) + (195675336643/500000000000 : ℝ)*(base44) + (68017643191/200000000000 : ℝ)*(base50) + (2664683/1000000000000 : ℝ)*(base60) + (2148899332847/1000000000000 : ℝ)*(major_s0_0) + (878774329781/500000000000 : ℝ)*(major_s0_1) + (2148899332847/1000000000000 : ℝ)*(major_s0_2) + (61983093/1000000000000 : ℝ)*(sp_s0_1) + (394710101971/125000000000 : ℝ)*(sp_s0_21) + (50130813751/25000000000 : ℝ)*(sp_s0_22) + (2396645206419/1000000000000 : ℝ)*(sp_s0_23) + (1124891728269/1000000000000 : ℝ)*(sp_s0_27) + (132817818623/100000000000 : ℝ)*(f.failure) + (2396645206419/1000000000000 : ℝ)*(f.sum) + (3491050229344173/10000000000000000000000000000 : ℝ)*base62 + (3790432855933727/10000000000000000000000000000 : ℝ)*base64 + (1931829853422021/5000000000000000000000000000 : ℝ)*base66 + (6075023616017659/10000000000000000000000000000 : ℝ)*base68 + (2176959216729017/2500000000000000000000000000 : ℝ)*base70 + (4659578434933727/10000000000000000000000000000 : ℝ)*base72 + (1204751846163257/5000000000000000000000000000 : ℝ)*base74 + (2036436875017659/10000000000000000000000000000 : ℝ)*base77 + (2854863423777769/10000000000000000000000000000 : ℝ)*base78 + (1039/10000000000000000 : ℝ)*base87 + (8961/10000000000000000 : ℝ)*base88 + (1039/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (30833/50000 : ℝ) ^ (35/8 : ℝ) ≤ (3015714957033820421/25000000000000000000 : ℝ) := by
    have hpowers : (30833/50000 : ℝ)^35 ≤ (3015714957033820421/25000000000000000000 : ℝ)^8 := by
      have hnat : (30833 : ℕ)^35*25000000000000000000^8 ≤ 3015714957033820421^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30833 50000 3015714957033820421 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30833/50000 : ℝ)) (X := (3015714957033820421/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (28015714957033820421/25000000000000000000 : ℝ) ≤ (2052747478873429/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (28015714957033820421/25000000000000000000 : ℝ)^8 ≤ (2052747478873429/2000000000000000 : ℝ)^35 := by
      have hnat : (28015714957033820421 : ℕ)^8*2000000000000000^35 ≤ 2052747478873429^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28015714957033820421 25000000000000000000 2052747478873429 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2052747478873429/2000000000000000 : ℝ)) (X := (28015714957033820421/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (15515714957033820421/12500000000000000000 : ℝ) ≤ (10506404590771499/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15515714957033820421/12500000000000000000 : ℝ)^8 ≤ (10506404590771499/10000000000000000 : ℝ)^35 := by
      have hnat : (15515714957033820421 : ℕ)^8*10000000000000000^35 ≤ 10506404590771499^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15515714957033820421 12500000000000000000 10506404590771499 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10506404590771499/10000000000000000 : ℝ)) (X := (15515714957033820421/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(52747478873429/1233320000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(121333598202177/3083300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (30833/50000 : ℝ)) (alpha := (52747478873429/1233320000000000 : ℝ)) (beta := (121333598202177/3083300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30833/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(52747478873429/1233320000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(121333598202177/3083300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18221/25000 : ℝ) ^ (35/8 : ℝ) ≤ (25062008480179985803/100000000000000000000 : ℝ) := by
    have hpowers : (18221/25000 : ℝ)^35 ≤ (25062008480179985803/100000000000000000000 : ℝ)^8 := by
      have hnat : (18221 : ℕ)^35*100000000000000000000^8 ≤ 25062008480179985803^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18221 25000 25062008480179985803 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18221/25000 : ℝ)) (X := (25062008480179985803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (125062008480179985803/100000000000000000000 : ℝ) ≤ (2631116632018493/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (125062008480179985803/100000000000000000000 : ℝ)^8 ≤ (2631116632018493/2500000000000000 : ℝ)^35 := by
      have hnat : (125062008480179985803 : ℕ)^8*2500000000000000^35 ≤ 2631116632018493^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125062008480179985803 100000000000000000000 2631116632018493 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2631116632018493/2500000000000000 : ℝ)) (X := (125062008480179985803/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (75062008480179985803/50000000000000000000 : ℝ) ≤ (1371644233236431/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (75062008480179985803/50000000000000000000 : ℝ)^8 ≤ (1371644233236431/1250000000000000 : ℝ)^35 := by
      have hnat : (75062008480179985803 : ℕ)^8*1250000000000000^35 ≤ 1371644233236431^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75062008480179985803 50000000000000000000 1371644233236431 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1371644233236431/1250000000000000 : ℝ)) (X := (75062008480179985803/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(131116632018493/1822100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(112171834454369/1822100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (18221/25000 : ℝ)) (alpha := (131116632018493/1822100000000000 : ℝ)) (beta := (112171834454369/1822100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (18221/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(131116632018493/1822100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(112171834454369/1822100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (77783/100000 : ℝ) ^ (35/8 : ℝ) ≤ (16656759696908498169/50000000000000000000 : ℝ) := by
    have hpowers : (77783/100000 : ℝ)^35 ≤ (16656759696908498169/50000000000000000000 : ℝ)^8 := by
      have hnat : (77783 : ℕ)^35*50000000000000000000^8 ≤ 16656759696908498169^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77783 100000 16656759696908498169 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77783/100000 : ℝ)) (X := (16656759696908498169/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (66656759696908498169/50000000000000000000 : ℝ) ≤ (10679297198589071/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (66656759696908498169/50000000000000000000 : ℝ)^8 ≤ (10679297198589071/10000000000000000 : ℝ)^35 := by
      have hnat : (66656759696908498169 : ℕ)^8*10000000000000000^35 ≤ 10679297198589071^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66656759696908498169 50000000000000000000 10679297198589071 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10679297198589071/10000000000000000 : ℝ)) (X := (66656759696908498169/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (41656759696908498169/25000000000000000000 : ℝ) ≤ (449515500152739/400000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (41656759696908498169/25000000000000000000 : ℝ)^8 ≤ (449515500152739/400000000000000 : ℝ)^35 := by
      have hnat : (41656759696908498169 : ℕ)^8*400000000000000^35 ≤ 449515500152739^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41656759696908498169 25000000000000000000 449515500152739 400000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (449515500152739/400000000000000 : ℝ)) (X := (41656759696908498169/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(679297198589071/7778300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(139647576307351/1944575000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (77783/100000 : ℝ)) (alpha := (679297198589071/7778300000000000 : ℝ)) (beta := (139647576307351/1944575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (77783/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(679297198589071/7778300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(139647576307351/1944575000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-316915579/625000000 : ℝ)*X 0 0+(1919003289/5000000000 : ℝ)*X 0 1+(955679669/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((431613161/1000000000 : ℝ)*X 1 0+(-1569213841/5000000000 : ℝ)*X 1 1+(1047008817/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4373399781/10000000000 : ℝ)*X 2 0+(1286435067/2500000000 : ℝ)*X 2 1+(-635723549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1811692497/10000000000 : ℝ)*X 0 0+(5447979307/10000000000 : ℝ)*X 0 1+(5194453009/10000000000 : ℝ)*X 0 2+(1811692497/10000000000 : ℝ)*X 1 0+(5447979307/10000000000 : ℝ)*X 1 1+(5194453009/10000000000 : ℝ)*X 1 2+(1811692497/10000000000 : ℝ)*X 2 0+(5447979307/10000000000 : ℝ)*X 2 1+(5194453009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310027_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-116411817500249328592748032748438907/17479647559127600000000000000000000 : ℝ) := by norm_num
    linear_combination (85579/1000000000000 : ℝ)*(base5) + (44759/1000000000000 : ℝ)*(base8) + (221893/1000000000000 : ℝ)*(base23) + (84787/250000000000 : ℝ)*(base29) + (11409/200000000000 : ℝ)*(base49) + (349463411261/1000000000000 : ℝ)*(base50) + (33730372033/100000000000 : ℝ)*(base60) + (73623/1000000000000 : ℝ)*(ratio_s0_0) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2219949701679/1000000000000 : ℝ)*(sp_s1_0) + (1109974873219/500000000000 : ℝ)*(sp_s1_1) + (554987402531/250000000000 : ℝ)*(sp_s1_2) + (999999575273/1000000000000 : ℝ)*(sp_s1_6) + (1109974873219/500000000000 : ℝ)*(f.sum) + (69334651684002629/566913617200000000000000000000 : ℝ)*base63 + (168408247605241/777830000000000000000000000 : ℝ)*base65 + (54032741237119/182210000000000000000000000 : ℝ)*base67 + (233744404344163/777830000000000000000000000 : ℝ)*base68 + (1883227069927082259/4796566478000000000000000000000 : ℝ)*base71 + (11138605172729/308330000000000000000000000 : ℝ)*base73 + (449165257799/7288400000000000000000000 : ℝ)*base75 + (205384917057181/308330000000000000000000000 : ℝ)*base77 + (733237846486748839/5618080930000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b015 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=27 := by omega
  rcases hc with rfl
  · exact collision_c310027 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

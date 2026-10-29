-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:56:08.843701+00:00
-- url     : https://prove2.me/submissions/d8a72016-ed3e-4c38-86d7-f42b8c184d0e

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
theorem collision_support_c324037_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-400633369/5000000000 : ℝ)*x 0 + (-6831444183/10000000000 : ℝ)*x 1 + (4044321907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400633369/5000000000 : ℝ)^43 ≤ (224999673661/5000000000000 : ℝ)^35 := by
    have hnat : (400633369 : ℕ)^43*5000000000000^35 ≤ 224999673661^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400633369 5000000000 224999673661 5000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6831444183/10000000000 : ℝ)^43 ≤ (15654053875399/25000000000000 : ℝ)^35 := by
    have hnat : (6831444183 : ℕ)^43*25000000000000^35 ≤ 15654053875399^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6831444183 10000000000 15654053875399 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4044321907/10000000000 : ℝ)^43 ≤ (32883791016441/100000000000000 : ℝ)^35 := by
    have hnat : (4044321907 : ℕ)^43*100000000000000^35 ≤ 32883791016441^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044321907 10000000000 32883791016441 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400633369/5000000000 : ℝ), (-6831444183/10000000000 : ℝ), (4044321907/10000000000 : ℝ)] ![(224999673661/5000000000000 : ℝ), (15654053875399/25000000000000 : ℝ), (32883791016441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400633369/5000000000 : ℝ)|^43 ≤ (224999673661/5000000000000 : ℝ)^35
        have hw : |(-400633369/5000000000 : ℝ)|=(400633369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6831444183/10000000000 : ℝ)|^43 ≤ (15654053875399/25000000000000 : ℝ)^35
        have hw : |(-6831444183/10000000000 : ℝ)|=(6831444183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4044321907/10000000000 : ℝ)|^43 ≤ (32883791016441/100000000000000 : ℝ)^35
        have hw : |(4044321907/10000000000 : ℝ)|=(4044321907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (153816651/312500000 : ℝ)*x 0 + (613180093/2000000000 : ℝ)*x 1 + (528671903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153816651/312500000 : ℝ)^43 ≤ (5232369307621/12500000000000 : ℝ)^35 := by
    have hnat : (153816651 : ℕ)^43*12500000000000^35 ≤ 5232369307621^35*312500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153816651 312500000 5232369307621 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613180093/2000000000 : ℝ)^43 ≤ (11699569884989/50000000000000 : ℝ)^35 := by
    have hnat : (613180093 : ℕ)^43*50000000000000^35 ≤ 11699569884989^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613180093 2000000000 11699569884989 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528671903/1250000000 : ℝ)^43 ≤ (34741905753659/100000000000000 : ℝ)^35 := by
    have hnat : (528671903 : ℕ)^43*100000000000000^35 ≤ 34741905753659^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528671903 1250000000 34741905753659 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153816651/312500000 : ℝ), (613180093/2000000000 : ℝ), (528671903/1250000000 : ℝ)] ![(5232369307621/12500000000000 : ℝ), (11699569884989/50000000000000 : ℝ), (34741905753659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153816651/312500000 : ℝ)|^43 ≤ (5232369307621/12500000000000 : ℝ)^35
        have hw : |(153816651/312500000 : ℝ)|=(153816651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(613180093/2000000000 : ℝ)|^43 ≤ (11699569884989/50000000000000 : ℝ)^35
        have hw : |(613180093/2000000000 : ℝ)|=(613180093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528671903/1250000000 : ℝ)|^43 ≤ (34741905753659/100000000000000 : ℝ)^35
        have hw : |(528671903/1250000000 : ℝ)|=(528671903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (984426527/2000000000 : ℝ)*x 0 + (-2987469373/10000000000 : ℝ)*x 1 + (-86037803/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984426527/2000000000 : ℝ)^43 ≤ (41858952402701/100000000000000 : ℝ)^35 := by
    have hnat : (984426527 : ℕ)^43*100000000000000^35 ≤ 41858952402701^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984426527 2000000000 41858952402701 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987469373/10000000000 : ℝ)^43 ≤ (22665892483123/100000000000000 : ℝ)^35 := by
    have hnat : (2987469373 : ℕ)^43*100000000000000^35 ≤ 22665892483123^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987469373 10000000000 22665892483123 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86037803/200000000 : ℝ)^43 ≤ (8868788776099/25000000000000 : ℝ)^35 := by
    have hnat : (86037803 : ℕ)^43*25000000000000^35 ≤ 8868788776099^35*200000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86037803 200000000 8868788776099 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984426527/2000000000 : ℝ), (-2987469373/10000000000 : ℝ), (-86037803/200000000 : ℝ)] ![(41858952402701/100000000000000 : ℝ), (22665892483123/100000000000000 : ℝ), (8868788776099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984426527/2000000000 : ℝ)|^43 ≤ (41858952402701/100000000000000 : ℝ)^35
        have hw : |(984426527/2000000000 : ℝ)|=(984426527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2987469373/10000000000 : ℝ)|^43 ≤ (22665892483123/100000000000000 : ℝ)^35
        have hw : |(-2987469373/10000000000 : ℝ)|=(2987469373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86037803/200000000 : ℝ)|^43 ≤ (8868788776099/25000000000000 : ℝ)^35
        have hw : |(-86037803/200000000 : ℝ)|=(86037803/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7981319027/10000000000 : ℝ)*x 0 + (-13183981/100000000 : ℝ)*x 1 + (447699407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7981319027/10000000000 : ℝ)^43 ≤ (1516078656999/2000000000000 : ℝ)^35 := by
    have hnat : (7981319027 : ℕ)^43*2000000000000^35 ≤ 1516078656999^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7981319027 10000000000 1516078656999 2000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13183981/100000000 : ℝ)^43 ≤ (8296871340677/100000000000000 : ℝ)^35 := by
    have hnat : (13183981 : ℕ)^43*100000000000000^35 ≤ 8296871340677^35*100000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13183981 100000000 8296871340677 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447699407/2000000000 : ℝ)^43 ≤ (3974798946903/25000000000000 : ℝ)^35 := by
    have hnat : (447699407 : ℕ)^43*25000000000000^35 ≤ 3974798946903^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447699407 2000000000 3974798946903 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7981319027/10000000000 : ℝ), (-13183981/100000000 : ℝ), (447699407/2000000000 : ℝ)] ![(1516078656999/2000000000000 : ℝ), (8296871340677/100000000000000 : ℝ), (3974798946903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7981319027/10000000000 : ℝ)|^43 ≤ (1516078656999/2000000000000 : ℝ)^35
        have hw : |(7981319027/10000000000 : ℝ)|=(7981319027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13183981/100000000 : ℝ)|^43 ≤ (8296871340677/100000000000000 : ℝ)^35
        have hw : |(-13183981/100000000 : ℝ)|=(13183981/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447699407/2000000000 : ℝ)|^43 ≤ (3974798946903/25000000000000 : ℝ)^35
        have hw : |(447699407/2000000000 : ℝ)|=(447699407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-357993801/5000000000 : ℝ)*x 0 + (-1944397877/2500000000 : ℝ)*x 1 + (2985479417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357993801/5000000000 : ℝ)^43 ≤ (3918949046863/100000000000000 : ℝ)^35 := by
    have hnat : (357993801 : ℕ)^43*100000000000000^35 ≤ 3918949046863^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357993801 5000000000 3918949046863 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944397877/2500000000 : ℝ)^43 ≤ (7343370573673/10000000000000 : ℝ)^35 := by
    have hnat : (1944397877 : ℕ)^43*10000000000000^35 ≤ 7343370573673^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944397877 2500000000 7343370573673 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985479417/10000000000 : ℝ)^43 ≤ (22647345205199/100000000000000 : ℝ)^35 := by
    have hnat : (2985479417 : ℕ)^43*100000000000000^35 ≤ 22647345205199^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985479417 10000000000 22647345205199 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357993801/5000000000 : ℝ), (-1944397877/2500000000 : ℝ), (2985479417/10000000000 : ℝ)] ![(3918949046863/100000000000000 : ℝ), (7343370573673/10000000000000 : ℝ), (22647345205199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357993801/5000000000 : ℝ)|^43 ≤ (3918949046863/100000000000000 : ℝ)^35
        have hw : |(-357993801/5000000000 : ℝ)|=(357993801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944397877/2500000000 : ℝ)|^43 ≤ (7343370573673/10000000000000 : ℝ)^35
        have hw : |(-1944397877/2500000000 : ℝ)|=(1944397877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2985479417/10000000000 : ℝ)|^43 ≤ (22647345205199/100000000000000 : ℝ)^35
        have hw : |(2985479417/10000000000 : ℝ)|=(2985479417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2408179169/5000000000 : ℝ)*x 0 + (2886583829/10000000000 : ℝ)*x 1 + (180084257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2408179169/5000000000 : ℝ)^43 ≤ (40756546015987/100000000000000 : ℝ)^35 := by
    have hnat : (2408179169 : ℕ)^43*100000000000000^35 ≤ 40756546015987^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408179169 5000000000 40756546015987 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2886583829/10000000000 : ℝ)^43 ≤ (10864591916931/50000000000000 : ℝ)^35 := by
    have hnat : (2886583829 : ℕ)^43*50000000000000^35 ≤ 10864591916931^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886583829 10000000000 10864591916931 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180084257/400000000 : ℝ)^43 ≤ (7502854029261/20000000000000 : ℝ)^35 := by
    have hnat : (180084257 : ℕ)^43*20000000000000^35 ≤ 7502854029261^35*400000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180084257 400000000 7502854029261 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2408179169/5000000000 : ℝ), (2886583829/10000000000 : ℝ), (180084257/400000000 : ℝ)] ![(40756546015987/100000000000000 : ℝ), (10864591916931/50000000000000 : ℝ), (7502854029261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2408179169/5000000000 : ℝ)|^43 ≤ (40756546015987/100000000000000 : ℝ)^35
        have hw : |(2408179169/5000000000 : ℝ)|=(2408179169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2886583829/10000000000 : ℝ)|^43 ≤ (10864591916931/50000000000000 : ℝ)^35
        have hw : |(2886583829/10000000000 : ℝ)|=(2886583829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180084257/400000000 : ℝ)|^43 ≤ (7502854029261/20000000000000 : ℝ)^35
        have hw : |(180084257/400000000 : ℝ)|=(180084257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1204089507/2500000000 : ℝ)*x 0 + (-2563318889/10000000000 : ℝ)*x 1 + (-2394123407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1204089507/2500000000 : ℝ)^43 ≤ (10189135698283/25000000000000 : ℝ)^35 := by
    have hnat : (1204089507 : ℕ)^43*25000000000000^35 ≤ 10189135698283^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204089507 2500000000 10189135698283 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563318889/10000000000 : ℝ)^43 ≤ (9389485952409/50000000000000 : ℝ)^35 := by
    have hnat : (2563318889 : ℕ)^43*50000000000000^35 ≤ 9389485952409^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563318889 10000000000 9389485952409 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394123407/5000000000 : ℝ)^43 ≤ (8092897058851/20000000000000 : ℝ)^35 := by
    have hnat : (2394123407 : ℕ)^43*20000000000000^35 ≤ 8092897058851^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394123407 5000000000 8092897058851 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1204089507/2500000000 : ℝ), (-2563318889/10000000000 : ℝ), (-2394123407/5000000000 : ℝ)] ![(10189135698283/25000000000000 : ℝ), (9389485952409/50000000000000 : ℝ), (8092897058851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1204089507/2500000000 : ℝ)|^43 ≤ (10189135698283/25000000000000 : ℝ)^35
        have hw : |(1204089507/2500000000 : ℝ)|=(1204089507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2563318889/10000000000 : ℝ)|^43 ≤ (9389485952409/50000000000000 : ℝ)^35
        have hw : |(-2563318889/10000000000 : ℝ)|=(2563318889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2394123407/5000000000 : ℝ)|^43 ≤ (8092897058851/20000000000000 : ℝ)^35
        have hw : |(-2394123407/5000000000 : ℝ)|=(2394123407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7720561659/10000000000 : ℝ)*x 0 + (-53535159/1250000000 : ℝ)*x 1 + (3250615531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7720561659/10000000000 : ℝ)^43 ≤ (72772725972809/100000000000000 : ℝ)^35 := by
    have hnat : (7720561659 : ℕ)^43*100000000000000^35 ≤ 72772725972809^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7720561659 10000000000 72772725972809 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53535159/1250000000 : ℝ)^43 ≤ (1042200915257/50000000000000 : ℝ)^35 := by
    have hnat : (53535159 : ℕ)^43*50000000000000^35 ≤ 1042200915257^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53535159 1250000000 1042200915257 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3250615531/10000000000 : ℝ)^43 ≤ (12571436086141/50000000000000 : ℝ)^35 := by
    have hnat : (3250615531 : ℕ)^43*50000000000000^35 ≤ 12571436086141^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3250615531 10000000000 12571436086141 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7720561659/10000000000 : ℝ), (-53535159/1250000000 : ℝ), (3250615531/10000000000 : ℝ)] ![(72772725972809/100000000000000 : ℝ), (1042200915257/50000000000000 : ℝ), (12571436086141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7720561659/10000000000 : ℝ)|^43 ≤ (72772725972809/100000000000000 : ℝ)^35
        have hw : |(7720561659/10000000000 : ℝ)|=(7720561659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53535159/1250000000 : ℝ)|^43 ≤ (1042200915257/50000000000000 : ℝ)^35
        have hw : |(-53535159/1250000000 : ℝ)|=(53535159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3250615531/10000000000 : ℝ)|^43 ≤ (12571436086141/50000000000000 : ℝ)^35
        have hw : |(3250615531/10000000000 : ℝ)|=(3250615531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-52426847/2500000000 : ℝ)*x 0 + (-6677294643/10000000000 : ℝ)*x 1 + (4573671693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52426847/2500000000 : ℝ)^43 ≤ (866927109177/100000000000000 : ℝ)^35 := by
    have hnat : (52426847 : ℕ)^43*100000000000000^35 ≤ 866927109177^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52426847 2500000000 866927109177 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6677294643/10000000000 : ℝ)^43 ≤ (15221212321487/25000000000000 : ℝ)^35 := by
    have hnat : (6677294643 : ℕ)^43*25000000000000^35 ≤ 15221212321487^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6677294643 10000000000 15221212321487 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4573671693/10000000000 : ℝ)^43 ≤ (19124111800839/50000000000000 : ℝ)^35 := by
    have hnat : (4573671693 : ℕ)^43*50000000000000^35 ≤ 19124111800839^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573671693 10000000000 19124111800839 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52426847/2500000000 : ℝ), (-6677294643/10000000000 : ℝ), (4573671693/10000000000 : ℝ)] ![(866927109177/100000000000000 : ℝ), (15221212321487/25000000000000 : ℝ), (19124111800839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52426847/2500000000 : ℝ)|^43 ≤ (866927109177/100000000000000 : ℝ)^35
        have hw : |(-52426847/2500000000 : ℝ)|=(52426847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6677294643/10000000000 : ℝ)|^43 ≤ (15221212321487/25000000000000 : ℝ)^35
        have hw : |(-6677294643/10000000000 : ℝ)|=(6677294643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4573671693/10000000000 : ℝ)|^43 ≤ (19124111800839/50000000000000 : ℝ)^35
        have hw : |(4573671693/10000000000 : ℝ)|=(4573671693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4655062389/10000000000 : ℝ)*x 0 + (3123165537/10000000000 : ℝ)*x 1 + (889903611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4655062389/10000000000 : ℝ)^43 ≤ (39086138306501/100000000000000 : ℝ)^35 := by
    have hnat : (4655062389 : ℕ)^43*100000000000000^35 ≤ 39086138306501^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655062389 10000000000 39086138306501 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123165537/10000000000 : ℝ)^43 ≤ (23937228291961/100000000000000 : ℝ)^35 := by
    have hnat : (3123165537 : ℕ)^43*100000000000000^35 ≤ 23937228291961^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123165537 10000000000 23937228291961 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889903611/2000000000 : ℝ)^43 ≤ (3697663337689/10000000000000 : ℝ)^35 := by
    have hnat : (889903611 : ℕ)^43*10000000000000^35 ≤ 3697663337689^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889903611 2000000000 3697663337689 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4655062389/10000000000 : ℝ), (3123165537/10000000000 : ℝ), (889903611/2000000000 : ℝ)] ![(39086138306501/100000000000000 : ℝ), (23937228291961/100000000000000 : ℝ), (3697663337689/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4655062389/10000000000 : ℝ)|^43 ≤ (39086138306501/100000000000000 : ℝ)^35
        have hw : |(4655062389/10000000000 : ℝ)|=(4655062389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123165537/10000000000 : ℝ)|^43 ≤ (23937228291961/100000000000000 : ℝ)^35
        have hw : |(3123165537/10000000000 : ℝ)|=(3123165537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(889903611/2000000000 : ℝ)|^43 ≤ (3697663337689/10000000000000 : ℝ)^35
        have hw : |(889903611/2000000000 : ℝ)|=(889903611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1383147229/2500000000 : ℝ)*x 0 + (-21548529/80000000 : ℝ)*x 1 + (-3927158203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1383147229/2500000000 : ℝ)^43 ≤ (24162350746177/50000000000000 : ℝ)^35 := by
    have hnat : (1383147229 : ℕ)^43*50000000000000^35 ≤ 24162350746177^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383147229 2500000000 24162350746177 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21548529/80000000 : ℝ)^43 ≤ (19957990742271/100000000000000 : ℝ)^35 := by
    have hnat : (21548529 : ℕ)^43*100000000000000^35 ≤ 19957990742271^35*80000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21548529 80000000 19957990742271 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3927158203/10000000000 : ℝ)^43 ≤ (31717307753649/100000000000000 : ℝ)^35 := by
    have hnat : (3927158203 : ℕ)^43*100000000000000^35 ≤ 31717307753649^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3927158203 10000000000 31717307753649 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1383147229/2500000000 : ℝ), (-21548529/80000000 : ℝ), (-3927158203/10000000000 : ℝ)] ![(24162350746177/50000000000000 : ℝ), (19957990742271/100000000000000 : ℝ), (31717307753649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1383147229/2500000000 : ℝ)|^43 ≤ (24162350746177/50000000000000 : ℝ)^35
        have hw : |(1383147229/2500000000 : ℝ)|=(1383147229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21548529/80000000 : ℝ)|^43 ≤ (19957990742271/100000000000000 : ℝ)^35
        have hw : |(-21548529/80000000 : ℝ)|=(21548529/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3927158203/10000000000 : ℝ)|^43 ≤ (31717307753649/100000000000000 : ℝ)^35
        have hw : |(-3927158203/10000000000 : ℝ)|=(3927158203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4410780157/5000000000 : ℝ)*x 0 + (-540690721/5000000000 : ℝ)*x 1 + (625105981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4410780157/5000000000 : ℝ)^43 ≤ (85723253137417/100000000000000 : ℝ)^35 := by
    have hnat : (4410780157 : ℕ)^43*100000000000000^35 ≤ 85723253137417^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410780157 5000000000 85723253137417 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540690721/5000000000 : ℝ)^43 ≤ (3251951774283/50000000000000 : ℝ)^35 := by
    have hnat : (540690721 : ℕ)^43*50000000000000^35 ≤ 3251951774283^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540690721 5000000000 3251951774283 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625105981/5000000000 : ℝ)^43 ≤ (3886421652651/50000000000000 : ℝ)^35 := by
    have hnat : (625105981 : ℕ)^43*50000000000000^35 ≤ 3886421652651^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625105981 5000000000 3886421652651 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4410780157/5000000000 : ℝ), (-540690721/5000000000 : ℝ), (625105981/5000000000 : ℝ)] ![(85723253137417/100000000000000 : ℝ), (3251951774283/50000000000000 : ℝ), (3886421652651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4410780157/5000000000 : ℝ)|^43 ≤ (85723253137417/100000000000000 : ℝ)^35
        have hw : |(4410780157/5000000000 : ℝ)|=(4410780157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-540690721/5000000000 : ℝ)|^43 ≤ (3251951774283/50000000000000 : ℝ)^35
        have hw : |(-540690721/5000000000 : ℝ)|=(540690721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625105981/5000000000 : ℝ)|^43 ≤ (3886421652651/50000000000000 : ℝ)^35
        have hw : |(625105981/5000000000 : ℝ)|=(625105981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-13214019/500000000 : ℝ)*x 0 + (-3676063491/5000000000 : ℝ)*x 1 + (757118153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13214019/500000000 : ℝ)^43 ≤ (1151845016769/100000000000000 : ℝ)^35 := by
    have hnat : (13214019 : ℕ)^43*100000000000000^35 ≤ 1151845016769^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13214019 500000000 1151845016769 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3676063491/5000000000 : ℝ)^43 ≤ (68529699548693/100000000000000 : ℝ)^35 := by
    have hnat : (3676063491 : ℕ)^43*100000000000000^35 ≤ 68529699548693^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3676063491 5000000000 68529699548693 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757118153/2000000000 : ℝ)^43 ≤ (15159227709183/50000000000000 : ℝ)^35 := by
    have hnat : (757118153 : ℕ)^43*50000000000000^35 ≤ 15159227709183^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757118153 2000000000 15159227709183 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13214019/500000000 : ℝ), (-3676063491/5000000000 : ℝ), (757118153/2000000000 : ℝ)] ![(1151845016769/100000000000000 : ℝ), (68529699548693/100000000000000 : ℝ), (15159227709183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13214019/500000000 : ℝ)|^43 ≤ (1151845016769/100000000000000 : ℝ)^35
        have hw : |(-13214019/500000000 : ℝ)|=(13214019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3676063491/5000000000 : ℝ)|^43 ≤ (68529699548693/100000000000000 : ℝ)^35
        have hw : |(-3676063491/5000000000 : ℝ)|=(3676063491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(757118153/2000000000 : ℝ)|^43 ≤ (15159227709183/50000000000000 : ℝ)^35
        have hw : |(757118153/2000000000 : ℝ)|=(757118153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5478015651/10000000000 : ℝ)*x 0 + (352937381/1250000000 : ℝ)*x 1 + (773230031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5478015651/10000000000 : ℝ)^43 ≤ (2983733519407/6250000000000 : ℝ)^35 := by
    have hnat : (5478015651 : ℕ)^43*6250000000000^35 ≤ 2983733519407^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478015651 10000000000 2983733519407 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352937381/1250000000 : ℝ)^43 ≤ (21147225347891/100000000000000 : ℝ)^35 := by
    have hnat : (352937381 : ℕ)^43*100000000000000^35 ≤ 21147225347891^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352937381 1250000000 21147225347891 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773230031/2000000000 : ℝ)^43 ≤ (6222607667611/20000000000000 : ℝ)^35 := by
    have hnat : (773230031 : ℕ)^43*20000000000000^35 ≤ 6222607667611^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773230031 2000000000 6222607667611 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5478015651/10000000000 : ℝ), (352937381/1250000000 : ℝ), (773230031/2000000000 : ℝ)] ![(2983733519407/6250000000000 : ℝ), (21147225347891/100000000000000 : ℝ), (6222607667611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5478015651/10000000000 : ℝ)|^43 ≤ (2983733519407/6250000000000 : ℝ)^35
        have hw : |(5478015651/10000000000 : ℝ)|=(5478015651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352937381/1250000000 : ℝ)|^43 ≤ (21147225347891/100000000000000 : ℝ)^35
        have hw : |(352937381/1250000000 : ℝ)|=(352937381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773230031/2000000000 : ℝ)|^43 ≤ (6222607667611/20000000000000 : ℝ)^35
        have hw : |(773230031/2000000000 : ℝ)|=(773230031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (580113143/1250000000 : ℝ)*x 0 + (-3048309539/10000000000 : ℝ)*x 1 + (-4532489403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (580113143/1250000000 : ℝ)^43 ≤ (2433759222603/6250000000000 : ℝ)^35 := by
    have hnat : (580113143 : ℕ)^43*6250000000000^35 ≤ 2433759222603^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580113143 1250000000 2433759222603 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3048309539/10000000000 : ℝ)^43 ≤ (5808576550451/25000000000000 : ℝ)^35 := by
    have hnat : (3048309539 : ℕ)^43*25000000000000^35 ≤ 5808576550451^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048309539 10000000000 5808576550451 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532489403/10000000000 : ℝ)^43 ≤ (7565109244747/20000000000000 : ℝ)^35 := by
    have hnat : (4532489403 : ℕ)^43*20000000000000^35 ≤ 7565109244747^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532489403 10000000000 7565109244747 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(580113143/1250000000 : ℝ), (-3048309539/10000000000 : ℝ), (-4532489403/10000000000 : ℝ)] ![(2433759222603/6250000000000 : ℝ), (5808576550451/25000000000000 : ℝ), (7565109244747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(580113143/1250000000 : ℝ)|^43 ≤ (2433759222603/6250000000000 : ℝ)^35
        have hw : |(580113143/1250000000 : ℝ)|=(580113143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3048309539/10000000000 : ℝ)|^43 ≤ (5808576550451/25000000000000 : ℝ)^35
        have hw : |(-3048309539/10000000000 : ℝ)|=(3048309539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4532489403/10000000000 : ℝ)|^43 ≤ (7565109244747/20000000000000 : ℝ)^35
        have hw : |(-4532489403/10000000000 : ℝ)|=(4532489403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (221588691/250000000 : ℝ)*x 0 + (-438835523/10000000000 : ℝ)*x 1 + (347040301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221588691/250000000 : ℝ)^43 ≤ (86224795647811/100000000000000 : ℝ)^35 := by
    have hnat : (221588691 : ℕ)^43*100000000000000^35 ≤ 86224795647811^35*250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221588691 250000000 86224795647811 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438835523/10000000000 : ℝ)^43 ≤ (214768583637/10000000000000 : ℝ)^35 := by
    have hnat : (438835523 : ℕ)^43*10000000000000^35 ≤ 214768583637^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438835523 10000000000 214768583637 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347040301/2000000000 : ℝ)^43 ≤ (2325503700537/20000000000000 : ℝ)^35 := by
    have hnat : (347040301 : ℕ)^43*20000000000000^35 ≤ 2325503700537^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347040301 2000000000 2325503700537 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(221588691/250000000 : ℝ), (-438835523/10000000000 : ℝ), (347040301/2000000000 : ℝ)] ![(86224795647811/100000000000000 : ℝ), (214768583637/10000000000000 : ℝ), (2325503700537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(221588691/250000000 : ℝ)|^43 ≤ (86224795647811/100000000000000 : ℝ)^35
        have hw : |(221588691/250000000 : ℝ)|=(221588691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438835523/10000000000 : ℝ)|^43 ≤ (214768583637/10000000000000 : ℝ)^35
        have hw : |(-438835523/10000000000 : ℝ)|=(438835523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(347040301/2000000000 : ℝ)|^43 ≤ (2325503700537/20000000000000 : ℝ)^35
        have hw : |(347040301/2000000000 : ℝ)|=(347040301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-258015967/1250000000 : ℝ)*x 0 + (-1128938581/2000000000 : ℝ)*x 1 + (2180653589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258015967/1250000000 : ℝ)^43 ≤ (3597865607969/25000000000000 : ℝ)^35 := by
    have hnat : (258015967 : ℕ)^43*25000000000000^35 ≤ 3597865607969^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258015967 1250000000 3597865607969 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128938581/2000000000 : ℝ)^43 ≤ (12382615886503/25000000000000 : ℝ)^35 := by
    have hnat : (1128938581 : ℕ)^43*25000000000000^35 ≤ 12382615886503^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128938581 2000000000 12382615886503 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180653589/5000000000 : ℝ)^43 ≤ (7215614800923/20000000000000 : ℝ)^35 := by
    have hnat : (2180653589 : ℕ)^43*20000000000000^35 ≤ 7215614800923^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180653589 5000000000 7215614800923 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258015967/1250000000 : ℝ), (-1128938581/2000000000 : ℝ), (2180653589/5000000000 : ℝ)] ![(3597865607969/25000000000000 : ℝ), (12382615886503/25000000000000 : ℝ), (7215614800923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258015967/1250000000 : ℝ)|^43 ≤ (3597865607969/25000000000000 : ℝ)^35
        have hw : |(-258015967/1250000000 : ℝ)|=(258015967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128938581/2000000000 : ℝ)|^43 ≤ (12382615886503/25000000000000 : ℝ)^35
        have hw : |(-1128938581/2000000000 : ℝ)|=(1128938581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180653589/5000000000 : ℝ)|^43 ≤ (7215614800923/20000000000000 : ℝ)^35
        have hw : |(2180653589/5000000000 : ℝ)|=(2180653589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4710271463/10000000000 : ℝ)*x 0 + (1690004873/5000000000 : ℝ)*x 1 + (2076143647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4710271463/10000000000 : ℝ)^43 ≤ (19828213398089/50000000000000 : ℝ)^35 := by
    have hnat : (4710271463 : ℕ)^43*50000000000000^35 ≤ 19828213398089^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4710271463 10000000000 19828213398089 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690004873/5000000000 : ℝ)^43 ≤ (13189005832323/50000000000000 : ℝ)^35 := by
    have hnat : (1690004873 : ℕ)^43*50000000000000^35 ≤ 13189005832323^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690004873 5000000000 13189005832323 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076143647/5000000000 : ℝ)^43 ≤ (8491390382103/25000000000000 : ℝ)^35 := by
    have hnat : (2076143647 : ℕ)^43*25000000000000^35 ≤ 8491390382103^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076143647 5000000000 8491390382103 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4710271463/10000000000 : ℝ), (1690004873/5000000000 : ℝ), (2076143647/5000000000 : ℝ)] ![(19828213398089/50000000000000 : ℝ), (13189005832323/50000000000000 : ℝ), (8491390382103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4710271463/10000000000 : ℝ)|^43 ≤ (19828213398089/50000000000000 : ℝ)^35
        have hw : |(4710271463/10000000000 : ℝ)|=(4710271463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1690004873/5000000000 : ℝ)|^43 ≤ (13189005832323/50000000000000 : ℝ)^35
        have hw : |(1690004873/5000000000 : ℝ)|=(1690004873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2076143647/5000000000 : ℝ)|^43 ≤ (8491390382103/25000000000000 : ℝ)^35
        have hw : |(2076143647/5000000000 : ℝ)|=(2076143647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2350227869/5000000000 : ℝ)*x 0 + (-338463681/1000000000 : ℝ)*x 1 + (-259873223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2350227869/5000000000 : ℝ)^43 ≤ (19777460956313/50000000000000 : ℝ)^35 := by
    have hnat : (2350227869 : ℕ)^43*50000000000000^35 ≤ 19777460956313^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350227869 5000000000 19777460956313 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338463681/1000000000 : ℝ)^43 ≤ (26422382534011/100000000000000 : ℝ)^35 := by
    have hnat : (338463681 : ℕ)^43*100000000000000^35 ≤ 26422382534011^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338463681 1000000000 26422382534011 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259873223/625000000 : ℝ)^43 ≤ (17011347771187/50000000000000 : ℝ)^35 := by
    have hnat : (259873223 : ℕ)^43*50000000000000^35 ≤ 17011347771187^35*625000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259873223 625000000 17011347771187 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2350227869/5000000000 : ℝ), (-338463681/1000000000 : ℝ), (-259873223/625000000 : ℝ)] ![(19777460956313/50000000000000 : ℝ), (26422382534011/100000000000000 : ℝ), (17011347771187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2350227869/5000000000 : ℝ)|^43 ≤ (19777460956313/50000000000000 : ℝ)^35
        have hw : |(2350227869/5000000000 : ℝ)|=(2350227869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338463681/1000000000 : ℝ)|^43 ≤ (26422382534011/100000000000000 : ℝ)^35
        have hw : |(-338463681/1000000000 : ℝ)|=(338463681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259873223/625000000 : ℝ)|^43 ≤ (17011347771187/50000000000000 : ℝ)^35
        have hw : |(-259873223/625000000 : ℝ)|=(259873223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324037_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6104742133/10000000000 : ℝ)*x 0 + (-674468689/2000000000 : ℝ)*x 1 + (651400613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6104742133/10000000000 : ℝ)^43 ≤ (27267605507593/50000000000000 : ℝ)^35 := by
    have hnat : (6104742133 : ℕ)^43*50000000000000^35 ≤ 27267605507593^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6104742133 10000000000 27267605507593 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674468689/2000000000 : ℝ)^43 ≤ (6576131707317/25000000000000 : ℝ)^35 := by
    have hnat : (674468689 : ℕ)^43*25000000000000^35 ≤ 6576131707317^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674468689 2000000000 6576131707317 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651400613/2500000000 : ℝ)^43 ≤ (1197516384003/6250000000000 : ℝ)^35 := by
    have hnat : (651400613 : ℕ)^43*6250000000000^35 ≤ 1197516384003^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651400613 2500000000 1197516384003 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6104742133/10000000000 : ℝ), (-674468689/2000000000 : ℝ), (651400613/2500000000 : ℝ)] ![(27267605507593/50000000000000 : ℝ), (6576131707317/25000000000000 : ℝ), (1197516384003/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6104742133/10000000000 : ℝ)|^43 ≤ (27267605507593/50000000000000 : ℝ)^35
        have hw : |(6104742133/10000000000 : ℝ)|=(6104742133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674468689/2000000000 : ℝ)|^43 ≤ (6576131707317/25000000000000 : ℝ)^35
        have hw : |(-674468689/2000000000 : ℝ)|=(674468689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651400613/2500000000 : ℝ)|^43 ≤ (1197516384003/6250000000000 : ℝ)^35
        have hw : |(651400613/2500000000 : ℝ)|=(651400613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324037 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-400633369/5000000000 : ℝ)*X 0 0+(-6831444183/10000000000 : ℝ)*X 0 1+(4044321907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((153816651/312500000 : ℝ)*X 1 0+(613180093/2000000000 : ℝ)*X 1 1+(528671903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((984426527/2000000000 : ℝ)*X 2 0+(-2987469373/10000000000 : ℝ)*X 2 1+(-86037803/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7981319027/10000000000 : ℝ)*X 0 0+(-13183981/100000000 : ℝ)*X 0 1+(447699407/2000000000 : ℝ)*X 0 2+(7981319027/10000000000 : ℝ)*X 1 0+(-13183981/100000000 : ℝ)*X 1 1+(447699407/2000000000 : ℝ)*X 1 2+(7981319027/10000000000 : ℝ)*X 2 0+(-13183981/100000000 : ℝ)*X 2 1+(447699407/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-357993801/5000000000 : ℝ)*X 0 0+(-1944397877/2500000000 : ℝ)*X 0 1+(2985479417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2408179169/5000000000 : ℝ)*X 1 0+(2886583829/10000000000 : ℝ)*X 1 1+(180084257/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1204089507/2500000000 : ℝ)*X 2 0+(-2563318889/10000000000 : ℝ)*X 2 1+(-2394123407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7720561659/10000000000 : ℝ)*X 0 0+(-53535159/1250000000 : ℝ)*X 0 1+(3250615531/10000000000 : ℝ)*X 0 2+(7720561659/10000000000 : ℝ)*X 1 0+(-53535159/1250000000 : ℝ)*X 1 1+(3250615531/10000000000 : ℝ)*X 1 2+(7720561659/10000000000 : ℝ)*X 2 0+(-53535159/1250000000 : ℝ)*X 2 1+(3250615531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-52426847/2500000000 : ℝ)*X 0 0+(-6677294643/10000000000 : ℝ)*X 0 1+(4573671693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4655062389/10000000000 : ℝ)*X 1 0+(3123165537/10000000000 : ℝ)*X 1 1+(889903611/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1383147229/2500000000 : ℝ)*X 2 0+(-21548529/80000000 : ℝ)*X 2 1+(-3927158203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4410780157/5000000000 : ℝ)*X 0 0+(-540690721/5000000000 : ℝ)*X 0 1+(625105981/5000000000 : ℝ)*X 0 2+(4410780157/5000000000 : ℝ)*X 1 0+(-540690721/5000000000 : ℝ)*X 1 1+(625105981/5000000000 : ℝ)*X 1 2+(4410780157/5000000000 : ℝ)*X 2 0+(-540690721/5000000000 : ℝ)*X 2 1+(625105981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-13214019/500000000 : ℝ)*X 0 0+(-3676063491/5000000000 : ℝ)*X 0 1+(757118153/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5478015651/10000000000 : ℝ)*X 1 0+(352937381/1250000000 : ℝ)*X 1 1+(773230031/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((580113143/1250000000 : ℝ)*X 2 0+(-3048309539/10000000000 : ℝ)*X 2 1+(-4532489403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((221588691/250000000 : ℝ)*X 0 0+(-438835523/10000000000 : ℝ)*X 0 1+(347040301/2000000000 : ℝ)*X 0 2+(221588691/250000000 : ℝ)*X 1 0+(-438835523/10000000000 : ℝ)*X 1 1+(347040301/2000000000 : ℝ)*X 1 2+(221588691/250000000 : ℝ)*X 2 0+(-438835523/10000000000 : ℝ)*X 2 1+(347040301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((15737/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15737/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37533672362803987218027/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (637235104487/500000000000 : ℝ)*(base40) + (1492891912779/1000000000000 : ℝ)*(base49) + (467279100431/1000000000000 : ℝ)*(base59) + (2505642390731/500000000000 : ℝ)*(major_s0_0) + (2505642390731/500000000000 : ℝ)*(major_s0_1) + (2505642390731/500000000000 : ℝ)*(major_s0_2) + (96224913/1000000000000 : ℝ)*(sp_s0_0) + (7495122863593/1000000000000 : ℝ)*(sp_s0_7) + (936871594241/125000000000 : ℝ)*(sp_s0_8) + (7495007375157/1000000000000 : ℝ)*(sp_s0_9) + (631831713787/250000000000 : ℝ)*(sp_s0_13) + (52989871/200000000000 : ℝ)*(sp_s0_15) + (18614777/1000000000000 : ℝ)*(sp_s0_21) + (115164063/500000000000 : ℝ)*(sp_s0_23) + (631831713787/250000000000 : ℝ)*(f.failure) + (7495237703283/1000000000000 : ℝ)*(f.sum) + (41251179393503/250000000000000000000000000 : ℝ)*base63 + (323682721658961/5000000000000000000000000000 : ℝ)*base64 + (402030799341039/5000000000000000000000000000 : ℝ)*base67 + (8639052143503/500000000000000000000000000 : ℝ)*base69 + (2554687196723931/5000000000000000000000000000 : ℝ)*base70 + (884435261658961/5000000000000000000000000000 : ℝ)*base73 + (9107563093503/500000000000000000000000000 : ℝ)*base75 + (67893246156497/500000000000000000000000000 : ℝ)*base76 + (1209936247/2500000000000000000000 : ℝ)*base79 + (2123/6250000000000000 : ℝ)*base86 + (2123/6250000000000000 : ℝ)*base88 + (2123/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5849/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5849/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (98332146527632313553/7812500000000000000000000 : ℝ) := by norm_num
    linear_combination (2766280604909/1000000000000 : ℝ)*(base40) + (1228602073259/1000000000000 : ℝ)*(base49) + (4998847/1000000000000 : ℝ)*(base59) + (5952454589/781250000 : ℝ)*(major_s0_0) + (5952454589/781250000 : ℝ)*(major_s0_1) + (5952454589/781250000 : ℝ)*(major_s0_2) + (20929669/500000000000 : ℝ)*(sp_s0_0) + (24918017/500000000000 : ℝ)*(sp_s0_6) + (395631549/1000000000000 : ℝ)*(sp_s0_8) + (11395697763433/1000000000000 : ℝ)*(sp_s0_14) + (5697671995611/500000000000 : ℝ)*(sp_s0_15) + (11395739622771/1000000000000 : ℝ)*(sp_s0_16) + (153699032963/40000000000 : ℝ)*(sp_s0_20) + (14269447/1000000000000 : ℝ)*(sp_s0_27) + (768507985911/200000000000 : ℝ)*(f.failure) + (11395739622771/1000000000000 : ℝ)*(f.sum) + (511317981747/1562500000000000000000000 : ℝ)*base62 + (590217023083/3906250000000000000000000 : ℝ)*base65 + (2815837914207/15625000000000000000000000 : ℝ)*base67 + (669118821811/1562500000000000000000000 : ℝ)*base68 + (135557023243/3906250000000000000000000 : ℝ)*base71 + (3753274351707/15625000000000000000000000 : ℝ)*base72 + (45486443121/97656250000000000000000 : ℝ)*base74 + (537336785753/3125000000000000000000000 : ℝ)*base77 + (1315289219/5000000000000000000000 : ℝ)*base79 + (5819/5000000000000000 : ℝ)*base86 + (5819/5000000000000000 : ℝ)*base88 + (5819/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35993/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (211460632901098284393/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1520719640587/500000000000 : ℝ)*(base40) + (1674076613707/1000000000000 : ℝ)*(base49) + (48154194403/200000000000 : ℝ)*(base59) + (399348446837/50000000000 : ℝ)*(major_s0_0) + (399348446837/50000000000 : ℝ)*(major_s0_1) + (399348446837/50000000000 : ℝ)*(major_s0_2) + (140229/200000000000 : ℝ)*(sp_s0_1) + (96896423/1000000000000 : ℝ)*(sp_s0_2) + (81323239/1000000000000 : ℝ)*(sp_s0_7) + (45708793/500000000000 : ℝ)*(sp_s0_20) + (11945805815999/1000000000000 : ℝ)*(sp_s0_21) + (11945886438093/1000000000000 : ℝ)*(sp_s0_22) + (2389158048563/200000000000 : ℝ)*(sp_s0_23) + (2013976838851/500000000000 : ℝ)*(sp_s0_27) + (503505636911/125000000000 : ℝ)*(f.failure) + (5972943569619/500000000000 : ℝ)*(f.sum) + (8793988178119/25000000000000000000000000 : ℝ)*base62 + (272376258467953/500000000000000000000000000 : ℝ)*base65 + (254609377932047/500000000000000000000000000 : ℝ)*base66 + (20515138548119/50000000000000000000000000 : ℝ)*base68 + (75249080386763/500000000000000000000000000 : ℝ)*base71 + (109478514082047/500000000000000000000000000 : ℝ)*base73 + (20937732458119/50000000000000000000000000 : ℝ)*base74 + (11900120103119/50000000000000000000000000 : ℝ)*base76 + (891382347/10000000000000000000000 : ℝ)*base78 + (2681/3125000000000000 : ℝ)*base87 + (2681/3125000000000000 : ℝ)*base89 + (2681/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (15737/100000 : ℝ) ^ (21/4 : ℝ) ≤ (3039556458520993/50000000000000000000 : ℝ) := by
    have hpowers : (15737/100000 : ℝ)^21 ≤ (3039556458520993/50000000000000000000 : ℝ)^4 := by
      have hnat : (15737 : ℕ)^21*50000000000000000000^4 ≤ 3039556458520993^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15737 100000 3039556458520993 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15737/100000 : ℝ)) (X := (3039556458520993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50003039556458520993/50000000000000000000 : ℝ) ≤ (10000115789777911/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50003039556458520993/50000000000000000000 : ℝ)^4 ≤ (10000115789777911/10000000000000000 : ℝ)^21 := by
      have hnat : (50003039556458520993 : ℕ)^4*10000000000000000^21 ≤ 10000115789777911^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003039556458520993 50000000000000000000 10000115789777911 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000115789777911/10000000000000000 : ℝ)) (X := (50003039556458520993/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25003039556458520993/25000000000000000000 : ℝ) ≤ (2500057893464519/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (25003039556458520993/25000000000000000000 : ℝ)^4 ≤ (2500057893464519/2500000000000000 : ℝ)^21 := by
      have hnat : (25003039556458520993 : ℕ)^4*2500000000000000^21 ≤ 2500057893464519^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003039556458520993 25000000000000000000 2500057893464519 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500057893464519/2500000000000000 : ℝ)) (X := (25003039556458520993/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(115789777911/1573700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23156816033/314740000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (15737/100000 : ℝ)) (alpha := (115789777911/1573700000000000 : ℝ)) (beta := (23156816033/314740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15737/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(115789777911/1573700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23156816033/314740000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5849/20000 : ℝ) ^ (21/4 : ℝ) ≤ (15731532611863391/10000000000000000000 : ℝ) := by
    have hpowers : (5849/20000 : ℝ)^21 ≤ (15731532611863391/10000000000000000000 : ℝ)^4 := by
      have hnat : (5849 : ℕ)^21*10000000000000000000^4 ≤ 15731532611863391^4*20000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5849 20000 15731532611863391 10000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5849/20000 : ℝ)) (X := (15731532611863391/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10015731532611863391/10000000000000000000 : ℝ) ≤ (10002994576193061/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (10015731532611863391/10000000000000000000 : ℝ)^4 ≤ (10002994576193061/10000000000000000 : ℝ)^21 := by
      have hnat : (10015731532611863391 : ℕ)^4*10000000000000000^21 ≤ 10002994576193061^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10015731532611863391 10000000000000000000 10002994576193061 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002994576193061/10000000000000000 : ℝ)) (X := (10015731532611863391/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5015731532611863391/5000000000000000000 : ℝ) ≤ (10005985347185751/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (5015731532611863391/5000000000000000000 : ℝ)^4 ≤ (10005985347185751/10000000000000000 : ℝ)^21 := by
      have hnat : (5015731532611863391 : ℕ)^4*10000000000000000^21 ≤ 10005985347185751^21*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5015731532611863391 5000000000000000000 10005985347185751 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005985347185751/10000000000000000 : ℝ)) (X := (5015731532611863391/5000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2994576193061/2924500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(299077099269/292450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (5849/20000 : ℝ)) (alpha := (2994576193061/2924500000000000 : ℝ)) (beta := (299077099269/292450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5849/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2994576193061/2924500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(299077099269/292450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35993/100000 : ℝ) ^ (21/4 : ℝ) ≤ (467891056158859351/100000000000000000000 : ℝ) := by
    have hpowers : (35993/100000 : ℝ)^21 ≤ (467891056158859351/100000000000000000000 : ℝ)^4 := by
      have hnat : (35993 : ℕ)^21*100000000000000000000^4 ≤ 467891056158859351^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35993 100000 467891056158859351 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35993/100000 : ℝ)) (X := (467891056158859351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100467891056158859351/100000000000000000000 : ℝ) ≤ (5004447689864161/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (100467891056158859351/100000000000000000000 : ℝ)^4 ≤ (5004447689864161/5000000000000000 : ℝ)^21 := by
      have hnat : (100467891056158859351 : ℕ)^4*5000000000000000^21 ≤ 5004447689864161^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100467891056158859351 100000000000000000000 5004447689864161 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004447689864161/5000000000000000 : ℝ)) (X := (100467891056158859351/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50467891056158859351/50000000000000000000 : ℝ) ≤ (2003551457279901/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50467891056158859351/50000000000000000000 : ℝ)^4 ≤ (2003551457279901/2000000000000000 : ℝ)^21 := by
      have hnat : (50467891056158859351 : ℕ)^4*2000000000000000^21 ≤ 2003551457279901^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50467891056158859351 50000000000000000000 2003551457279901 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003551457279901/2000000000000000 : ℝ)) (X := (50467891056158859351/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4447689864161/1799650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8861906671183/3599300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (35993/100000 : ℝ)) (alpha := (4447689864161/1799650000000000 : ℝ)) (beta := (8861906671183/3599300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35993/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4447689864161/1799650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8861906671183/3599300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-258015967/1250000000 : ℝ)*X 0 0+(-1128938581/2000000000 : ℝ)*X 0 1+(2180653589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4710271463/10000000000 : ℝ)*X 1 0+(1690004873/5000000000 : ℝ)*X 1 1+(2076143647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2350227869/5000000000 : ℝ)*X 2 0+(-338463681/1000000000 : ℝ)*X 2 1+(-259873223/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6104742133/10000000000 : ℝ)*X 0 0+(-674468689/2000000000 : ℝ)*X 0 1+(651400613/2500000000 : ℝ)*X 0 2+(6104742133/10000000000 : ℝ)*X 1 0+(-674468689/2000000000 : ℝ)*X 1 1+(651400613/2500000000 : ℝ)*X 1 2+(6104742133/10000000000 : ℝ)*X 2 0+(-674468689/2000000000 : ℝ)*X 2 1+(651400613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-145306428996382619408459395713545817/16565006740045000000000000000000000 : ℝ) := by norm_num
    linear_combination (127/100000000000 : ℝ)*(base13) + (431/1000000000000 : ℝ)*(base21) + (5899693083/40000000000 : ℝ)*(base39) + (26232171521/40000000000 : ℝ)*(base40) + (445021648789/1000000000000 : ℝ)*(base49) + (219/125000000000 : ℝ)*(base59) + (717/250000000000 : ℝ)*(base60) + (579/250000000000 : ℝ)*(ratio_s0_1) + (49571/25000 : ℝ)*(major_s1_0) + (49571/25000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (730990893501/250000000000 : ℝ)*(sp_s1_0) + (1461981787637/500000000000 : ℝ)*(sp_s1_1) + (2923963574843/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1461981787637/500000000000 : ℝ)*(f.sum) + (42273290978197381/65788455312500000000000000000 : ℝ)*base62 + (1264148581433/17996500000000000000000000 : ℝ)*base65 + (4531763345561/7311250000000000000000000 : ℝ)*base66 + (75797170395483/179965000000000000000000000 : ℝ)*base68 + (623926659477039059/1416054602500000000000000000000 : ℝ)*base71 + (21002297191443/39342500000000000000000000 : ℝ)*base72 + (17269894167383/29245000000000000000000000 : ℝ)*base74 + (6567495955171/15737000000000000000000000 : ℝ)*base77 + (20022431512275843/57528570625000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b017 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c324037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

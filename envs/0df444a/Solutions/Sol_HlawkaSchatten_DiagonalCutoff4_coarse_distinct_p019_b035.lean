-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:35.783305+00:00
-- url     : https://prove2.me/submissions/6db8109d-74e0-4b38-9178-861a305b1563

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
theorem collision_support_c319070_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-16782349/78125000 : ℝ)*x 0 + (-1987278381/5000000000 : ℝ)*x 1 + (-6091703077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16782349/78125000 : ℝ)^5 ≤ (7312205728639/50000000000000 : ℝ)^4 := by
    have hnat : (16782349 : ℕ)^5*50000000000000^4 ≤ 7312205728639^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16782349 78125000 7312205728639 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987278381/5000000000 : ℝ)^5 ≤ (3944762786827/12500000000000 : ℝ)^4 := by
    have hnat : (1987278381 : ℕ)^5*12500000000000^4 ≤ 3944762786827^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987278381 5000000000 3944762786827 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6091703077/10000000000 : ℝ)^5 ≤ (13454371558197/25000000000000 : ℝ)^4 := by
    have hnat : (6091703077 : ℕ)^5*25000000000000^4 ≤ 13454371558197^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6091703077 10000000000 13454371558197 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16782349/78125000 : ℝ), (-1987278381/5000000000 : ℝ), (-6091703077/10000000000 : ℝ)] ![(7312205728639/50000000000000 : ℝ), (3944762786827/12500000000000 : ℝ), (13454371558197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16782349/78125000 : ℝ)|^5 ≤ (7312205728639/50000000000000 : ℝ)^4
        have hw : |(-16782349/78125000 : ℝ)|=(16782349/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987278381/5000000000 : ℝ)|^5 ≤ (3944762786827/12500000000000 : ℝ)^4
        have hw : |(-1987278381/5000000000 : ℝ)|=(1987278381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6091703077/10000000000 : ℝ)|^5 ≤ (13454371558197/25000000000000 : ℝ)^4
        have hw : |(-6091703077/10000000000 : ℝ)|=(6091703077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319070_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6091702957/10000000000 : ℝ)*x 0 + (3974556817/10000000000 : ℝ)*x 1 + (-537035191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6091702957/10000000000 : ℝ)^5 ≤ (10763496981521/20000000000000 : ℝ)^4 := by
    have hnat : (6091702957 : ℕ)^5*20000000000000^4 ≤ 10763496981521^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6091702957 10000000000 10763496981521 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3974556817/10000000000 : ℝ)^5 ≤ (31558102840493/100000000000000 : ℝ)^4 := by
    have hnat : (3974556817 : ℕ)^5*100000000000000^4 ≤ 31558102840493^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974556817 10000000000 31558102840493 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537035191/2500000000 : ℝ)^5 ≤ (14624412240191/100000000000000 : ℝ)^4 := by
    have hnat : (537035191 : ℕ)^5*100000000000000^4 ≤ 14624412240191^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537035191 2500000000 14624412240191 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6091702957/10000000000 : ℝ), (3974556817/10000000000 : ℝ), (-537035191/2500000000 : ℝ)] ![(10763496981521/20000000000000 : ℝ), (31558102840493/100000000000000 : ℝ), (14624412240191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6091702957/10000000000 : ℝ)|^5 ≤ (10763496981521/20000000000000 : ℝ)^4
        have hw : |(6091702957/10000000000 : ℝ)|=(6091702957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3974556817/10000000000 : ℝ)|^5 ≤ (31558102840493/100000000000000 : ℝ)^4
        have hw : |(3974556817/10000000000 : ℝ)|=(3974556817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537035191/2500000000 : ℝ)|^5 ≤ (14624412240191/100000000000000 : ℝ)^4
        have hw : |(-537035191/2500000000 : ℝ)|=(537035191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319070_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3718690861/10000000000 : ℝ)*x 0 + (-4988236133/10000000000 : ℝ)*x 1 + (3718690969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3718690861/10000000000 : ℝ)^5 ≤ (29039397102903/100000000000000 : ℝ)^4 := by
    have hnat : (3718690861 : ℕ)^5*100000000000000^4 ≤ 29039397102903^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718690861 10000000000 29039397102903 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988236133/10000000000 : ℝ)^5 ≤ (41921204729991/100000000000000 : ℝ)^4 := by
    have hnat : (4988236133 : ℕ)^5*100000000000000^4 ≤ 41921204729991^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988236133 10000000000 41921204729991 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3718690969/10000000000 : ℝ)^5 ≤ (29039398157123/100000000000000 : ℝ)^4 := by
    have hnat : (3718690969 : ℕ)^5*100000000000000^4 ≤ 29039398157123^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718690969 10000000000 29039398157123 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3718690861/10000000000 : ℝ), (-4988236133/10000000000 : ℝ), (3718690969/10000000000 : ℝ)] ![(29039397102903/100000000000000 : ℝ), (41921204729991/100000000000000 : ℝ), (29039398157123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3718690861/10000000000 : ℝ)|^5 ≤ (29039397102903/100000000000000 : ℝ)^4
        have hw : |(3718690861/10000000000 : ℝ)|=(3718690861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4988236133/10000000000 : ℝ)|^5 ≤ (41921204729991/100000000000000 : ℝ)^4
        have hw : |(-4988236133/10000000000 : ℝ)|=(4988236133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3718690969/10000000000 : ℝ)|^5 ≤ (29039398157123/100000000000000 : ℝ)^4
        have hw : |(3718690969/10000000000 : ℝ)|=(3718690969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319070_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (38881209/78125000 : ℝ)*x 0 + (-1177065601/5000000000 : ℝ)*x 1 + (-4976794919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38881209/78125000 : ℝ)^5 ≤ (20900523653373/50000000000000 : ℝ)^4 := by
    have hnat : (38881209 : ℕ)^5*50000000000000^4 ≤ 20900523653373^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38881209 78125000 20900523653373 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177065601/5000000000 : ℝ)^5 ≤ (3279580723843/20000000000000 : ℝ)^4 := by
    have hnat : (1177065601 : ℕ)^5*20000000000000^4 ≤ 3279580723843^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177065601 5000000000 3279580723843 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4976794919/10000000000 : ℝ)^5 ≤ (41801049060077/100000000000000 : ℝ)^4 := by
    have hnat : (4976794919 : ℕ)^5*100000000000000^4 ≤ 41801049060077^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976794919 10000000000 41801049060077 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(38881209/78125000 : ℝ), (-1177065601/5000000000 : ℝ), (-4976794919/10000000000 : ℝ)] ![(20900523653373/50000000000000 : ℝ), (3279580723843/20000000000000 : ℝ), (41801049060077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(38881209/78125000 : ℝ)|^5 ≤ (20900523653373/50000000000000 : ℝ)^4
        have hw : |(38881209/78125000 : ℝ)|=(38881209/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1177065601/5000000000 : ℝ)|^5 ≤ (3279580723843/20000000000000 : ℝ)^4
        have hw : |(-1177065601/5000000000 : ℝ)|=(1177065601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4976794919/10000000000 : ℝ)|^5 ≤ (41801049060077/100000000000000 : ℝ)^4
        have hw : |(-4976794919/10000000000 : ℝ)|=(4976794919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319070 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-16782349/78125000 : ℝ)*X 0 0+(-1987278381/5000000000 : ℝ)*X 0 1+(-6091703077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6091702957/10000000000 : ℝ)*X 1 0+(3974556817/10000000000 : ℝ)*X 1 1+(-537035191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3718690861/10000000000 : ℝ)*X 2 0+(-4988236133/10000000000 : ℝ)*X 2 1+(3718690969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((38881209/78125000 : ℝ)*X 0 0+(-1177065601/5000000000 : ℝ)*X 0 1+(-4976794919/10000000000 : ℝ)*X 0 2+(38881209/78125000 : ℝ)*X 1 0+(-1177065601/5000000000 : ℝ)*X 1 1+(-4976794919/10000000000 : ℝ)*X 1 2+(38881209/78125000 : ℝ)*X 2 0+(-1177065601/5000000000 : ℝ)*X 2 1+(-4976794919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-10047846586793254305191555313/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25883/250000000000 : ℝ)*(base3) + (34359/1000000000000 : ℝ)*(base21) + (297696512779/500000000000 : ℝ)*(base39) + (28041/1000000000000 : ℝ)*(base40) + (69109/1000000000000 : ℝ)*(base43) + (174575809207/1000000000000 : ℝ)*(base49) + (184142380927/500000000000 : ℝ)*(base59) + (45899/1000000000000 : ℝ)*(base60) + (92547/50000 : ℝ)*(major_s0_0) + (1850939930891/1000000000000 : ℝ)*(major_s0_1) + (92547/50000 : ℝ)*(major_s0_2) + (1339712843683/500000000000 : ℝ)*(sp_s0_0) + (2679425860007/1000000000000 : ℝ)*(sp_s0_1) + (1339712826503/500000000000 : ℝ)*(sp_s0_2) + (249999974117/250000000000 : ℝ)*(sp_s0_6) + (107177030259/40000000000 : ℝ)*(f.sum) + (1546084788773123/10000000000000000000000000000 : ℝ)*base63 + (241230299/1250000000000000000000 : ℝ)*base64 + (2231944064633961/10000000000000000000000000000 : ℝ)*base67 + (5044251/80000000000000000000 : ℝ)*base68 + (2892516257/10000000000000000000000 : ℝ)*base71 + (89451719/500000000000000000000 : ℝ)*base72 + (7950411410773123/10000000000000000000000000000 : ℝ)*base75 + (1251402797/5000000000000000000000 : ℝ)*base77 + (538310248633961/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c319071_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3578490393/10000000000 : ℝ)*x 0 + (2548006439/5000000000 : ℝ)*x 1 + (1870953191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3578490393/10000000000 : ℝ)^5 ≤ (13838684998571/50000000000000 : ℝ)^4 := by
    have hnat : (3578490393 : ℕ)^5*50000000000000^4 ≤ 13838684998571^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3578490393 10000000000 13838684998571 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548006439/5000000000 : ℝ)^5 ≤ (43056442723203/100000000000000 : ℝ)^4 := by
    have hnat : (2548006439 : ℕ)^5*100000000000000^4 ≤ 43056442723203^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548006439 5000000000 43056442723203 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870953191/5000000000 : ℝ)^5 ≤ (1829136704213/6250000000000 : ℝ)^4 := by
    have hnat : (1870953191 : ℕ)^5*6250000000000^4 ≤ 1829136704213^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870953191 5000000000 1829136704213 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3578490393/10000000000 : ℝ), (2548006439/5000000000 : ℝ), (1870953191/5000000000 : ℝ)] ![(13838684998571/50000000000000 : ℝ), (43056442723203/100000000000000 : ℝ), (1829136704213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3578490393/10000000000 : ℝ)|^5 ≤ (13838684998571/50000000000000 : ℝ)^4
        have hw : |(3578490393/10000000000 : ℝ)|=(3578490393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548006439/5000000000 : ℝ)|^5 ≤ (43056442723203/100000000000000 : ℝ)^4
        have hw : |(2548006439/5000000000 : ℝ)|=(2548006439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870953191/5000000000 : ℝ)|^5 ≤ (1829136704213/6250000000000 : ℝ)^4
        have hw : |(1870953191/5000000000 : ℝ)|=(1870953191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1584050347/2500000000 : ℝ)*x 0 + (-3629968941/10000000000 : ℝ)*x 1 + (-2226365809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1584050347/2500000000 : ℝ)^5 ≤ (11306188217861/20000000000000 : ℝ)^4 := by
    have hnat : (1584050347 : ℕ)^5*20000000000000^4 ≤ 11306188217861^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584050347 2500000000 11306188217861 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3629968941/10000000000 : ℝ)^5 ≤ (28175954440683/100000000000000 : ℝ)^4 := by
    have hnat : (3629968941 : ℕ)^5*100000000000000^4 ≤ 28175954440683^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629968941 10000000000 28175954440683 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226365809/10000000000 : ℝ)^5 ≤ (3058620890067/20000000000000 : ℝ)^4 := by
    have hnat : (2226365809 : ℕ)^5*20000000000000^4 ≤ 3058620890067^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226365809 10000000000 3058620890067 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1584050347/2500000000 : ℝ), (-3629968941/10000000000 : ℝ), (-2226365809/10000000000 : ℝ)] ![(11306188217861/20000000000000 : ℝ), (28175954440683/100000000000000 : ℝ), (3058620890067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1584050347/2500000000 : ℝ)|^5 ≤ (11306188217861/20000000000000 : ℝ)^4
        have hw : |(1584050347/2500000000 : ℝ)|=(1584050347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3629968941/10000000000 : ℝ)|^5 ≤ (28175954440683/100000000000000 : ℝ)^4
        have hw : |(-3629968941/10000000000 : ℝ)|=(3629968941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226365809/10000000000 : ℝ)|^5 ≤ (3058620890067/20000000000000 : ℝ)^4
        have hw : |(-2226365809/10000000000 : ℝ)|=(2226365809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-94276089/250000000 : ℝ)*x 0 + (-2548693307/5000000000 : ℝ)*x 1 + (3547463071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94276089/250000000 : ℝ)^5 ≤ (14775661754507/50000000000000 : ℝ)^4 := by
    have hnat : (94276089 : ℕ)^5*50000000000000^4 ≤ 14775661754507^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94276089 250000000 14775661754507 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548693307/5000000000 : ℝ)^5 ≤ (8614190331771/20000000000000 : ℝ)^4 := by
    have hnat : (2548693307 : ℕ)^5*20000000000000^4 ≤ 8614190331771^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548693307 5000000000 8614190331771 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3547463071/10000000000 : ℝ)^5 ≤ (27377724817903/100000000000000 : ℝ)^4 := by
    have hnat : (3547463071 : ℕ)^5*100000000000000^4 ≤ 27377724817903^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3547463071 10000000000 27377724817903 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94276089/250000000 : ℝ), (-2548693307/5000000000 : ℝ), (3547463071/10000000000 : ℝ)] ![(14775661754507/50000000000000 : ℝ), (8614190331771/20000000000000 : ℝ), (27377724817903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94276089/250000000 : ℝ)|^5 ≤ (14775661754507/50000000000000 : ℝ)^4
        have hw : |(-94276089/250000000 : ℝ)|=(94276089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2548693307/5000000000 : ℝ)|^5 ≤ (8614190331771/20000000000000 : ℝ)^4
        have hw : |(-2548693307/5000000000 : ℝ)|=(2548693307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3547463071/10000000000 : ℝ)|^5 ≤ (27377724817903/100000000000000 : ℝ)^4
        have hw : |(3547463071/10000000000 : ℝ)|=(3547463071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3211290993/10000000000 : ℝ)*x 0 + (1167035489/2000000000 : ℝ)*x 1 + (3280415353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3211290993/10000000000 : ℝ)^5 ≤ (24174058931483/100000000000000 : ℝ)^4 := by
    have hnat : (3211290993 : ℕ)^5*100000000000000^4 ≤ 24174058931483^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3211290993 10000000000 24174058931483 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167035489/2000000000 : ℝ)^5 ≤ (12749923904199/25000000000000 : ℝ)^4 := by
    have hnat : (1167035489 : ℕ)^5*25000000000000^4 ≤ 12749923904199^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167035489 2000000000 12749923904199 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3280415353/10000000000 : ℝ)^5 ≤ (12413122723477/50000000000000 : ℝ)^4 := by
    have hnat : (3280415353 : ℕ)^5*50000000000000^4 ≤ 12413122723477^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3280415353 10000000000 12413122723477 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3211290993/10000000000 : ℝ), (1167035489/2000000000 : ℝ), (3280415353/10000000000 : ℝ)] ![(24174058931483/100000000000000 : ℝ), (12749923904199/25000000000000 : ℝ), (12413122723477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3211290993/10000000000 : ℝ)|^5 ≤ (24174058931483/100000000000000 : ℝ)^4
        have hw : |(3211290993/10000000000 : ℝ)|=(3211290993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167035489/2000000000 : ℝ)|^5 ≤ (12749923904199/25000000000000 : ℝ)^4
        have hw : |(1167035489/2000000000 : ℝ)|=(1167035489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3280415353/10000000000 : ℝ)|^5 ≤ (12413122723477/50000000000000 : ℝ)^4
        have hw : |(3280415353/10000000000 : ℝ)|=(3280415353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6460145929/10000000000 : ℝ)*x 0 + (-458781739/1250000000 : ℝ)*x 1 + (-2016879869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6460145929/10000000000 : ℝ)^5 ≤ (57916580250927/100000000000000 : ℝ)^4 := by
    have hnat : (6460145929 : ℕ)^5*100000000000000^4 ≤ 57916580250927^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6460145929 10000000000 57916580250927 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458781739/1250000000 : ℝ)^5 ≤ (28567361978949/100000000000000 : ℝ)^4 := by
    have hnat : (458781739 : ℕ)^5*100000000000000^4 ≤ 28567361978949^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458781739 1250000000 28567361978949 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016879869/10000000000 : ℝ)^5 ≤ (6758028879249/50000000000000 : ℝ)^4 := by
    have hnat : (2016879869 : ℕ)^5*50000000000000^4 ≤ 6758028879249^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016879869 10000000000 6758028879249 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6460145929/10000000000 : ℝ), (-458781739/1250000000 : ℝ), (-2016879869/10000000000 : ℝ)] ![(57916580250927/100000000000000 : ℝ), (28567361978949/100000000000000 : ℝ), (6758028879249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6460145929/10000000000 : ℝ)|^5 ≤ (57916580250927/100000000000000 : ℝ)^4
        have hw : |(6460145929/10000000000 : ℝ)|=(6460145929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458781739/1250000000 : ℝ)|^5 ≤ (28567361978949/100000000000000 : ℝ)^4
        have hw : |(-458781739/1250000000 : ℝ)|=(458781739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016879869/10000000000 : ℝ)|^5 ≤ (6758028879249/50000000000000 : ℝ)^4
        have hw : |(-2016879869/10000000000 : ℝ)|=(2016879869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-4605693/5000000000 : ℝ)*x 0 + (-1307174259/10000000000 : ℝ)*x 1 + (9364798527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4605693/5000000000 : ℝ)^5 ≤ (8023728619/50000000000000 : ℝ)^4 := by
    have hnat : (4605693 : ℕ)^5*50000000000000^4 ≤ 8023728619^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605693 5000000000 8023728619 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307174259/10000000000 : ℝ)^5 ≤ (491243567041/6250000000000 : ℝ)^4 := by
    have hnat : (1307174259 : ℕ)^5*6250000000000^4 ≤ 491243567041^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307174259 10000000000 491243567041 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9364798527/10000000000 : ℝ)^5 ≤ (5757753465829/6250000000000 : ℝ)^4 := by
    have hnat : (9364798527 : ℕ)^5*6250000000000^4 ≤ 5757753465829^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9364798527 10000000000 5757753465829 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4605693/5000000000 : ℝ), (-1307174259/10000000000 : ℝ), (9364798527/10000000000 : ℝ)] ![(8023728619/50000000000000 : ℝ), (491243567041/6250000000000 : ℝ), (5757753465829/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4605693/5000000000 : ℝ)|^5 ≤ (8023728619/50000000000000 : ℝ)^4
        have hw : |(-4605693/5000000000 : ℝ)|=(4605693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307174259/10000000000 : ℝ)|^5 ≤ (491243567041/6250000000000 : ℝ)^4
        have hw : |(-1307174259/10000000000 : ℝ)|=(1307174259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9364798527/10000000000 : ℝ)|^5 ≤ (5757753465829/6250000000000 : ℝ)^4
        have hw : |(9364798527/10000000000 : ℝ)|=(9364798527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1642188537/5000000000 : ℝ)*x 0 + (-2982393569/10000000000 : ℝ)*x 1 + (1506582843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1642188537/5000000000 : ℝ)^5 ≤ (24863729077303/100000000000000 : ℝ)^4 := by
    have hnat : (1642188537 : ℕ)^5*100000000000000^4 ≤ 24863729077303^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642188537 5000000000 24863729077303 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2982393569/10000000000 : ℝ)^5 ≤ (22039726087437/100000000000000 : ℝ)^4 := by
    have hnat : (2982393569 : ℕ)^5*100000000000000^4 ≤ 22039726087437^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982393569 10000000000 22039726087437 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506582843/2500000000 : ℝ)^5 ≤ (26548272406867/50000000000000 : ℝ)^4 := by
    have hnat : (1506582843 : ℕ)^5*50000000000000^4 ≤ 26548272406867^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506582843 2500000000 26548272406867 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1642188537/5000000000 : ℝ), (-2982393569/10000000000 : ℝ), (1506582843/2500000000 : ℝ)] ![(24863729077303/100000000000000 : ℝ), (22039726087437/100000000000000 : ℝ), (26548272406867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1642188537/5000000000 : ℝ)|^5 ≤ (24863729077303/100000000000000 : ℝ)^4
        have hw : |(-1642188537/5000000000 : ℝ)|=(1642188537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2982393569/10000000000 : ℝ)|^5 ≤ (22039726087437/100000000000000 : ℝ)^4
        have hw : |(-2982393569/10000000000 : ℝ)|=(2982393569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506582843/2500000000 : ℝ)|^5 ≤ (26548272406867/50000000000000 : ℝ)^4
        have hw : |(1506582843/2500000000 : ℝ)|=(1506582843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5452578787/10000000000 : ℝ)*x 0 + (55496751/125000000 : ℝ)*x 1 + (301519171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5452578787/10000000000 : ℝ)^5 ≤ (11713655459101/25000000000000 : ℝ)^4 := by
    have hnat : (5452578787 : ℕ)^5*25000000000000^4 ≤ 11713655459101^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452578787 10000000000 11713655459101 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55496751/125000000 : ℝ)^5 ≤ (36240729565957/100000000000000 : ℝ)^4 := by
    have hnat : (55496751 : ℕ)^5*100000000000000^4 ≤ 36240729565957^4*125000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55496751 125000000 36240729565957 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301519171/1250000000 : ℝ)^5 ≤ (3380929714467/20000000000000 : ℝ)^4 := by
    have hnat : (301519171 : ℕ)^5*20000000000000^4 ≤ 3380929714467^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301519171 1250000000 3380929714467 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5452578787/10000000000 : ℝ), (55496751/125000000 : ℝ), (301519171/1250000000 : ℝ)] ![(11713655459101/25000000000000 : ℝ), (36240729565957/100000000000000 : ℝ), (3380929714467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5452578787/10000000000 : ℝ)|^5 ≤ (11713655459101/25000000000000 : ℝ)^4
        have hw : |(5452578787/10000000000 : ℝ)|=(5452578787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55496751/125000000 : ℝ)|^5 ≤ (36240729565957/100000000000000 : ℝ)^4
        have hw : |(55496751/125000000 : ℝ)|=(55496751/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301519171/1250000000 : ℝ)|^5 ≤ (3380929714467/20000000000000 : ℝ)^4
        have hw : |(301519171/1250000000 : ℝ)|=(301519171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7865196683/10000000000 : ℝ)*x 0 + (-134797963/500000000 : ℝ)*x 1 + (-1123501083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7865196683/10000000000 : ℝ)^5 ≤ (74069085773361/100000000000000 : ℝ)^4 := by
    have hnat : (7865196683 : ℕ)^5*100000000000000^4 ≤ 74069085773361^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7865196683 10000000000 74069085773361 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134797963/500000000 : ℝ)^5 ≤ (4856592501861/25000000000000 : ℝ)^4 := by
    have hnat : (134797963 : ℕ)^5*25000000000000^4 ≤ 4856592501861^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134797963 500000000 4856592501861 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123501083/10000000000 : ℝ)^5 ≤ (3252272100511/50000000000000 : ℝ)^4 := by
    have hnat : (1123501083 : ℕ)^5*50000000000000^4 ≤ 3252272100511^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123501083 10000000000 3252272100511 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7865196683/10000000000 : ℝ), (-134797963/500000000 : ℝ), (-1123501083/10000000000 : ℝ)] ![(74069085773361/100000000000000 : ℝ), (4856592501861/25000000000000 : ℝ), (3252272100511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7865196683/10000000000 : ℝ)|^5 ≤ (74069085773361/100000000000000 : ℝ)^4
        have hw : |(7865196683/10000000000 : ℝ)|=(7865196683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134797963/500000000 : ℝ)|^5 ≤ (4856592501861/25000000000000 : ℝ)^4
        have hw : |(-134797963/500000000 : ℝ)|=(134797963/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123501083/10000000000 : ℝ)|^5 ≤ (3252272100511/50000000000000 : ℝ)^4
        have hw : |(-1123501083/10000000000 : ℝ)|=(1123501083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-79257/2500000000 : ℝ)*x 0 + (-1710570313/10000000000 : ℝ)*x 1 + (9109777427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79257/2500000000 : ℝ)^5 ≤ (118943861/50000000000000 : ℝ)^4 := by
    have hnat : (79257 : ℕ)^5*50000000000000^4 ≤ 118943861^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79257 2500000000 118943861 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1710570313/10000000000 : ℝ)^5 ≤ (5500423989633/50000000000000 : ℝ)^4 := by
    have hnat : (1710570313 : ℕ)^5*50000000000000^4 ≤ 5500423989633^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710570313 10000000000 5500423989633 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9109777427/10000000000 : ℝ)^5 ≤ (44499457062191/50000000000000 : ℝ)^4 := by
    have hnat : (9109777427 : ℕ)^5*50000000000000^4 ≤ 44499457062191^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9109777427 10000000000 44499457062191 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79257/2500000000 : ℝ), (-1710570313/10000000000 : ℝ), (9109777427/10000000000 : ℝ)] ![(118943861/50000000000000 : ℝ), (5500423989633/50000000000000 : ℝ), (44499457062191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79257/2500000000 : ℝ)|^5 ≤ (118943861/50000000000000 : ℝ)^4
        have hw : |(-79257/2500000000 : ℝ)|=(79257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1710570313/10000000000 : ℝ)|^5 ≤ (5500423989633/50000000000000 : ℝ)^4
        have hw : |(-1710570313/10000000000 : ℝ)|=(1710570313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9109777427/10000000000 : ℝ)|^5 ≤ (44499457062191/50000000000000 : ℝ)^4
        have hw : |(9109777427/10000000000 : ℝ)|=(9109777427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-135301011/400000000 : ℝ)*x 0 + (-2168218337/5000000000 : ℝ)*x 1 + (2354773367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135301011/400000000 : ℝ)^5 ≤ (25795937322137/100000000000000 : ℝ)^4 := by
    have hnat : (135301011 : ℕ)^5*100000000000000^4 ≤ 25795937322137^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135301011 400000000 25795937322137 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168218337/5000000000 : ℝ)^5 ≤ (17594878215409/50000000000000 : ℝ)^4 := by
    have hnat : (2168218337 : ℕ)^5*50000000000000^4 ≤ 17594878215409^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168218337 5000000000 17594878215409 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354773367/5000000000 : ℝ)^5 ≤ (39014306237507/100000000000000 : ℝ)^4 := by
    have hnat : (2354773367 : ℕ)^5*100000000000000^4 ≤ 39014306237507^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354773367 5000000000 39014306237507 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135301011/400000000 : ℝ), (-2168218337/5000000000 : ℝ), (2354773367/5000000000 : ℝ)] ![(25795937322137/100000000000000 : ℝ), (17594878215409/50000000000000 : ℝ), (39014306237507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135301011/400000000 : ℝ)|^5 ≤ (25795937322137/100000000000000 : ℝ)^4
        have hw : |(-135301011/400000000 : ℝ)|=(135301011/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168218337/5000000000 : ℝ)|^5 ≤ (17594878215409/50000000000000 : ℝ)^4
        have hw : |(-2168218337/5000000000 : ℝ)|=(2168218337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2354773367/5000000000 : ℝ)|^5 ≤ (39014306237507/100000000000000 : ℝ)^4
        have hw : |(2354773367/5000000000 : ℝ)|=(2354773367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (367881483/1250000000 : ℝ)*x 0 + (2785479271/5000000000 : ℝ)*x 1 + (479557243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367881483/1250000000 : ℝ)^5 ≤ (21676910995399/100000000000000 : ℝ)^4 := by
    have hnat : (367881483 : ℕ)^5*100000000000000^4 ≤ 21676910995399^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367881483 1250000000 21676910995399 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785479271/5000000000 : ℝ)^5 ≤ (48129617271971/100000000000000 : ℝ)^4 := by
    have hnat : (2785479271 : ℕ)^5*100000000000000^4 ≤ 48129617271971^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785479271 5000000000 48129617271971 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479557243/1250000000 : ℝ)^5 ≤ (754836793053/2500000000000 : ℝ)^4 := by
    have hnat : (479557243 : ℕ)^5*2500000000000^4 ≤ 754836793053^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479557243 1250000000 754836793053 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(367881483/1250000000 : ℝ), (2785479271/5000000000 : ℝ), (479557243/1250000000 : ℝ)] ![(21676910995399/100000000000000 : ℝ), (48129617271971/100000000000000 : ℝ), (754836793053/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(367881483/1250000000 : ℝ)|^5 ≤ (21676910995399/100000000000000 : ℝ)^4
        have hw : |(367881483/1250000000 : ℝ)|=(367881483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785479271/5000000000 : ℝ)|^5 ≤ (48129617271971/100000000000000 : ℝ)^4
        have hw : |(2785479271/5000000000 : ℝ)|=(2785479271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(479557243/1250000000 : ℝ)|^5 ≤ (754836793053/2500000000000 : ℝ)^4
        have hw : |(479557243/1250000000 : ℝ)|=(479557243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1438702869/2000000000 : ℝ)*x 0 + (-730923351/2500000000 : ℝ)*x 1 + (-1864589191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1438702869/2000000000 : ℝ)^5 ≤ (66248552333879/100000000000000 : ℝ)^4 := by
    have hnat : (1438702869 : ℕ)^5*100000000000000^4 ≤ 66248552333879^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438702869 2000000000 66248552333879 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730923351/2500000000 : ℝ)^5 ≤ (21498827988639/100000000000000 : ℝ)^4 := by
    have hnat : (730923351 : ℕ)^5*100000000000000^4 ≤ 21498827988639^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730923351 2500000000 21498827988639 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864589191/10000000000 : ℝ)^5 ≤ (6126309834343/50000000000000 : ℝ)^4 := by
    have hnat : (1864589191 : ℕ)^5*50000000000000^4 ≤ 6126309834343^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864589191 10000000000 6126309834343 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1438702869/2000000000 : ℝ), (-730923351/2500000000 : ℝ), (-1864589191/10000000000 : ℝ)] ![(66248552333879/100000000000000 : ℝ), (21498827988639/100000000000000 : ℝ), (6126309834343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1438702869/2000000000 : ℝ)|^5 ≤ (66248552333879/100000000000000 : ℝ)^4
        have hw : |(1438702869/2000000000 : ℝ)|=(1438702869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-730923351/2500000000 : ℝ)|^5 ≤ (21498827988639/100000000000000 : ℝ)^4
        have hw : |(-730923351/2500000000 : ℝ)|=(730923351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864589191/10000000000 : ℝ)|^5 ≤ (6126309834343/50000000000000 : ℝ)^4
        have hw : |(-1864589191/10000000000 : ℝ)|=(1864589191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727750481/5000000000 : ℝ)*x 0 + (-1910258337/5000000000 : ℝ)*x 1 + (5135114869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727750481/5000000000 : ℝ)^5 ≤ (26493465652301/100000000000000 : ℝ)^4 := by
    have hnat : (1727750481 : ℕ)^5*100000000000000^4 ≤ 26493465652301^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727750481 5000000000 26493465652301 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1910258337/5000000000 : ℝ)^5 ≤ (15018364086773/50000000000000 : ℝ)^4 := by
    have hnat : (1910258337 : ℕ)^5*50000000000000^4 ≤ 15018364086773^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910258337 5000000000 15018364086773 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135114869/10000000000 : ℝ)^5 ≤ (43469806164507/100000000000000 : ℝ)^4 := by
    have hnat : (5135114869 : ℕ)^5*100000000000000^4 ≤ 43469806164507^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135114869 10000000000 43469806164507 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727750481/5000000000 : ℝ), (-1910258337/5000000000 : ℝ), (5135114869/10000000000 : ℝ)] ![(26493465652301/100000000000000 : ℝ), (15018364086773/50000000000000 : ℝ), (43469806164507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727750481/5000000000 : ℝ)|^5 ≤ (26493465652301/100000000000000 : ℝ)^4
        have hw : |(-1727750481/5000000000 : ℝ)|=(1727750481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1910258337/5000000000 : ℝ)|^5 ≤ (15018364086773/50000000000000 : ℝ)^4
        have hw : |(-1910258337/5000000000 : ℝ)|=(1910258337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135114869/10000000000 : ℝ)|^5 ≤ (43469806164507/100000000000000 : ℝ)^4
        have hw : |(5135114869/10000000000 : ℝ)|=(5135114869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (843692669/2000000000 : ℝ)*x 0 + (4677519341/10000000000 : ℝ)*x 1 + (885366459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843692669/2000000000 : ℝ)^5 ≤ (4249647060559/12500000000000 : ℝ)^4 := by
    have hnat : (843692669 : ℕ)^5*12500000000000^4 ≤ 4249647060559^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843692669 2000000000 4249647060559 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4677519341/10000000000 : ℝ)^5 ≤ (38682941406097/100000000000000 : ℝ)^4 := by
    have hnat : (4677519341 : ℕ)^5*100000000000000^4 ≤ 38682941406097^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677519341 10000000000 38682941406097 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885366459/2500000000 : ℝ)^5 ≤ (13659941047657/50000000000000 : ℝ)^4 := by
    have hnat : (885366459 : ℕ)^5*50000000000000^4 ≤ 13659941047657^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885366459 2500000000 13659941047657 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843692669/2000000000 : ℝ), (4677519341/10000000000 : ℝ), (885366459/2500000000 : ℝ)] ![(4249647060559/12500000000000 : ℝ), (38682941406097/100000000000000 : ℝ), (13659941047657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843692669/2000000000 : ℝ)|^5 ≤ (4249647060559/12500000000000 : ℝ)^4
        have hw : |(843692669/2000000000 : ℝ)|=(843692669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4677519341/10000000000 : ℝ)|^5 ≤ (38682941406097/100000000000000 : ℝ)^4
        have hw : |(4677519341/10000000000 : ℝ)|=(4677519341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(885366459/2500000000 : ℝ)|^5 ≤ (13659941047657/50000000000000 : ℝ)^4
        have hw : |(885366459/2500000000 : ℝ)|=(885366459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5084732963/10000000000 : ℝ)*x 0 + (-837328311/2000000000 : ℝ)*x 1 + (-3127238327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5084732963/10000000000 : ℝ)^5 ≤ (2146867253233/5000000000000 : ℝ)^4 := by
    have hnat : (5084732963 : ℕ)^5*5000000000000^4 ≤ 2146867253233^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084732963 10000000000 2146867253233 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837328311/2000000000 : ℝ)^5 ≤ (33676909102647/100000000000000 : ℝ)^4 := by
    have hnat : (837328311 : ℕ)^5*100000000000000^4 ≤ 33676909102647^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837328311 2000000000 33676909102647 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3127238327/10000000000 : ℝ)^5 ≤ (2923218228301/12500000000000 : ℝ)^4 := by
    have hnat : (3127238327 : ℕ)^5*12500000000000^4 ≤ 2923218228301^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127238327 10000000000 2923218228301 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5084732963/10000000000 : ℝ), (-837328311/2000000000 : ℝ), (-3127238327/10000000000 : ℝ)] ![(2146867253233/5000000000000 : ℝ), (33676909102647/100000000000000 : ℝ), (2923218228301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5084732963/10000000000 : ℝ)|^5 ≤ (2146867253233/5000000000000 : ℝ)^4
        have hw : |(5084732963/10000000000 : ℝ)|=(5084732963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837328311/2000000000 : ℝ)|^5 ≤ (33676909102647/100000000000000 : ℝ)^4
        have hw : |(-837328311/2000000000 : ℝ)|=(837328311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3127238327/10000000000 : ℝ)|^5 ≤ (2923218228301/12500000000000 : ℝ)^4
        have hw : |(-3127238327/10000000000 : ℝ)|=(3127238327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s1_5 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-37/1000000000 : ℝ)*x 0 + (-37/1000000000 : ℝ)*x 1 + (9999999991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37/1000000000 : ℝ)^5 ≤ (12829/25000000000000 : ℝ)^4 := by
    have hnat : (37 : ℕ)^5*25000000000000^4 ≤ 12829^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37 1000000000 12829 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37/1000000000 : ℝ)^5 ≤ (12829/25000000000000 : ℝ)^4 := by
    have hnat : (37 : ℕ)^5*25000000000000^4 ≤ 12829^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37 1000000000 12829 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999991/10000000000 : ℝ)^5 ≤ (99999999887501/100000000000000 : ℝ)^4 := by
    have hnat : (9999999991 : ℕ)^5*100000000000000^4 ≤ 99999999887501^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999991 10000000000 99999999887501 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37/1000000000 : ℝ), (-37/1000000000 : ℝ), (9999999991/10000000000 : ℝ)] ![(12829/25000000000000 : ℝ), (12829/25000000000000 : ℝ), (99999999887501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37/1000000000 : ℝ)|^5 ≤ (12829/25000000000000 : ℝ)^4
        have hw : |(-37/1000000000 : ℝ)|=(37/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37/1000000000 : ℝ)|^5 ≤ (12829/25000000000000 : ℝ)^4
        have hw : |(-37/1000000000 : ℝ)|=(37/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999991/10000000000 : ℝ)|^5 ≤ (99999999887501/100000000000000 : ℝ)^4
        have hw : |(9999999991/10000000000 : ℝ)|=(9999999991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319071_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1540823109/5000000000 : ℝ)*x 0 + (-1598802971/5000000000 : ℝ)*x 1 + (1504261429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540823109/5000000000 : ℝ)^5 ≤ (5740087099403/25000000000000 : ℝ)^4 := by
    have hnat : (1540823109 : ℕ)^5*25000000000000^4 ≤ 5740087099403^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540823109 5000000000 5740087099403 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1598802971/5000000000 : ℝ)^5 ≤ (961814165849/4000000000000 : ℝ)^4 := by
    have hnat : (1598802971 : ℕ)^5*4000000000000^4 ≤ 961814165849^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598802971 5000000000 961814165849 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504261429/2500000000 : ℝ)^5 ≤ (5299429743859/10000000000000 : ℝ)^4 := by
    have hnat : (1504261429 : ℕ)^5*10000000000000^4 ≤ 5299429743859^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504261429 2500000000 5299429743859 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1540823109/5000000000 : ℝ), (-1598802971/5000000000 : ℝ), (1504261429/2500000000 : ℝ)] ![(5740087099403/25000000000000 : ℝ), (961814165849/4000000000000 : ℝ), (5299429743859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1540823109/5000000000 : ℝ)|^5 ≤ (5740087099403/25000000000000 : ℝ)^4
        have hw : |(1540823109/5000000000 : ℝ)|=(1540823109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1598802971/5000000000 : ℝ)|^5 ≤ (961814165849/4000000000000 : ℝ)^4
        have hw : |(-1598802971/5000000000 : ℝ)|=(1598802971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1504261429/2500000000 : ℝ)|^5 ≤ (5299429743859/10000000000000 : ℝ)^4
        have hw : |(1504261429/2500000000 : ℝ)|=(1504261429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319071 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3578490393/10000000000 : ℝ)*X 1 0+(2548006439/5000000000 : ℝ)*X 1 1+(1870953191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1584050347/2500000000 : ℝ)*X 2 0+(-3629968941/10000000000 : ℝ)*X 2 1+(-2226365809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-94276089/250000000 : ℝ)*X 0 0+(-2548693307/5000000000 : ℝ)*X 0 1+(3547463071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3211290993/10000000000 : ℝ)*X 1 0+(1167035489/2000000000 : ℝ)*X 1 1+(3280415353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((6460145929/10000000000 : ℝ)*X 2 0+(-458781739/1250000000 : ℝ)*X 2 1+(-2016879869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-4605693/5000000000 : ℝ)*X 0 0+(-1307174259/10000000000 : ℝ)*X 0 1+(9364798527/10000000000 : ℝ)*X 0 2+(-4605693/5000000000 : ℝ)*X 1 0+(-1307174259/10000000000 : ℝ)*X 1 1+(9364798527/10000000000 : ℝ)*X 1 2+(-4605693/5000000000 : ℝ)*X 2 0+(-1307174259/10000000000 : ℝ)*X 2 1+(9364798527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1642188537/5000000000 : ℝ)*X 0 0+(-2982393569/10000000000 : ℝ)*X 0 1+(1506582843/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5452578787/10000000000 : ℝ)*X 1 0+(55496751/125000000 : ℝ)*X 1 1+(301519171/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7865196683/10000000000 : ℝ)*X 2 0+(-134797963/500000000 : ℝ)*X 2 1+(-1123501083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-79257/2500000000 : ℝ)*X 0 0+(-1710570313/10000000000 : ℝ)*X 0 1+(9109777427/10000000000 : ℝ)*X 0 2+(-79257/2500000000 : ℝ)*X 1 0+(-1710570313/10000000000 : ℝ)*X 1 1+(9109777427/10000000000 : ℝ)*X 1 2+(-79257/2500000000 : ℝ)*X 2 0+(-1710570313/10000000000 : ℝ)*X 2 1+(9109777427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-135301011/400000000 : ℝ)*X 0 0+(-2168218337/5000000000 : ℝ)*X 0 1+(2354773367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((367881483/1250000000 : ℝ)*X 1 0+(2785479271/5000000000 : ℝ)*X 1 1+(479557243/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1438702869/2000000000 : ℝ)*X 2 0+(-730923351/2500000000 : ℝ)*X 2 1+(-1864589191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((7997/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7997/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10122219818107749/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (32820437369/250000000000 : ℝ)*(base1) + (279291752799/500000000000 : ℝ)*(base7) + (19369403293/40000000000 : ℝ)*(base54) + (870457579867/1000000000000 : ℝ)*(base60) + (575040381571/200000000000 : ℝ)*(major_s0_0) + (575040381571/200000000000 : ℝ)*(major_s0_1) + (239096682553/100000000000 : ℝ)*(major_s0_2) + (927256543/500000000000 : ℝ)*(sp_s0_2) + (160443548269/40000000000 : ℝ)*(sp_s0_7) + (3879703047957/1000000000000 : ℝ)*(sp_s0_8) + (3393702387941/1000000000000 : ℝ)*(sp_s0_9) + (1496440585353/1000000000000 : ℝ)*(sp_s0_13) + (25977323/250000000000 : ℝ)*(sp_s0_22) + (14973897/1000000000000 : ℝ)*(sp_s0_23) + (388343477889/250000000000 : ℝ)*(f.failure) + (3879806957249/1000000000000 : ℝ)*(f.sum) + (765212691309889/2000000000000000000000000000 : ℝ)*base63 + (418277259195009/1000000000000000000000000000 : ℝ)*base65 + (634404020468241/2000000000000000000000000000 : ℝ)*base66 + (138404207540637/1000000000000000000000000000 : ℝ)*base68 + (199460256678223/2000000000000000000000000000 : ℝ)*base70 + (256113488591163/2000000000000000000000000000 : ℝ)*base72 + (524667164208837/2000000000000000000000000000 : ℝ)*base74 + (597409667331759/2000000000000000000000000000 : ℝ)*base77 + (57571152985149/500000000000000000000000000 : ℝ)*base79 + (5783/12500000000000000 : ℝ)*base87 + (5783/12500000000000000 : ℝ)*base89 + (5783/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-69347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-69347/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20408644226528964028497/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166329517311/250000000000 : ℝ)*(base1) + (1243254814497/1000000000000 : ℝ)*(base7) + (8653013211/40000000000 : ℝ)*(base40) + (505206729299/1000000000000 : ℝ)*(base60) + (563050757369/250000000000 : ℝ)*(major_s0_0) + (563050757369/250000000000 : ℝ)*(major_s0_1) + (563050757369/250000000000 : ℝ)*(major_s0_2) + (9773279/200000000000 : ℝ)*(sp_s0_1) + (78058127/200000000000 : ℝ)*(sp_s0_13) + (3246885494019/1000000000000 : ℝ)*(sp_s0_14) + (2581518558379/1000000000000 : ℝ)*(sp_s0_15) + (322694628529/125000000000 : ℝ)*(sp_s0_16) + (1794335237331/1000000000000 : ℝ)*(sp_s0_20) + (10396543/1000000000000 : ℝ)*(sp_s0_23) + (608394391357/500000000000 : ℝ)*(f.failure) + (103262696991/40000000000 : ℝ)*(f.sum) + (34057743753289/625000000000000000000000000 : ℝ)*base63 + (976623186128657/2500000000000000000000000000 : ℝ)*base65 + (107684325134499/2500000000000000000000000000 : ℝ)*base66 + (65388969865501/2500000000000000000000000000 : ℝ)*base68 + (666764069122079/1250000000000000000000000000 : ℝ)*base71 + (364766197621343/2500000000000000000000000000 : ℝ)*base73 + (1281677886871343/2500000000000000000000000000 : ℝ)*base74 + (1130699627365501/2500000000000000000000000000 : ℝ)*base77 + (135516179434211/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (16279/25000000000000000 : ℝ)*base87 + (16279/25000000000000000 : ℝ)*base89 + (16279/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1699/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1699/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23840640761405337/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (2847894572319/1000000000000 : ℝ)*(base1) + (1145666317071/1000000000000 : ℝ)*(base7) + (1521411425877/1000000000000 : ℝ)*(base40) + (513766940787/1000000000000 : ℝ)*(base60) + (3150722366769/1000000000000 : ℝ)*(major_s0_0) + (3150722366769/1000000000000 : ℝ)*(major_s0_1) + (3150722366769/1000000000000 : ℝ)*(major_s0_2) + (1836007/500000000000 : ℝ)*(sp_s0_7) + (14461483/500000000000 : ℝ)*(sp_s0_8) + (1550093/500000000000 : ℝ)*(sp_s0_9) + (420677/125000000000 : ℝ)*(sp_s0_16) + (27185927551/4000000000 : ℝ)*(sp_s0_21) + (1974281032239/500000000000 : ℝ)*(sp_s0_22) + (1974292260921/500000000000 : ℝ)*(sp_s0_23) + (106389265953/62500000000 : ℝ)*(f.failure) + (987147746861/250000000000 : ℝ)*(f.sum) + (1046668069254689/2500000000000000000000000000 : ℝ)*base63 + (6529459881736857/10000000000000000000000000000 : ℝ)*base65 + (6912068895281899/10000000000000000000000000000 : ℝ)*base66 + (2188966828718101/10000000000000000000000000000 : ℝ)*base68 + (1865121280772521/5000000000000000000000000000 : ℝ)*base70 + (1052106015736857/10000000000000000000000000000 : ℝ)*base72 + (2451885626263143/10000000000000000000000000000 : ℝ)*base74 + (488944558718101/10000000000000000000000000000 : ℝ)*base77 + (599762449245311/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (417/1562500000000000 : ℝ)*base86 + (417/1562500000000000 : ℝ)*base88 + (417/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (7997/20000 : ℝ) ^ (79/16 : ℝ) ≤ (1082348034931433291/100000000000000000000 : ℝ) := by
    have hpowers : (7997/20000 : ℝ)^79 ≤ (1082348034931433291/100000000000000000000 : ℝ)^16 := by
      have hnat : (7997 : ℕ)^79*100000000000000000000^16 ≤ 1082348034931433291^16*20000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7997 20000 1082348034931433291 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7997/20000 : ℝ)) (X := (1082348034931433291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101082348034931433291/100000000000000000000 : ℝ) ≤ (2004365395519993/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (101082348034931433291/100000000000000000000 : ℝ)^16 ≤ (2004365395519993/2000000000000000 : ℝ)^79 := by
      have hnat : (101082348034931433291 : ℕ)^16*2000000000000000^79 ≤ 2004365395519993^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101082348034931433291 100000000000000000000 2004365395519993 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004365395519993/2000000000000000 : ℝ)) (X := (101082348034931433291/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51082348034931433291/50000000000000000000 : ℝ) ≤ (5021734182008769/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (51082348034931433291/50000000000000000000 : ℝ)^16 ≤ (5021734182008769/5000000000000000 : ℝ)^79 := by
      have hnat : (51082348034931433291 : ℕ)^16*5000000000000000^79 ≤ 5021734182008769^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51082348034931433291 50000000000000000000 5021734182008769 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021734182008769/5000000000000000 : ℝ)) (X := (51082348034931433291/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4365395519993/799700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(21641386417573/3998500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (7997/20000 : ℝ)) (alpha := (4365395519993/799700000000000 : ℝ)) (beta := (21641386417573/3998500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7997/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4365395519993/799700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(21641386417573/3998500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (69347/100000 : ℝ) ^ (79/16 : ℝ) ≤ (1640869942937753721/10000000000000000000 : ℝ) := by
    have hpowers : (69347/100000 : ℝ)^79 ≤ (1640869942937753721/10000000000000000000 : ℝ)^16 := by
      have hnat : (69347 : ℕ)^79*10000000000000000000^16 ≤ 1640869942937753721^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69347 100000 1640869942937753721 10000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69347/100000 : ℝ)) (X := (1640869942937753721/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (11640869942937753721/10000000000000000000 : ℝ) ≤ (5156252108674573/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (11640869942937753721/10000000000000000000 : ℝ)^16 ≤ (5156252108674573/5000000000000000 : ℝ)^79 := by
      have hnat : (11640869942937753721 : ℕ)^16*5000000000000000^79 ≤ 5156252108674573^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11640869942937753721 10000000000000000000 5156252108674573 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5156252108674573/5000000000000000 : ℝ)) (X := (11640869942937753721/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6640869942937753721/5000000000000000000 : ℝ) ≤ (2647908908280407/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (6640869942937753721/5000000000000000000 : ℝ)^16 ≤ (2647908908280407/2500000000000000 : ℝ)^79 := by
      have hnat : (6640869942937753721 : ℕ)^16*2500000000000000^79 ≤ 2647908908280407^79*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6640869942937753721 5000000000000000000 2647908908280407 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2647908908280407/2500000000000000 : ℝ)) (X := (6640869942937753721/5000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(156252108674573/3467350000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(139565707886241/3467350000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (69347/100000 : ℝ)) (alpha := (156252108674573/3467350000000000 : ℝ)) (beta := (139565707886241/3467350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (69347/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(156252108674573/3467350000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(139565707886241/3467350000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1699/4000 : ℝ) ^ (79/16 : ℝ) ≤ (729253639633011337/50000000000000000000 : ℝ) := by
    have hpowers : (1699/4000 : ℝ)^79 ≤ (729253639633011337/50000000000000000000 : ℝ)^16 := by
      have hnat : (1699 : ℕ)^79*50000000000000000000^16 ≤ 729253639633011337^16*4000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1699 4000 729253639633011337 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1699/4000 : ℝ)) (X := (729253639633011337/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50729253639633011337/50000000000000000000 : ℝ) ≤ (10029369085712107/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50729253639633011337/50000000000000000000 : ℝ)^16 ≤ (10029369085712107/10000000000000000 : ℝ)^79 := by
      have hnat : (50729253639633011337 : ℕ)^16*10000000000000000^79 ≤ 10029369085712107^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50729253639633011337 50000000000000000000 10029369085712107 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029369085712107/10000000000000000 : ℝ)) (X := (50729253639633011337/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25729253639633011337/25000000000000000000 : ℝ) ≤ (10058403392708713/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25729253639633011337/25000000000000000000 : ℝ)^16 ≤ (10058403392708713/10000000000000000 : ℝ)^79 := by
      have hnat : (25729253639633011337 : ℕ)^16*10000000000000000^79 ≤ 10058403392708713^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25729253639633011337 25000000000000000000 10058403392708713 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058403392708713/10000000000000000 : ℝ)) (X := (25729253639633011337/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(29369085712107/4247500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(14517153498303/2123750000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1699/4000 : ℝ)) (alpha := (29369085712107/4247500000000000 : ℝ)) (beta := (14517153498303/2123750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1699/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(29369085712107/4247500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(14517153498303/2123750000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1727750481/5000000000 : ℝ)*X 0 0+(-1910258337/5000000000 : ℝ)*X 0 1+(5135114869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((843692669/2000000000 : ℝ)*X 1 0+(4677519341/10000000000 : ℝ)*X 1 1+(885366459/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5084732963/10000000000 : ℝ)*X 2 0+(-837328311/2000000000 : ℝ)*X 2 1+(-3127238327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_5 : ((-37/1000000000 : ℝ)*X 0 0+(-37/1000000000 : ℝ)*X 0 1+(9999999991/10000000000 : ℝ)*X 0 2+(-37/1000000000 : ℝ)*X 1 0+(-37/1000000000 : ℝ)*X 1 1+(9999999991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s1_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1540823109/5000000000 : ℝ)*X 0 0+(-1598802971/5000000000 : ℝ)*X 0 1+(1504261429/2500000000 : ℝ)*X 0 2+(1540823109/5000000000 : ℝ)*X 1 0+(-1598802971/5000000000 : ℝ)*X 1 1+(1504261429/2500000000 : ℝ)*X 1 2+(1540823109/5000000000 : ℝ)*X 2 0+(-1598802971/5000000000 : ℝ)*X 2 1+(1504261429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-33761134812451215258932757690927/4245907187500000000000000000000 : ℝ) := by norm_num
    linear_combination (20132242283/62500000000 : ℝ)*(base1) + (351/2500000000 : ℝ)*(base15) + (258431/500000000000 : ℝ)*(base17) + (100871/250000000000 : ℝ)*(base39) + (514412578637/1000000000000 : ℝ)*(base40) + (54959130081/250000000000 : ℝ)*(base49) + (511144767373/1000000000000 : ℝ)*(base60) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (462736387103/250000000000 : ℝ)*(major_s1_2) + (743150118581/250000000000 : ℝ)*(sp_s1_0) + (1325241970267/500000000000 : ℝ)*(sp_s1_1) + (662621149449/250000000000 : ℝ)*(sp_s1_2) + (1387103/250000000000 : ℝ)*(sp_s1_5) + (42367757717/62500000000 : ℝ)*(sp_s1_6) + (662621149449/250000000000 : ℝ)*(f.sum) + (9934962369265167713/73637845625000000000000000000000 : ℝ)*base63 + (305132918256209/530937500000000000000000000 : ℝ)*base64 + (476455067357/3467350000000000000000000 : ℝ)*base67 + (222450888262177/530937500000000000000000000 : ℝ)*base69 + (2952476753619957371/8491814375000000000000000000000 : ℝ)*base70 + (2386235755999/19992500000000000000000000 : ℝ)*base72 + (30682831639017/173367500000000000000000000 : ℝ)*base74 + (6349940604553/19992500000000000000000000 : ℝ)*base76 + (56400251856880747/277283979500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p019_b035 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c319070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c319071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

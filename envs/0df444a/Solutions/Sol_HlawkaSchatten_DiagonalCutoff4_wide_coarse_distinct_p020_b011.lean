-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:07.484796+00:00
-- url     : https://prove2.me/submissions/d1d74e69-0da2-4e50-a26b-6c0be7c22ed2

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
theorem collision_support_c320023_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-637278949/2000000000 : ℝ)*x 0 + (5503497319/10000000000 : ℝ)*x 1 + (3613642273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (637278949/2000000000 : ℝ)^41 ≤ (965933759049/4000000000000 : ℝ)^33 := by
    have hnat : (637278949 : ℕ)^41*4000000000000^33 ≤ 965933759049^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637278949 2000000000 965933759049 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503497319/10000000000 : ℝ)^41 ≤ (11904284996247/25000000000000 : ℝ)^33 := by
    have hnat : (5503497319 : ℕ)^41*25000000000000^33 ≤ 11904284996247^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503497319 10000000000 11904284996247 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3613642273/10000000000 : ℝ)^41 ≤ (28234516029877/100000000000000 : ℝ)^33 := by
    have hnat : (3613642273 : ℕ)^41*100000000000000^33 ≤ 28234516029877^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613642273 10000000000 28234516029877 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-637278949/2000000000 : ℝ), (5503497319/10000000000 : ℝ), (3613642273/10000000000 : ℝ)] ![(965933759049/4000000000000 : ℝ), (11904284996247/25000000000000 : ℝ), (28234516029877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-637278949/2000000000 : ℝ)|^41 ≤ (965933759049/4000000000000 : ℝ)^33
        have hw : |(-637278949/2000000000 : ℝ)|=(637278949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503497319/10000000000 : ℝ)|^41 ≤ (11904284996247/25000000000000 : ℝ)^33
        have hw : |(5503497319/10000000000 : ℝ)|=(5503497319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3613642273/10000000000 : ℝ)|^41 ≤ (28234516029877/100000000000000 : ℝ)^33
        have hw : |(3613642273/10000000000 : ℝ)|=(3613642273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6021373379/10000000000 : ℝ)*x 0 + (244689/10000000000 : ℝ)*x 1 + (5423025791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6021373379/10000000000 : ℝ)^41 ≤ (53246175684691/100000000000000 : ℝ)^33 := by
    have hnat : (6021373379 : ℕ)^41*100000000000000^33 ≤ 53246175684691^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021373379 10000000000 53246175684691 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244689/10000000000 : ℝ)^41 ≤ (18651029/10000000000000 : ℝ)^33 := by
    have hnat : (244689 : ℕ)^41*10000000000000^33 ≤ 18651029^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244689 10000000000 18651029 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423025791/10000000000 : ℝ)^41 ≤ (23376818898923/50000000000000 : ℝ)^33 := by
    have hnat : (5423025791 : ℕ)^41*50000000000000^33 ≤ 23376818898923^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423025791 10000000000 23376818898923 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6021373379/10000000000 : ℝ), (244689/10000000000 : ℝ), (5423025791/10000000000 : ℝ)] ![(53246175684691/100000000000000 : ℝ), (18651029/10000000000000 : ℝ), (23376818898923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6021373379/10000000000 : ℝ)|^41 ≤ (53246175684691/100000000000000 : ℝ)^33
        have hw : |(6021373379/10000000000 : ℝ)|=(6021373379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244689/10000000000 : ℝ)|^41 ≤ (18651029/10000000000000 : ℝ)^33
        have hw : |(244689/10000000000 : ℝ)|=(244689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423025791/10000000000 : ℝ)|^41 ≤ (23376818898923/50000000000000 : ℝ)^33
        have hw : |(5423025791/10000000000 : ℝ)|=(5423025791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2752760373/10000000000 : ℝ)*x 0 + (629984873/1000000000 : ℝ)*x 1 + (-624372813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752760373/10000000000 : ℝ)^41 ≤ (4027028323641/20000000000000 : ℝ)^33 := by
    have hnat : (2752760373 : ℕ)^41*20000000000000^33 ≤ 4027028323641^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752760373 10000000000 4027028323641 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629984873/1000000000 : ℝ)^41 ≤ (28161311890381/50000000000000 : ℝ)^33 := by
    have hnat : (629984873 : ℕ)^41*50000000000000^33 ≤ 28161311890381^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629984873 1000000000 28161311890381 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624372813/2000000000 : ℝ)^41 ≤ (23542234587323/100000000000000 : ℝ)^33 := by
    have hnat : (624372813 : ℕ)^41*100000000000000^33 ≤ 23542234587323^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624372813 2000000000 23542234587323 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752760373/10000000000 : ℝ), (629984873/1000000000 : ℝ), (-624372813/2000000000 : ℝ)] ![(4027028323641/20000000000000 : ℝ), (28161311890381/50000000000000 : ℝ), (23542234587323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752760373/10000000000 : ℝ)|^41 ≤ (4027028323641/20000000000000 : ℝ)^33
        have hw : |(2752760373/10000000000 : ℝ)|=(2752760373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629984873/1000000000 : ℝ)|^41 ≤ (28161311890381/50000000000000 : ℝ)^33
        have hw : |(629984873/1000000000 : ℝ)|=(629984873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624372813/2000000000 : ℝ)|^41 ≤ (23542234587323/100000000000000 : ℝ)^33
        have hw : |(-624372813/2000000000 : ℝ)|=(624372813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3649001569/10000000000 : ℝ)*x 0 + (2397761351/10000000000 : ℝ)*x 1 + (3065835863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3649001569/10000000000 : ℝ)^41 ≤ (5715634138713/20000000000000 : ℝ)^33 := by
    have hnat : (3649001569 : ℕ)^41*20000000000000^33 ≤ 5715634138713^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3649001569 10000000000 5715634138713 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397761351/10000000000 : ℝ)^41 ≤ (8480586507343/50000000000000 : ℝ)^33 := by
    have hnat : (2397761351 : ℕ)^41*50000000000000^33 ≤ 8480586507343^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397761351 10000000000 8480586507343 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3065835863/5000000000 : ℝ)^41 ≤ (54460656281449/100000000000000 : ℝ)^33 := by
    have hnat : (3065835863 : ℕ)^41*100000000000000^33 ≤ 54460656281449^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3065835863 5000000000 54460656281449 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3649001569/10000000000 : ℝ), (2397761351/10000000000 : ℝ), (3065835863/5000000000 : ℝ)] ![(5715634138713/20000000000000 : ℝ), (8480586507343/50000000000000 : ℝ), (54460656281449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3649001569/10000000000 : ℝ)|^41 ≤ (5715634138713/20000000000000 : ℝ)^33
        have hw : |(-3649001569/10000000000 : ℝ)|=(3649001569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2397761351/10000000000 : ℝ)|^41 ≤ (8480586507343/50000000000000 : ℝ)^33
        have hw : |(2397761351/10000000000 : ℝ)|=(2397761351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3065835863/5000000000 : ℝ)|^41 ≤ (54460656281449/100000000000000 : ℝ)^33
        have hw : |(3065835863/5000000000 : ℝ)|=(3065835863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4699469059/10000000000 : ℝ)*x 0 + (4442349/10000000000 : ℝ)*x 1 + (3352611651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4699469059/10000000000 : ℝ)^41 ≤ (39133209873373/100000000000000 : ℝ)^33 := by
    have hnat : (4699469059 : ℕ)^41*100000000000000^33 ≤ 39133209873373^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699469059 10000000000 39133209873373 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442349/10000000000 : ℝ)^41 ≤ (6837742109/100000000000000 : ℝ)^33 := by
    have hnat : (4442349 : ℕ)^41*100000000000000^33 ≤ 6837742109^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442349 10000000000 6837742109 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352611651/5000000000 : ℝ)^41 ≤ (60859952375503/100000000000000 : ℝ)^33 := by
    have hnat : (3352611651 : ℕ)^41*100000000000000^33 ≤ 60859952375503^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352611651 5000000000 60859952375503 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4699469059/10000000000 : ℝ), (4442349/10000000000 : ℝ), (3352611651/5000000000 : ℝ)] ![(39133209873373/100000000000000 : ℝ), (6837742109/100000000000000 : ℝ), (60859952375503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4699469059/10000000000 : ℝ)|^41 ≤ (39133209873373/100000000000000 : ℝ)^33
        have hw : |(4699469059/10000000000 : ℝ)|=(4699469059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442349/10000000000 : ℝ)|^41 ≤ (6837742109/100000000000000 : ℝ)^33
        have hw : |(4442349/10000000000 : ℝ)|=(4442349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3352611651/5000000000 : ℝ)|^41 ≤ (60859952375503/100000000000000 : ℝ)^33
        have hw : |(3352611651/5000000000 : ℝ)|=(3352611651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (351978171/5000000000 : ℝ)*x 0 + (839923099/1000000000 : ℝ)*x 1 + (-113155627/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351978171/5000000000 : ℝ)^41 ≤ (924917252063/25000000000000 : ℝ)^33 := by
    have hnat : (351978171 : ℕ)^41*25000000000000^33 ≤ 924917252063^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351978171 5000000000 924917252063 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (839923099/1000000000 : ℝ)^41 ≤ (80514360786993/100000000000000 : ℝ)^33 := by
    have hnat : (839923099 : ℕ)^41*100000000000000^33 ≤ 80514360786993^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839923099 1000000000 80514360786993 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113155627/500000000 : ℝ)^41 ≤ (15785970199273/100000000000000 : ℝ)^33 := by
    have hnat : (113155627 : ℕ)^41*100000000000000^33 ≤ 15785970199273^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113155627 500000000 15785970199273 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351978171/5000000000 : ℝ), (839923099/1000000000 : ℝ), (-113155627/500000000 : ℝ)] ![(924917252063/25000000000000 : ℝ), (80514360786993/100000000000000 : ℝ), (15785970199273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351978171/5000000000 : ℝ)|^41 ≤ (924917252063/25000000000000 : ℝ)^33
        have hw : |(351978171/5000000000 : ℝ)|=(351978171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(839923099/1000000000 : ℝ)|^41 ≤ (80514360786993/100000000000000 : ℝ)^33
        have hw : |(839923099/1000000000 : ℝ)|=(839923099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113155627/500000000 : ℝ)|^41 ≤ (15785970199273/100000000000000 : ℝ)^33
        have hw : |(-113155627/500000000 : ℝ)|=(113155627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2121459517/10000000000 : ℝ)*x 0 + (6843485379/10000000000 : ℝ)*x 1 + (612968697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121459517/10000000000 : ℝ)^41 ≤ (14567824062463/100000000000000 : ℝ)^33 := by
    have hnat : (2121459517 : ℕ)^41*100000000000000^33 ≤ 14567824062463^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121459517 10000000000 14567824062463 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6843485379/10000000000 : ℝ)^41 ≤ (12484598329601/20000000000000 : ℝ)^33 := by
    have hnat : (6843485379 : ℕ)^41*20000000000000^33 ≤ 12484598329601^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6843485379 10000000000 12484598329601 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612968697/2000000000 : ℝ)^41 ≤ (11504592140121/50000000000000 : ℝ)^33 := by
    have hnat : (612968697 : ℕ)^41*50000000000000^33 ≤ 11504592140121^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612968697 2000000000 11504592140121 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121459517/10000000000 : ℝ), (6843485379/10000000000 : ℝ), (612968697/2000000000 : ℝ)] ![(14567824062463/100000000000000 : ℝ), (12484598329601/20000000000000 : ℝ), (11504592140121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121459517/10000000000 : ℝ)|^41 ≤ (14567824062463/100000000000000 : ℝ)^33
        have hw : |(2121459517/10000000000 : ℝ)|=(2121459517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6843485379/10000000000 : ℝ)|^41 ≤ (12484598329601/20000000000000 : ℝ)^33
        have hw : |(6843485379/10000000000 : ℝ)|=(6843485379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(612968697/2000000000 : ℝ)|^41 ≤ (11504592140121/50000000000000 : ℝ)^33
        have hw : |(612968697/2000000000 : ℝ)|=(612968697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5591819393/10000000000 : ℝ)*x 0 + (4011323921/10000000000 : ℝ)*x 1 + (2658983173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5591819393/10000000000 : ℝ)^41 ≤ (24284205564471/50000000000000 : ℝ)^33 := by
    have hnat : (5591819393 : ℕ)^41*50000000000000^33 ≤ 24284205564471^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591819393 10000000000 24284205564471 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011323921/10000000000 : ℝ)^41 ≤ (32145120839751/100000000000000 : ℝ)^33 := by
    have hnat : (4011323921 : ℕ)^41*100000000000000^33 ≤ 32145120839751^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011323921 10000000000 32145120839751 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2658983173/10000000000 : ℝ)^41 ≤ (19286468018889/100000000000000 : ℝ)^33 := by
    have hnat : (2658983173 : ℕ)^41*100000000000000^33 ≤ 19286468018889^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2658983173 10000000000 19286468018889 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5591819393/10000000000 : ℝ), (4011323921/10000000000 : ℝ), (2658983173/10000000000 : ℝ)] ![(24284205564471/50000000000000 : ℝ), (32145120839751/100000000000000 : ℝ), (19286468018889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5591819393/10000000000 : ℝ)|^41 ≤ (24284205564471/50000000000000 : ℝ)^33
        have hw : |(-5591819393/10000000000 : ℝ)|=(5591819393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011323921/10000000000 : ℝ)|^41 ≤ (32145120839751/100000000000000 : ℝ)^33
        have hw : |(4011323921/10000000000 : ℝ)|=(4011323921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2658983173/10000000000 : ℝ)|^41 ≤ (19286468018889/100000000000000 : ℝ)^33
        have hw : |(2658983173/10000000000 : ℝ)|=(2658983173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3386982203/5000000000 : ℝ)*x 0 + (8557283/5000000000 : ℝ)*x 1 + (924284267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3386982203/5000000000 : ℝ)^41 ≤ (61636097144117/100000000000000 : ℝ)^33 := by
    have hnat : (3386982203 : ℕ)^41*100000000000000^33 ≤ 61636097144117^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3386982203 5000000000 61636097144117 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8557283/5000000000 : ℝ)^41 ≤ (18265716673/50000000000000 : ℝ)^33 := by
    have hnat : (8557283 : ℕ)^41*50000000000000^33 ≤ 18265716673^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8557283 5000000000 18265716673 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924284267/2000000000 : ℝ)^41 ≤ (38327371410453/100000000000000 : ℝ)^33 := by
    have hnat : (924284267 : ℕ)^41*100000000000000^33 ≤ 38327371410453^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924284267 2000000000 38327371410453 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3386982203/5000000000 : ℝ), (8557283/5000000000 : ℝ), (924284267/2000000000 : ℝ)] ![(61636097144117/100000000000000 : ℝ), (18265716673/50000000000000 : ℝ), (38327371410453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3386982203/5000000000 : ℝ)|^41 ≤ (61636097144117/100000000000000 : ℝ)^33
        have hw : |(3386982203/5000000000 : ℝ)|=(3386982203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8557283/5000000000 : ℝ)|^41 ≤ (18265716673/50000000000000 : ℝ)^33
        have hw : |(8557283/5000000000 : ℝ)|=(8557283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924284267/2000000000 : ℝ)|^41 ≤ (38327371410453/100000000000000 : ℝ)^33
        have hw : |(924284267/2000000000 : ℝ)|=(924284267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (63166297/2500000000 : ℝ)*x 0 + (3042800237/5000000000 : ℝ)*x 1 + (-32873609/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63166297/2500000000 : ℝ)^41 ≤ (1035818564359/100000000000000 : ℝ)^33 := by
    have hnat : (63166297 : ℕ)^41*100000000000000^33 ≤ 1035818564359^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63166297 2500000000 1035818564359 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3042800237/5000000000 : ℝ)^41 ≤ (10790544419847/20000000000000 : ℝ)^33 := by
    have hnat : (3042800237 : ℕ)^41*20000000000000^33 ≤ 10790544419847^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042800237 5000000000 10790544419847 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32873609/62500000 : ℝ)^41 ≤ (45011459330449/100000000000000 : ℝ)^33 := by
    have hnat : (32873609 : ℕ)^41*100000000000000^33 ≤ 45011459330449^33*62500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32873609 62500000 45011459330449 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63166297/2500000000 : ℝ), (3042800237/5000000000 : ℝ), (-32873609/62500000 : ℝ)] ![(1035818564359/100000000000000 : ℝ), (10790544419847/20000000000000 : ℝ), (45011459330449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63166297/2500000000 : ℝ)|^41 ≤ (1035818564359/100000000000000 : ℝ)^33
        have hw : |(63166297/2500000000 : ℝ)|=(63166297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3042800237/5000000000 : ℝ)|^41 ≤ (10790544419847/20000000000000 : ℝ)^33
        have hw : |(3042800237/5000000000 : ℝ)|=(3042800237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32873609/62500000 : ℝ)|^41 ≤ (45011459330449/100000000000000 : ℝ)^33
        have hw : |(-32873609/62500000 : ℝ)|=(32873609/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (549371299/2500000000 : ℝ)*x 0 + (5394977563/10000000000 : ℝ)*x 1 + (924284267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549371299/2500000000 : ℝ)^41 ≤ (7609618093819/50000000000000 : ℝ)^33 := by
    have hnat : (549371299 : ℕ)^41*50000000000000^33 ≤ 7609618093819^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549371299 2500000000 7609618093819 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394977563/10000000000 : ℝ)^41 ≤ (23226696194351/50000000000000 : ℝ)^33 := by
    have hnat : (5394977563 : ℕ)^41*50000000000000^33 ≤ 23226696194351^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394977563 10000000000 23226696194351 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924284267/2000000000 : ℝ)^41 ≤ (38327371410453/100000000000000 : ℝ)^33 := by
    have hnat : (924284267 : ℕ)^41*100000000000000^33 ≤ 38327371410453^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924284267 2000000000 38327371410453 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549371299/2500000000 : ℝ), (5394977563/10000000000 : ℝ), (924284267/2000000000 : ℝ)] ![(7609618093819/50000000000000 : ℝ), (23226696194351/50000000000000 : ℝ), (38327371410453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549371299/2500000000 : ℝ)|^41 ≤ (7609618093819/50000000000000 : ℝ)^33
        have hw : |(549371299/2500000000 : ℝ)|=(549371299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394977563/10000000000 : ℝ)|^41 ≤ (23226696194351/50000000000000 : ℝ)^33
        have hw : |(5394977563/10000000000 : ℝ)|=(5394977563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924284267/2000000000 : ℝ)|^41 ≤ (38327371410453/100000000000000 : ℝ)^33
        have hw : |(924284267/2000000000 : ℝ)|=(924284267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-557712117/2500000000 : ℝ)*x 0 + (3432630249/5000000000 : ℝ)*x 1 + (146852553/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557712117/2500000000 : ℝ)^41 ≤ (15506844154051/100000000000000 : ℝ)^33 := by
    have hnat : (557712117 : ℕ)^41*100000000000000^33 ≤ 15506844154051^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557712117 2500000000 15506844154051 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3432630249/5000000000 : ℝ)^41 ≤ (62669859774779/100000000000000 : ℝ)^33 := by
    have hnat : (3432630249 : ℕ)^41*100000000000000^33 ≤ 62669859774779^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432630249 5000000000 62669859774779 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146852553/500000000 : ℝ)^41 ≤ (10911648028627/50000000000000 : ℝ)^33 := by
    have hnat : (146852553 : ℕ)^41*50000000000000^33 ≤ 10911648028627^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146852553 500000000 10911648028627 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-557712117/2500000000 : ℝ), (3432630249/5000000000 : ℝ), (146852553/500000000 : ℝ)] ![(15506844154051/100000000000000 : ℝ), (62669859774779/100000000000000 : ℝ), (10911648028627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-557712117/2500000000 : ℝ)|^41 ≤ (15506844154051/100000000000000 : ℝ)^33
        have hw : |(-557712117/2500000000 : ℝ)|=(557712117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3432630249/5000000000 : ℝ)|^41 ≤ (62669859774779/100000000000000 : ℝ)^33
        have hw : |(3432630249/5000000000 : ℝ)|=(3432630249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146852553/500000000 : ℝ)|^41 ≤ (10911648028627/50000000000000 : ℝ)^33
        have hw : |(146852553/500000000 : ℝ)|=(146852553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4103861557/5000000000 : ℝ)*x 0 + (891/1000000000 : ℝ)*x 1 + (29302049/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103861557/5000000000 : ℝ)^41 ≤ (15647976858739/20000000000000 : ℝ)^33 := by
    have hnat : (4103861557 : ℕ)^41*20000000000000^33 ≤ 15647976858739^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103861557 5000000000 15647976858739 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891/1000000000 : ℝ)^41 ≤ (760539/25000000000000 : ℝ)^33 := by
    have hnat : (891 : ℕ)^41*25000000000000^33 ≤ 760539^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891 1000000000 760539 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29302049/100000000 : ℝ)^41 ≤ (21760112654159/100000000000000 : ℝ)^33 := by
    have hnat : (29302049 : ℕ)^41*100000000000000^33 ≤ 21760112654159^33*100000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29302049 100000000 21760112654159 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103861557/5000000000 : ℝ), (891/1000000000 : ℝ), (29302049/100000000 : ℝ)] ![(15647976858739/20000000000000 : ℝ), (760539/25000000000000 : ℝ), (21760112654159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103861557/5000000000 : ℝ)|^41 ≤ (15647976858739/20000000000000 : ℝ)^33
        have hw : |(4103861557/5000000000 : ℝ)|=(4103861557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(891/1000000000 : ℝ)|^41 ≤ (760539/25000000000000 : ℝ)^33
        have hw : |(891/1000000000 : ℝ)|=(891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29302049/100000000 : ℝ)|^41 ≤ (21760112654159/100000000000000 : ℝ)^33
        have hw : |(29302049/100000000 : ℝ)|=(29302049/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (420498931/10000000000 : ℝ)*x 0 + (517456239/625000000 : ℝ)*x 1 + (-1311407701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420498931/10000000000 : ℝ)^41 ≤ (487609493223/25000000000000 : ℝ)^33 := by
    have hnat : (420498931 : ℕ)^41*25000000000000^33 ≤ 487609493223^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420498931 10000000000 487609493223 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517456239/625000000 : ℝ)^41 ≤ (79088488096289/100000000000000 : ℝ)^33 := by
    have hnat : (517456239 : ℕ)^41*100000000000000^33 ≤ 79088488096289^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517456239 625000000 79088488096289 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311407701/5000000000 : ℝ)^41 ≤ (18961073925339/100000000000000 : ℝ)^33 := by
    have hnat : (1311407701 : ℕ)^41*100000000000000^33 ≤ 18961073925339^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311407701 5000000000 18961073925339 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420498931/10000000000 : ℝ), (517456239/625000000 : ℝ), (-1311407701/5000000000 : ℝ)] ![(487609493223/25000000000000 : ℝ), (79088488096289/100000000000000 : ℝ), (18961073925339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420498931/10000000000 : ℝ)|^41 ≤ (487609493223/25000000000000 : ℝ)^33
        have hw : |(420498931/10000000000 : ℝ)|=(420498931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517456239/625000000 : ℝ)|^41 ≤ (79088488096289/100000000000000 : ℝ)^33
        have hw : |(517456239/625000000 : ℝ)|=(517456239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1311407701/5000000000 : ℝ)|^41 ≤ (18961073925339/100000000000000 : ℝ)^33
        have hw : |(-1311407701/5000000000 : ℝ)|=(1311407701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s0_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6682576339/10000000000 : ℝ)*x 0 + (3144559683/10000000000 : ℝ)*x 1 + (2246284859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6682576339/10000000000 : ℝ)^41 ≤ (60604670334431/100000000000000 : ℝ)^33 := by
    have hnat : (6682576339 : ℕ)^41*100000000000000^33 ≤ 60604670334431^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6682576339 10000000000 60604670334431 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3144559683/10000000000 : ℝ)^41 ≤ (11877530973151/50000000000000 : ℝ)^33 := by
    have hnat : (3144559683 : ℕ)^41*50000000000000^33 ≤ 11877530973151^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3144559683 10000000000 11877530973151 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246284859/10000000000 : ℝ)^41 ≤ (15640267708703/100000000000000 : ℝ)^33 := by
    have hnat : (2246284859 : ℕ)^41*100000000000000^33 ≤ 15640267708703^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246284859 10000000000 15640267708703 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6682576339/10000000000 : ℝ), (3144559683/10000000000 : ℝ), (2246284859/10000000000 : ℝ)] ![(60604670334431/100000000000000 : ℝ), (11877530973151/50000000000000 : ℝ), (15640267708703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6682576339/10000000000 : ℝ)|^41 ≤ (60604670334431/100000000000000 : ℝ)^33
        have hw : |(6682576339/10000000000 : ℝ)|=(6682576339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3144559683/10000000000 : ℝ)|^41 ≤ (11877530973151/50000000000000 : ℝ)^33
        have hw : |(3144559683/10000000000 : ℝ)|=(3144559683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246284859/10000000000 : ℝ)|^41 ≤ (15640267708703/100000000000000 : ℝ)^33
        have hw : |(2246284859/10000000000 : ℝ)|=(2246284859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3349946541/10000000000 : ℝ)*x 0 + (133597021/250000000 : ℝ)*x 1 + (1815073781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3349946541/10000000000 : ℝ)^41 ≤ (25697776261101/100000000000000 : ℝ)^33 := by
    have hnat : (3349946541 : ℕ)^41*100000000000000^33 ≤ 25697776261101^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3349946541 10000000000 25697776261101 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133597021/250000000 : ℝ)^41 ≤ (11476848709857/25000000000000 : ℝ)^33 := by
    have hnat : (133597021 : ℕ)^41*25000000000000^33 ≤ 11476848709857^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133597021 250000000 11476848709857 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815073781/5000000000 : ℝ)^41 ≤ (14197414440397/50000000000000 : ℝ)^33 := by
    have hnat : (1815073781 : ℕ)^41*50000000000000^33 ≤ 14197414440397^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815073781 5000000000 14197414440397 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3349946541/10000000000 : ℝ), (133597021/250000000 : ℝ), (1815073781/5000000000 : ℝ)] ![(25697776261101/100000000000000 : ℝ), (11476848709857/25000000000000 : ℝ), (14197414440397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3349946541/10000000000 : ℝ)|^41 ≤ (25697776261101/100000000000000 : ℝ)^33
        have hw : |(-3349946541/10000000000 : ℝ)|=(3349946541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133597021/250000000 : ℝ)|^41 ≤ (11476848709857/25000000000000 : ℝ)^33
        have hw : |(133597021/250000000 : ℝ)|=(133597021/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1815073781/5000000000 : ℝ)|^41 ≤ (14197414440397/50000000000000 : ℝ)^33
        have hw : |(1815073781/5000000000 : ℝ)|=(1815073781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5731969979/10000000000 : ℝ)*x 0 + (-826702877/10000000000 : ℝ)*x 1 + (662003721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5731969979/10000000000 : ℝ)^41 ≤ (50085373286099/100000000000000 : ℝ)^33 := by
    have hnat : (5731969979 : ℕ)^41*100000000000000^33 ≤ 50085373286099^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5731969979 10000000000 50085373286099 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826702877/10000000000 : ℝ)^41 ≤ (2258700841793/50000000000000 : ℝ)^33 := by
    have hnat : (826702877 : ℕ)^41*50000000000000^33 ≤ 2258700841793^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826702877 10000000000 2258700841793 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662003721/1250000000 : ℝ)^41 ≤ (45397225011667/100000000000000 : ℝ)^33 := by
    have hnat : (662003721 : ℕ)^41*100000000000000^33 ≤ 45397225011667^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662003721 1250000000 45397225011667 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5731969979/10000000000 : ℝ), (-826702877/10000000000 : ℝ), (662003721/1250000000 : ℝ)] ![(50085373286099/100000000000000 : ℝ), (2258700841793/50000000000000 : ℝ), (45397225011667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5731969979/10000000000 : ℝ)|^41 ≤ (50085373286099/100000000000000 : ℝ)^33
        have hw : |(5731969979/10000000000 : ℝ)|=(5731969979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-826702877/10000000000 : ℝ)|^41 ≤ (2258700841793/50000000000000 : ℝ)^33
        have hw : |(-826702877/10000000000 : ℝ)|=(826702877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(662003721/1250000000 : ℝ)|^41 ≤ (45397225011667/100000000000000 : ℝ)^33
        have hw : |(662003721/1250000000 : ℝ)|=(662003721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (98471983/312500000 : ℝ)*x 0 + (1427970849/2500000000 : ℝ)*x 1 + (-3414672559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98471983/312500000 : ℝ)^41 ≤ (23816495260169/100000000000000 : ℝ)^33 := by
    have hnat : (98471983 : ℕ)^41*100000000000000^33 ≤ 23816495260169^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98471983 312500000 23816495260169 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427970849/2500000000 : ℝ)^41 ≤ (2493370124443/5000000000000 : ℝ)^33 := by
    have hnat : (1427970849 : ℕ)^41*5000000000000^33 ≤ 2493370124443^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427970849 2500000000 2493370124443 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3414672559/10000000000 : ℝ)^41 ≤ (26316102238861/100000000000000 : ℝ)^33 := by
    have hnat : (3414672559 : ℕ)^41*100000000000000^33 ≤ 26316102238861^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414672559 10000000000 26316102238861 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(98471983/312500000 : ℝ), (1427970849/2500000000 : ℝ), (-3414672559/10000000000 : ℝ)] ![(23816495260169/100000000000000 : ℝ), (2493370124443/5000000000000 : ℝ), (26316102238861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(98471983/312500000 : ℝ)|^41 ≤ (23816495260169/100000000000000 : ℝ)^33
        have hw : |(98471983/312500000 : ℝ)|=(98471983/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1427970849/2500000000 : ℝ)|^41 ≤ (2493370124443/5000000000000 : ℝ)^33
        have hw : |(1427970849/2500000000 : ℝ)|=(1427970849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3414672559/10000000000 : ℝ)|^41 ≤ (26316102238861/100000000000000 : ℝ)^33
        have hw : |(-3414672559/10000000000 : ℝ)|=(3414672559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320023_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3899333167/10000000000 : ℝ)*x 0 + (2431734859/5000000000 : ℝ)*x 1 + (28822181/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3899333167/10000000000 : ℝ)^41 ≤ (193961933663/625000000000 : ℝ)^33 := by
    have hnat : (3899333167 : ℕ)^41*625000000000^33 ≤ 193961933663^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3899333167 10000000000 193961933663 625000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431734859/5000000000 : ℝ)^41 ≤ (20418526310907/50000000000000 : ℝ)^33 := by
    have hnat : (2431734859 : ℕ)^41*50000000000000^33 ≤ 20418526310907^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431734859 5000000000 20418526310907 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28822181/80000000 : ℝ)^41 ≤ (879032436859/3125000000000 : ℝ)^33 := by
    have hnat : (28822181 : ℕ)^41*3125000000000^33 ≤ 879032436859^33*80000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28822181 80000000 879032436859 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3899333167/10000000000 : ℝ), (2431734859/5000000000 : ℝ), (28822181/80000000 : ℝ)] ![(193961933663/625000000000 : ℝ), (20418526310907/50000000000000 : ℝ), (879032436859/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3899333167/10000000000 : ℝ)|^41 ≤ (193961933663/625000000000 : ℝ)^33
        have hw : |(3899333167/10000000000 : ℝ)|=(3899333167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2431734859/5000000000 : ℝ)|^41 ≤ (20418526310907/50000000000000 : ℝ)^33
        have hw : |(2431734859/5000000000 : ℝ)|=(2431734859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28822181/80000000 : ℝ)|^41 ≤ (879032436859/3125000000000 : ℝ)^33
        have hw : |(28822181/80000000 : ℝ)|=(28822181/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320023 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
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
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-637278949/2000000000 : ℝ)*X 0 0+(5503497319/10000000000 : ℝ)*X 0 1+(3613642273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6021373379/10000000000 : ℝ)*X 1 0+(244689/10000000000 : ℝ)*X 1 1+(5423025791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2752760373/10000000000 : ℝ)*X 2 0+(629984873/1000000000 : ℝ)*X 2 1+(-624372813/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3649001569/10000000000 : ℝ)*X 0 0+(2397761351/10000000000 : ℝ)*X 0 1+(3065835863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4699469059/10000000000 : ℝ)*X 1 0+(4442349/10000000000 : ℝ)*X 1 1+(3352611651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((351978171/5000000000 : ℝ)*X 2 0+(839923099/1000000000 : ℝ)*X 2 1+(-113155627/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2121459517/10000000000 : ℝ)*X 0 0+(6843485379/10000000000 : ℝ)*X 0 1+(612968697/2000000000 : ℝ)*X 0 2+(2121459517/10000000000 : ℝ)*X 1 0+(6843485379/10000000000 : ℝ)*X 1 1+(612968697/2000000000 : ℝ)*X 1 2+(2121459517/10000000000 : ℝ)*X 2 0+(6843485379/10000000000 : ℝ)*X 2 1+(612968697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-5591819393/10000000000 : ℝ)*X 0 0+(4011323921/10000000000 : ℝ)*X 0 1+(2658983173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3386982203/5000000000 : ℝ)*X 1 0+(8557283/5000000000 : ℝ)*X 1 1+(924284267/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((63166297/2500000000 : ℝ)*X 2 0+(3042800237/5000000000 : ℝ)*X 2 1+(-32873609/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((549371299/2500000000 : ℝ)*X 0 0+(5394977563/10000000000 : ℝ)*X 0 1+(924284267/2000000000 : ℝ)*X 0 2+(549371299/2500000000 : ℝ)*X 1 0+(5394977563/10000000000 : ℝ)*X 1 1+(924284267/2000000000 : ℝ)*X 1 2+(549371299/2500000000 : ℝ)*X 2 0+(5394977563/10000000000 : ℝ)*X 2 1+(924284267/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-557712117/2500000000 : ℝ)*X 0 0+(3432630249/5000000000 : ℝ)*X 0 1+(146852553/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4103861557/5000000000 : ℝ)*X 1 0+(891/1000000000 : ℝ)*X 1 1+(29302049/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((420498931/10000000000 : ℝ)*X 2 0+(517456239/625000000 : ℝ)*X 2 1+(-1311407701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6682576339/10000000000 : ℝ)*X 0 0+(3144559683/10000000000 : ℝ)*X 0 1+(2246284859/10000000000 : ℝ)*X 0 2+(6682576339/10000000000 : ℝ)*X 1 0+(3144559683/10000000000 : ℝ)*X 1 1+(2246284859/10000000000 : ℝ)*X 1 2+(6682576339/10000000000 : ℝ)*X 2 0+(3144559683/10000000000 : ℝ)*X 2 1+(2246284859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((64507/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64507/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4560538489927755303207/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1167685506639/1000000000000 : ℝ)*(base7) + (2673699/1000000000000 : ℝ)*(base49) + (222898460343/1000000000000 : ℝ)*(base50) + (551881/200000000000 : ℝ)*(base53) + (761953/1000000000000 : ℝ)*(base60) + (210484734203/125000000000 : ℝ)*(major_s0_0) + (210484734203/125000000000 : ℝ)*(major_s0_1) + (1683875114219/1000000000000 : ℝ)*(major_s0_2) + (12313501/1000000000000 : ℝ)*(sp_s0_0) + (1811213767059/1000000000000 : ℝ)*(sp_s0_7) + (22640326007/12500000000 : ℝ)*(sp_s0_8) + (1811191372223/1000000000000 : ℝ)*(sp_s0_9) + (2064701207483/1000000000000 : ℝ)*(sp_s0_13) + (18733871/500000000000 : ℝ)*(sp_s0_23) + (224253925211/250000000000 : ℝ)*(f.failure) + (362245767993/200000000000 : ℝ)*(f.sum) + (305159233719769/2000000000000000000000000000 : ℝ)*base63 + (2367377075701763/10000000000000000000000000000 : ℝ)*base64 + (327906749648931/1250000000000000000000000000 : ℝ)*base67 + (3664474562479131/10000000000000000000000000000 : ℝ)*base68 + (752718137220261/10000000000000000000000000000 : ℝ)*base71 + (104845154273931/1250000000000000000000000000 : ℝ)*base72 + (208128487990253/1250000000000000000000000000 : ℝ)*base74 + (175921138759747/1250000000000000000000000000 : ℝ)*base76 + (2568940449/10000000000000000000000 : ℝ)*base79 + (223/625000000000000 : ℝ)*base87 + (223/625000000000000 : ℝ)*base89 + (223/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(33559/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(33559/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10431891518436663/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (12332713141/20000000000 : ℝ)*(base3) + (48426587237/100000000000 : ℝ)*(base7) + (141464250383/1000000000000 : ℝ)*(base40) + (31411353383/62500000000 : ℝ)*(base49) + (151207454849/1000000000000 : ℝ)*(base60) + (691370875417/500000000000 : ℝ)*(major_s0_0) + (691370875417/500000000000 : ℝ)*(major_s0_1) + (691370875417/500000000000 : ℝ)*(major_s0_2) + (188479/1000000000000 : ℝ)*(sp_s0_0) + (17879307/250000000000 : ℝ)*(sp_s0_1) + (1755369174497/1000000000000 : ℝ)*(sp_s0_14) + (1185966751399/500000000000 : ℝ)*(sp_s0_15) + (54855292593/31250000000 : ℝ)*(sp_s0_16) + (604228207453/1000000000000 : ℝ)*(sp_s0_20) + (368298996067/500000000000 : ℝ)*(f.failure) + (54855292593/31250000000 : ℝ)*(f.sum) + (409099347/2500000000000000000000 : ℝ)*base63 + (1464963300696191/5000000000000000000000000000 : ℝ)*base65 + (4354672159303809/5000000000000000000000000000 : ℝ)*base67 + (4201511670761367/5000000000000000000000000000 : ℝ)*base69 + (231582522771221/2500000000000000000000000000 : ℝ)*base70 + (3540150872696191/5000000000000000000000000000 : ℝ)*base73 + (1642242097238633/5000000000000000000000000000 : ℝ)*base75 + (2445921433261367/5000000000000000000000000000 : ℝ)*base77 + (1247170337/2000000000000000000000 : ℝ)*base79 + (69/1250000000000000 : ℝ)*base86 + (69/1250000000000000 : ℝ)*base88 + (69/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14201/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14201/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21110696538702204029601/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40923992361/250000000000 : ℝ)*(base3) + (1186342524547/1000000000000 : ℝ)*(base7) + (647509/200000000000 : ℝ)*(base11) + (91217767869/500000000000 : ℝ)*(base40) + (116153726017/1000000000000 : ℝ)*(base50) + (1778929326627/1000000000000 : ℝ)*(major_s0_0) + (1778929326627/1000000000000 : ℝ)*(major_s0_1) + (1778929326627/1000000000000 : ℝ)*(major_s0_2) + (3263513/1000000000000 : ℝ)*(sp_s0_2) + (25572577/500000000000 : ℝ)*(sp_s0_9) + (1940157352723/1000000000000 : ℝ)*(sp_s0_21) + (65745517491/31250000000 : ℝ)*(sp_s0_22) + (2425132727/1250000000 : ℝ)*(sp_s0_23) + (1970296952837/1000000000000 : ℝ)*(sp_s0_27) + (473825198867/500000000000 : ℝ)*(f.failure) + (485040147567/250000000000 : ℝ)*(f.sum) + (1294945379/10000000000000000000000 : ℝ)*base62 + (106150347817979/10000000000000000000000000000 : ℝ)*base64 + (4187612259817979/10000000000000000000000000000 : ℝ)*base67 + (3143803333836077/10000000000000000000000000000 : ℝ)*base69 + (2796981015509049/5000000000000000000000000000 : ℝ)*base71 + (4494027405817979/10000000000000000000000000000 : ℝ)*base72 + (593540604836077/10000000000000000000000000000 : ℝ)*base74 + (12314290223836077/10000000000000000000000000000 : ℝ)*base77 + (1181600139/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (919/1250000000000000 : ℝ)*base86 + (919/1250000000000000 : ℝ)*base88 + (919/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (64507/100000 : ℝ) ^ (5 : ℝ) ≤ (11169512643324091819/100000000000000000000 : ℝ) := by
    have hpowers : (64507/100000 : ℝ)^5 ≤ (11169512643324091819/100000000000000000000 : ℝ)^1 := by
      have hnat : (64507 : ℕ)^5*100000000000000000000^1 ≤ 11169512643324091819^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64507 100000 11169512643324091819 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64507/100000 : ℝ)) (X := (11169512643324091819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (111169512643324091819/100000000000000000000 : ℝ) ≤ (10214030264543911/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (111169512643324091819/100000000000000000000 : ℝ)^1 ≤ (10214030264543911/10000000000000000 : ℝ)^5 := by
      have hnat : (111169512643324091819 : ℕ)^1*10000000000000000^5 ≤ 10214030264543911^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111169512643324091819 100000000000000000000 10214030264543911 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10214030264543911/10000000000000000 : ℝ)) (X := (111169512643324091819/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (61169512643324091819/50000000000000000000 : ℝ) ≤ (2602873200470127/2500000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (61169512643324091819/50000000000000000000 : ℝ)^1 ≤ (2602873200470127/2500000000000000 : ℝ)^5 := by
      have hnat : (61169512643324091819 : ℕ)^1*2500000000000000^5 ≤ 2602873200470127^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61169512643324091819 50000000000000000000 2602873200470127 2500000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2602873200470127/2500000000000000 : ℝ)) (X := (61169512643324091819/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(214030264543911/6450700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(197462537336597/6450700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (64507/100000 : ℝ)) (alpha := (214030264543911/6450700000000000 : ℝ)) (beta := (197462537336597/6450700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64507/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(214030264543911/6450700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(197462537336597/6450700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (33559/100000 : ℝ) ^ (5 : ℝ) ≤ (53205321111359313/12500000000000000000 : ℝ) := by
    have hpowers : (33559/100000 : ℝ)^5 ≤ (53205321111359313/12500000000000000000 : ℝ)^1 := by
      have hnat : (33559 : ℕ)^5*12500000000000000000^1 ≤ 53205321111359313^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33559 100000 53205321111359313 12500000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33559/100000 : ℝ)) (X := (53205321111359313/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (12553205321111359313/12500000000000000000 : ℝ) ≤ (10008498394555057/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (12553205321111359313/12500000000000000000 : ℝ)^1 ≤ (10008498394555057/10000000000000000 : ℝ)^5 := by
      have hnat : (12553205321111359313 : ℕ)^1*10000000000000000^5 ≤ 10008498394555057^5*12500000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12553205321111359313 12500000000000000000 10008498394555057 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008498394555057/10000000000000000 : ℝ)) (X := (12553205321111359313/12500000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (6303205321111359313/6250000000000000000 : ℝ) ≤ (10016968022210617/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (6303205321111359313/6250000000000000000 : ℝ)^1 ≤ (10016968022210617/10000000000000000 : ℝ)^5 := by
      have hnat : (6303205321111359313 : ℕ)^1*10000000000000000^5 ≤ 10016968022210617^5*6250000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6303205321111359313 6250000000000000000 10016968022210617 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016968022210617/10000000000000000 : ℝ)) (X := (6303205321111359313/6250000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8498394555057/3355900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(211740691389/83897500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (33559/100000 : ℝ)) (alpha := (8498394555057/3355900000000000 : ℝ)) (beta := (211740691389/83897500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (33559/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8498394555057/3355900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(211740691389/83897500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14201/20000 : ℝ) ^ (5 : ℝ) ≤ (18048647325090514719/100000000000000000000 : ℝ) := by
    have hpowers : (14201/20000 : ℝ)^5 ≤ (18048647325090514719/100000000000000000000 : ℝ)^1 := by
      have hnat : (14201 : ℕ)^5*100000000000000000000^1 ≤ 18048647325090514719^1*20000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14201 20000 18048647325090514719 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14201/20000 : ℝ)) (X := (18048647325090514719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (118048647325090514719/100000000000000000000 : ℝ) ≤ (10337420985016117/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (118048647325090514719/100000000000000000000 : ℝ)^1 ≤ (10337420985016117/10000000000000000 : ℝ)^5 := by
      have hnat : (118048647325090514719 : ℕ)^1*10000000000000000^5 ≤ 10337420985016117^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118048647325090514719 100000000000000000000 10337420985016117 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10337420985016117/10000000000000000 : ℝ)) (X := (118048647325090514719/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (68048647325090514719/50000000000000000000 : ℝ) ≤ (265894838605419/250000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (68048647325090514719/50000000000000000000 : ℝ)^1 ≤ (265894838605419/250000000000000 : ℝ)^5 := by
      have hnat : (68048647325090514719 : ℕ)^1*250000000000000^5 ≤ 265894838605419^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68048647325090514719 50000000000000000000 265894838605419 250000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (265894838605419/250000000000000 : ℝ)) (X := (68048647325090514719/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(337420985016117/7100500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(298372559200643/7100500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (14201/20000 : ℝ)) (alpha := (337420985016117/7100500000000000 : ℝ)) (beta := (298372559200643/7100500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14201/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(337420985016117/7100500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(298372559200643/7100500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3349946541/10000000000 : ℝ)*X 0 0+(133597021/250000000 : ℝ)*X 0 1+(1815073781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5731969979/10000000000 : ℝ)*X 1 0+(-826702877/10000000000 : ℝ)*X 1 1+(662003721/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((98471983/312500000 : ℝ)*X 2 0+(1427970849/2500000000 : ℝ)*X 2 1+(-3414672559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3899333167/10000000000 : ℝ)*X 0 0+(2431734859/5000000000 : ℝ)*X 0 1+(28822181/80000000 : ℝ)*X 0 2+(3899333167/10000000000 : ℝ)*X 1 0+(2431734859/5000000000 : ℝ)*X 1 1+(28822181/80000000 : ℝ)*X 1 2+(3899333167/10000000000 : ℝ)*X 2 0+(2431734859/5000000000 : ℝ)*X 2 1+(28822181/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320023_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-18895985162643673135744067903169/2290159767500000000000000000000 : ℝ) := by norm_num
    linear_combination (87029/500000000000 : ℝ)*(base8) + (89/31250000000 : ℝ)*(base21) + (19729/100000000000 : ℝ)*(base33) + (117810618481/1000000000000 : ℝ)*(base40) + (564819984539/500000000000 : ℝ)*(base49) + (123171986231/200000000000 : ℝ)*(base50) + (214513/1000000000000 : ℝ)*(base59) + (1707/100000000000 : ℝ)*(base60) + (187719980271/100000000000 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (2750315245091/1000000000000 : ℝ)*(sp_s1_0) + (2750315221859/1000000000000 : ℝ)*(sp_s1_1) + (2750315219011/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (687578854787/250000000000 : ℝ)*(f.sum) + (1106224118962103929/4765713590000000000000000000000 : ℝ)*base63 + (373902210111/3550250000000000000000000 : ℝ)*base64 + (38565599363689/167795000000000000000000000 : ℝ)*base66 + (100264372217161/142010000000000000000000000 : ℝ)*base68 + (1277526001242636909/4580319535000000000000000000000 : ℝ)*base70 + (172632941262803/645070000000000000000000000 : ℝ)*base73 + (264974645467/10487187500000000000000000 : ℝ)*base74 + (399812975371611/645070000000000000000000000 : ℝ)*base76 + (1002092158222627247/2164790413000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c320024_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4694101439/10000000000 : ℝ)*x 0 + (2939361849/10000000000 : ℝ)*x 1 + (-4694101409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4694101439/10000000000 : ℝ)^41 ≤ (39077684919161/100000000000000 : ℝ)^33 := by
    have hnat : (4694101439 : ℕ)^41*100000000000000^33 ≤ 39077684919161^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694101439 10000000000 39077684919161 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939361849/10000000000 : ℝ)^41 ≤ (218446304587/1000000000000 : ℝ)^33 := by
    have hnat : (2939361849 : ℕ)^41*1000000000000^33 ≤ 218446304587^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939361849 10000000000 218446304587 1000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4694101409/10000000000 : ℝ)^41 ≤ (39077684608871/100000000000000 : ℝ)^33 := by
    have hnat : (4694101409 : ℕ)^41*100000000000000^33 ≤ 39077684608871^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694101409 10000000000 39077684608871 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4694101439/10000000000 : ℝ), (2939361849/10000000000 : ℝ), (-4694101409/10000000000 : ℝ)] ![(39077684919161/100000000000000 : ℝ), (218446304587/1000000000000 : ℝ), (39077684608871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4694101439/10000000000 : ℝ)|^41 ≤ (39077684919161/100000000000000 : ℝ)^33
        have hw : |(-4694101439/10000000000 : ℝ)|=(4694101439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2939361849/10000000000 : ℝ)|^41 ≤ (218446304587/1000000000000 : ℝ)^33
        have hw : |(2939361849/10000000000 : ℝ)|=(2939361849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4694101409/10000000000 : ℝ)|^41 ≤ (39077684608871/100000000000000 : ℝ)^33
        have hw : |(-4694101409/10000000000 : ℝ)|=(4694101409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320024_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4694101439/10000000000 : ℝ)*x 0 + (-2939361849/10000000000 : ℝ)*x 1 + (-4694101409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4694101439/10000000000 : ℝ)^41 ≤ (39077684919161/100000000000000 : ℝ)^33 := by
    have hnat : (4694101439 : ℕ)^41*100000000000000^33 ≤ 39077684919161^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694101439 10000000000 39077684919161 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939361849/10000000000 : ℝ)^41 ≤ (218446304587/1000000000000 : ℝ)^33 := by
    have hnat : (2939361849 : ℕ)^41*1000000000000^33 ≤ 218446304587^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939361849 10000000000 218446304587 1000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4694101409/10000000000 : ℝ)^41 ≤ (39077684608871/100000000000000 : ℝ)^33 := by
    have hnat : (4694101409 : ℕ)^41*100000000000000^33 ≤ 39077684608871^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694101409 10000000000 39077684608871 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4694101439/10000000000 : ℝ), (-2939361849/10000000000 : ℝ), (-4694101409/10000000000 : ℝ)] ![(39077684919161/100000000000000 : ℝ), (218446304587/1000000000000 : ℝ), (39077684608871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4694101439/10000000000 : ℝ)|^41 ≤ (39077684919161/100000000000000 : ℝ)^33
        have hw : |(4694101439/10000000000 : ℝ)|=(4694101439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2939361849/10000000000 : ℝ)|^41 ≤ (218446304587/1000000000000 : ℝ)^33
        have hw : |(-2939361849/10000000000 : ℝ)|=(2939361849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4694101409/10000000000 : ℝ)|^41 ≤ (39077684608871/100000000000000 : ℝ)^33
        have hw : |(-4694101409/10000000000 : ℝ)|=(4694101409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320024_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1616730121/5000000000 : ℝ)*x 0 + (5799121263/10000000000 : ℝ)*x 1 + (3233460221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616730121/5000000000 : ℝ)^41 ≤ (24592294251533/100000000000000 : ℝ)^33 := by
    have hnat : (1616730121 : ℕ)^41*100000000000000^33 ≤ 24592294251533^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616730121 5000000000 24592294251533 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5799121263/10000000000 : ℝ)^41 ≤ (50815411687671/100000000000000 : ℝ)^33 := by
    have hnat : (5799121263 : ℕ)^41*100000000000000^33 ≤ 50815411687671^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799121263 10000000000 50815411687671 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3233460221/10000000000 : ℝ)^41 ≤ (24592294053097/100000000000000 : ℝ)^33 := by
    have hnat : (3233460221 : ℕ)^41*100000000000000^33 ≤ 24592294053097^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233460221 10000000000 24592294053097 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1616730121/5000000000 : ℝ), (5799121263/10000000000 : ℝ), (3233460221/10000000000 : ℝ)] ![(24592294251533/100000000000000 : ℝ), (50815411687671/100000000000000 : ℝ), (24592294053097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1616730121/5000000000 : ℝ)|^41 ≤ (24592294251533/100000000000000 : ℝ)^33
        have hw : |(1616730121/5000000000 : ℝ)|=(1616730121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5799121263/10000000000 : ℝ)|^41 ≤ (50815411687671/100000000000000 : ℝ)^33
        have hw : |(5799121263/10000000000 : ℝ)|=(5799121263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3233460221/10000000000 : ℝ)|^41 ≤ (24592294053097/100000000000000 : ℝ)^33
        have hw : |(3233460221/10000000000 : ℝ)|=(3233460221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320024_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1616730121/5000000000 : ℝ)*x 0 + (5799121263/10000000000 : ℝ)*x 1 + (-3233460221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616730121/5000000000 : ℝ)^41 ≤ (24592294251533/100000000000000 : ℝ)^33 := by
    have hnat : (1616730121 : ℕ)^41*100000000000000^33 ≤ 24592294251533^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616730121 5000000000 24592294251533 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5799121263/10000000000 : ℝ)^41 ≤ (50815411687671/100000000000000 : ℝ)^33 := by
    have hnat : (5799121263 : ℕ)^41*100000000000000^33 ≤ 50815411687671^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799121263 10000000000 50815411687671 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3233460221/10000000000 : ℝ)^41 ≤ (24592294053097/100000000000000 : ℝ)^33 := by
    have hnat : (3233460221 : ℕ)^41*100000000000000^33 ≤ 24592294053097^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233460221 10000000000 24592294053097 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1616730121/5000000000 : ℝ), (5799121263/10000000000 : ℝ), (-3233460221/10000000000 : ℝ)] ![(24592294251533/100000000000000 : ℝ), (50815411687671/100000000000000 : ℝ), (24592294053097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1616730121/5000000000 : ℝ)|^41 ≤ (24592294251533/100000000000000 : ℝ)^33
        have hw : |(1616730121/5000000000 : ℝ)|=(1616730121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5799121263/10000000000 : ℝ)|^41 ≤ (50815411687671/100000000000000 : ℝ)^33
        have hw : |(5799121263/10000000000 : ℝ)|=(5799121263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3233460221/10000000000 : ℝ)|^41 ≤ (24592294053097/100000000000000 : ℝ)^33
        have hw : |(-3233460221/10000000000 : ℝ)|=(3233460221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320024 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]]) : False := by
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
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4694101439/10000000000 : ℝ)*X 0 0+(2939361849/10000000000 : ℝ)*X 0 1+(-4694101409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320024_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4694101439/10000000000 : ℝ)*X 1 0+(-2939361849/10000000000 : ℝ)*X 1 1+(-4694101409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320024_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1616730121/5000000000 : ℝ)*X 2 0+(5799121263/10000000000 : ℝ)*X 2 1+(3233460221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320024_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1616730121/5000000000 : ℝ)*X 0 0+(5799121263/10000000000 : ℝ)*X 0 1+(-3233460221/10000000000 : ℝ)*X 0 2+(1616730121/5000000000 : ℝ)*X 1 0+(5799121263/10000000000 : ℝ)*X 1 1+(-3233460221/10000000000 : ℝ)*X 1 2+(1616730121/5000000000 : ℝ)*X 2 0+(5799121263/10000000000 : ℝ)*X 2 1+(-3233460221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320024_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-40775775932793453083828837817/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4082534277/1000000000000 : ℝ)*(base5) + (96986981027/1000000000000 : ℝ)*(base39) + (123181359111/250000000000 : ℝ)*(base49) + (197869225083/500000000000 : ℝ)*(base50) + (9843/1000000000000 : ℝ)*(base54) + (159237050509/500000000000 : ℝ)*(base59) + (469300002317/250000000000 : ℝ)*(major_s0_0) + (4693/2500 : ℝ)*(major_s0_1) + (1877199997209/1000000000000 : ℝ)*(major_s0_2) + (1359192510137/500000000000 : ℝ)*(sp_s0_0) + (1359192514771/500000000000 : ℝ)*(sp_s0_1) + (108898701877/40000000000 : ℝ)*(sp_s0_2) + (24897936397/25000000000 : ℝ)*(sp_s0_6) + (1359192506611/500000000000 : ℝ)*(f.sum) + (3943744893249641/10000000000000000000000000000 : ℝ)*base63 + (3029801964159007/10000000000000000000000000000 : ℝ)*base64 + (4164625573/5000000000000000000000 : ℝ)*base67 + (5100643130750359/10000000000000000000000000000 : ℝ)*base68 + (2343493854945939/10000000000000000000000000000 : ℝ)*base70 + (939736950265109/2500000000000000000000000000 : ℝ)*base72 + (336887601/1000000000000000000000 : ℝ)*base74 + (270926097446733/2500000000000000000000000000 : ℝ)*base76 + (335898173984891/2500000000000000000000000000 : ℝ)*base79 + (1763/250000000000 : ℝ)*base81 + (51/3125000000 : ℝ)*base83 + (9269/1000000000000 : ℝ)*base85 + (2317/250000000000 : ℝ)*base86 + (1763/250000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b011 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 23 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=23 ∨ c=24 := by omega
  rcases hc with rfl|rfl
  · exact collision_c320023 p hpa (by linarith only [hpb]) X hX
  · exact collision_c320024 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 23 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b011 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

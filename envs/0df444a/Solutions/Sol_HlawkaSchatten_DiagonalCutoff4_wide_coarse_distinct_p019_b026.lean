-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:22.188707+00:00
-- url     : https://prove2.me/submissions/c37dca76-924c-424a-a655-19bddbafc287

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
theorem collision_support_c319047_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-61286763/2000000000 : ℝ)*x 0 + (-1543069971/2500000000 : ℝ)*x 1 + (2582147183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61286763/2000000000 : ℝ)^81 ≤ (1299399340543/100000000000000 : ℝ)^65 := by
    have hnat : (61286763 : ℕ)^81*100000000000000^65 ≤ 1299399340543^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61286763 2000000000 1299399340543 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543069971/2500000000 : ℝ)^81 ≤ (13702600654007/25000000000000 : ℝ)^65 := by
    have hnat : (1543069971 : ℕ)^81*25000000000000^65 ≤ 13702600654007^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543069971 2500000000 13702600654007 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582147183/5000000000 : ℝ)^81 ≤ (8778039606247/20000000000000 : ℝ)^65 := by
    have hnat : (2582147183 : ℕ)^81*20000000000000^65 ≤ 8778039606247^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582147183 5000000000 8778039606247 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61286763/2000000000 : ℝ), (-1543069971/2500000000 : ℝ), (2582147183/5000000000 : ℝ)] ![(1299399340543/100000000000000 : ℝ), (13702600654007/25000000000000 : ℝ), (8778039606247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61286763/2000000000 : ℝ)|^81 ≤ (1299399340543/100000000000000 : ℝ)^65
        have hw : |(-61286763/2000000000 : ℝ)|=(61286763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1543069971/2500000000 : ℝ)|^81 ≤ (13702600654007/25000000000000 : ℝ)^65
        have hw : |(-1543069971/2500000000 : ℝ)|=(1543069971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582147183/5000000000 : ℝ)|^81 ≤ (8778039606247/20000000000000 : ℝ)^65
        have hw : |(2582147183/5000000000 : ℝ)|=(2582147183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5125825163/10000000000 : ℝ)*x 0 + (753846979/2000000000 : ℝ)*x 1 + (348364133/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5125825163/10000000000 : ℝ)^81 ≤ (21741576571073/50000000000000 : ℝ)^65 := by
    have hnat : (5125825163 : ℕ)^81*50000000000000^65 ≤ 21741576571073^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125825163 10000000000 21741576571073 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753846979/2000000000 : ℝ)^81 ≤ (7411162022807/25000000000000 : ℝ)^65 := by
    have hnat : (753846979 : ℕ)^81*25000000000000^65 ≤ 7411162022807^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753846979 2000000000 7411162022807 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348364133/1000000000 : ℝ)^81 ≤ (26872198744747/100000000000000 : ℝ)^65 := by
    have hnat : (348364133 : ℕ)^81*100000000000000^65 ≤ 26872198744747^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348364133 1000000000 26872198744747 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5125825163/10000000000 : ℝ), (753846979/2000000000 : ℝ), (348364133/1000000000 : ℝ)] ![(21741576571073/50000000000000 : ℝ), (7411162022807/25000000000000 : ℝ), (26872198744747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5125825163/10000000000 : ℝ)|^81 ≤ (21741576571073/50000000000000 : ℝ)^65
        have hw : |(5125825163/10000000000 : ℝ)|=(5125825163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(753846979/2000000000 : ℝ)|^81 ≤ (7411162022807/25000000000000 : ℝ)^65
        have hw : |(753846979/2000000000 : ℝ)|=(753846979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(348364133/1000000000 : ℝ)|^81 ≤ (26872198744747/100000000000000 : ℝ)^65
        have hw : |(348364133/1000000000 : ℝ)|=(348364133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5508241269/10000000000 : ℝ)*x 0 + (-1875803193/5000000000 : ℝ)*x 1 + (-1535527149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508241269/10000000000 : ℝ)^81 ≤ (1902489588591/4000000000000 : ℝ)^65 := by
    have hnat : (5508241269 : ℕ)^81*4000000000000^65 ≤ 1902489588591^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508241269 10000000000 1902489588591 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875803193/5000000000 : ℝ)^81 ≤ (920999152659/3125000000000 : ℝ)^65 := by
    have hnat : (1875803193 : ℕ)^81*3125000000000^65 ≤ 920999152659^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875803193 5000000000 920999152659 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1535527149/5000000000 : ℝ)^81 ≤ (22965787394453/100000000000000 : ℝ)^65 := by
    have hnat : (1535527149 : ℕ)^81*100000000000000^65 ≤ 22965787394453^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535527149 5000000000 22965787394453 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508241269/10000000000 : ℝ), (-1875803193/5000000000 : ℝ), (-1535527149/5000000000 : ℝ)] ![(1902489588591/4000000000000 : ℝ), (920999152659/3125000000000 : ℝ), (22965787394453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508241269/10000000000 : ℝ)|^81 ≤ (1902489588591/4000000000000 : ℝ)^65
        have hw : |(5508241269/10000000000 : ℝ)|=(5508241269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1875803193/5000000000 : ℝ)|^81 ≤ (920999152659/3125000000000 : ℝ)^65
        have hw : |(-1875803193/5000000000 : ℝ)|=(1875803193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1535527149/5000000000 : ℝ)|^81 ≤ (22965787394453/100000000000000 : ℝ)^65
        have hw : |(-1535527149/5000000000 : ℝ)|=(1535527149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-62639053/5000000000 : ℝ)*x 0 + (-975170463/1250000000 : ℝ)*x 1 + (682399689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62639053/5000000000 : ℝ)^81 ≤ (53280691343/12500000000000 : ℝ)^65 := by
    have hnat : (62639053 : ℕ)^81*12500000000000^65 ≤ 53280691343^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62639053 5000000000 53280691343 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975170463/1250000000 : ℝ)^81 ≤ (14677695753859/20000000000000 : ℝ)^65 := by
    have hnat : (975170463 : ℕ)^81*20000000000000^65 ≤ 14677695753859^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975170463 1250000000 14677695753859 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682399689/2000000000 : ℝ)^81 ≤ (13092637842361/50000000000000 : ℝ)^65 := by
    have hnat : (682399689 : ℕ)^81*50000000000000^65 ≤ 13092637842361^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682399689 2000000000 13092637842361 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62639053/5000000000 : ℝ), (-975170463/1250000000 : ℝ), (682399689/2000000000 : ℝ)] ![(53280691343/12500000000000 : ℝ), (14677695753859/20000000000000 : ℝ), (13092637842361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62639053/5000000000 : ℝ)|^81 ≤ (53280691343/12500000000000 : ℝ)^65
        have hw : |(-62639053/5000000000 : ℝ)|=(62639053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975170463/1250000000 : ℝ)|^81 ≤ (14677695753859/20000000000000 : ℝ)^65
        have hw : |(-975170463/1250000000 : ℝ)|=(975170463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682399689/2000000000 : ℝ)|^81 ≤ (13092637842361/50000000000000 : ℝ)^65
        have hw : |(682399689/2000000000 : ℝ)|=(682399689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (762262527/2500000000 : ℝ)*x 0 + (5338284201/10000000000 : ℝ)*x 1 + (494657359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (762262527/2500000000 : ℝ)^81 ≤ (4552182659737/20000000000000 : ℝ)^65 := by
    have hnat : (762262527 : ℕ)^81*20000000000000^65 ≤ 4552182659737^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762262527 2500000000 4552182659737 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5338284201/10000000000 : ℝ)^81 ≤ (22870232164067/50000000000000 : ℝ)^65 := by
    have hnat : (5338284201 : ℕ)^81*50000000000000^65 ≤ 22870232164067^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338284201 10000000000 22870232164067 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494657359/1250000000 : ℝ)^81 ≤ (3937327794633/12500000000000 : ℝ)^65 := by
    have hnat : (494657359 : ℕ)^81*12500000000000^65 ≤ 3937327794633^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494657359 1250000000 3937327794633 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(762262527/2500000000 : ℝ), (5338284201/10000000000 : ℝ), (494657359/1250000000 : ℝ)] ![(4552182659737/20000000000000 : ℝ), (22870232164067/50000000000000 : ℝ), (3937327794633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(762262527/2500000000 : ℝ)|^81 ≤ (4552182659737/20000000000000 : ℝ)^65
        have hw : |(762262527/2500000000 : ℝ)|=(762262527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5338284201/10000000000 : ℝ)|^81 ≤ (22870232164067/50000000000000 : ℝ)^65
        have hw : |(5338284201/10000000000 : ℝ)|=(5338284201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(494657359/1250000000 : ℝ)|^81 ≤ (3937327794633/12500000000000 : ℝ)^65
        have hw : |(494657359/1250000000 : ℝ)|=(494657359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2349331633/5000000000 : ℝ)*x 0 + (-3313687891/10000000000 : ℝ)*x 1 + (-4379138071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2349331633/5000000000 : ℝ)^81 ≤ (487685173837/1250000000000 : ℝ)^65 := by
    have hnat : (2349331633 : ℕ)^81*1250000000000^65 ≤ 487685173837^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349331633 5000000000 487685173837 1250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3313687891/10000000000 : ℝ)^81 ≤ (25248434556673/100000000000000 : ℝ)^65 := by
    have hnat : (3313687891 : ℕ)^81*100000000000000^65 ≤ 25248434556673^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3313687891 10000000000 25248434556673 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4379138071/10000000000 : ℝ)^81 ≤ (17868375759049/50000000000000 : ℝ)^65 := by
    have hnat : (4379138071 : ℕ)^81*50000000000000^65 ≤ 17868375759049^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379138071 10000000000 17868375759049 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2349331633/5000000000 : ℝ), (-3313687891/10000000000 : ℝ), (-4379138071/10000000000 : ℝ)] ![(487685173837/1250000000000 : ℝ), (25248434556673/100000000000000 : ℝ), (17868375759049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2349331633/5000000000 : ℝ)|^81 ≤ (487685173837/1250000000000 : ℝ)^65
        have hw : |(2349331633/5000000000 : ℝ)|=(2349331633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3313687891/10000000000 : ℝ)|^81 ≤ (25248434556673/100000000000000 : ℝ)^65
        have hw : |(-3313687891/10000000000 : ℝ)|=(3313687891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4379138071/10000000000 : ℝ)|^81 ≤ (17868375759049/50000000000000 : ℝ)^65
        have hw : |(-4379138071/10000000000 : ℝ)|=(4379138071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5065184791/10000000000 : ℝ)*x 0 + (13268571/10000000000 : ℝ)*x 1 + (39882011/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5065184791/10000000000 : ℝ)^81 ≤ (42843041016701/100000000000000 : ℝ)^65 := by
    have hnat : (5065184791 : ℕ)^81*100000000000000^65 ≤ 42843041016701^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065184791 10000000000 42843041016701 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13268571/10000000000 : ℝ)^81 ≤ (25977434103/100000000000000 : ℝ)^65 := by
    have hnat : (13268571 : ℕ)^81*100000000000000^65 ≤ 25977434103^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13268571 10000000000 25977434103 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39882011/62500000 : ℝ)^81 ≤ (14282745384999/25000000000000 : ℝ)^65 := by
    have hnat : (39882011 : ℕ)^81*25000000000000^65 ≤ 14282745384999^65*62500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39882011 62500000 14282745384999 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5065184791/10000000000 : ℝ), (13268571/10000000000 : ℝ), (39882011/62500000 : ℝ)] ![(42843041016701/100000000000000 : ℝ), (25977434103/100000000000000 : ℝ), (14282745384999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5065184791/10000000000 : ℝ)|^81 ≤ (42843041016701/100000000000000 : ℝ)^65
        have hw : |(5065184791/10000000000 : ℝ)|=(5065184791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13268571/10000000000 : ℝ)|^81 ≤ (25977434103/100000000000000 : ℝ)^65
        have hw : |(13268571/10000000000 : ℝ)|=(13268571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39882011/62500000 : ℝ)|^81 ≤ (14282745384999/25000000000000 : ℝ)^65
        have hw : |(39882011/62500000 : ℝ)|=(39882011/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (11919/5000000000 : ℝ)*x 0 + (-4651329363/10000000000 : ℝ)*x 1 + (3383789909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11919/5000000000 : ℝ)^81 ≤ (4922471/50000000000000 : ℝ)^65 := by
    have hnat : (11919 : ℕ)^81*50000000000000^65 ≤ 4922471^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11919 5000000000 4922471 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4651329363/10000000000 : ℝ)^81 ≤ (19262822398337/50000000000000 : ℝ)^65 := by
    have hnat : (4651329363 : ℕ)^81*50000000000000^65 ≤ 19262822398337^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651329363 10000000000 19262822398337 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3383789909/5000000000 : ℝ)^81 ≤ (61474345348299/100000000000000 : ℝ)^65 := by
    have hnat : (3383789909 : ℕ)^81*100000000000000^65 ≤ 61474345348299^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383789909 5000000000 61474345348299 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11919/5000000000 : ℝ), (-4651329363/10000000000 : ℝ), (3383789909/5000000000 : ℝ)] ![(4922471/50000000000000 : ℝ), (19262822398337/50000000000000 : ℝ), (61474345348299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11919/5000000000 : ℝ)|^81 ≤ (4922471/50000000000000 : ℝ)^65
        have hw : |(11919/5000000000 : ℝ)|=(11919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4651329363/10000000000 : ℝ)|^81 ≤ (19262822398337/50000000000000 : ℝ)^65
        have hw : |(-4651329363/10000000000 : ℝ)|=(4651329363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3383789909/5000000000 : ℝ)|^81 ≤ (61474345348299/100000000000000 : ℝ)^65
        have hw : |(3383789909/5000000000 : ℝ)|=(3383789909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3041385729/10000000000 : ℝ)*x 0 + (927332817/2000000000 : ℝ)*x 1 + (938209493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3041385729/10000000000 : ℝ)^81 ≤ (1418102372491/6250000000000 : ℝ)^65 := by
    have hnat : (3041385729 : ℕ)^81*6250000000000^65 ≤ 1418102372491^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3041385729 10000000000 1418102372491 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (927332817/2000000000 : ℝ)^81 ≤ (38374335333681/100000000000000 : ℝ)^65 := by
    have hnat : (927332817 : ℕ)^81*100000000000000^65 ≤ 38374335333681^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927332817 2000000000 38374335333681 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938209493/2000000000 : ℝ)^81 ≤ (38936026685147/100000000000000 : ℝ)^65 := by
    have hnat : (938209493 : ℕ)^81*100000000000000^65 ≤ 38936026685147^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938209493 2000000000 38936026685147 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3041385729/10000000000 : ℝ), (927332817/2000000000 : ℝ), (938209493/2000000000 : ℝ)] ![(1418102372491/6250000000000 : ℝ), (38374335333681/100000000000000 : ℝ), (38936026685147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3041385729/10000000000 : ℝ)|^81 ≤ (1418102372491/6250000000000 : ℝ)^65
        have hw : |(3041385729/10000000000 : ℝ)|=(3041385729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(927332817/2000000000 : ℝ)|^81 ≤ (38374335333681/100000000000000 : ℝ)^65
        have hw : |(927332817/2000000000 : ℝ)|=(927332817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(938209493/2000000000 : ℝ)|^81 ≤ (38936026685147/100000000000000 : ℝ)^65
        have hw : |(938209493/2000000000 : ℝ)|=(938209493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6883314181/10000000000 : ℝ)*x 0 + (-2571872209/10000000000 : ℝ)*x 1 + (-65389213/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6883314181/10000000000 : ℝ)^81 ≤ (31393580512929/50000000000000 : ℝ)^65 := by
    have hnat : (6883314181 : ℕ)^81*50000000000000^65 ≤ 31393580512929^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6883314181 10000000000 31393580512929 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571872209/10000000000 : ℝ)^81 ≤ (1841111130647/10000000000000 : ℝ)^65 := by
    have hnat : (2571872209 : ℕ)^81*10000000000000^65 ≤ 1841111130647^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571872209 10000000000 1841111130647 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65389213/250000000 : ℝ)^81 ≤ (3760345530419/20000000000000 : ℝ)^65 := by
    have hnat : (65389213 : ℕ)^81*20000000000000^65 ≤ 3760345530419^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65389213 250000000 3760345530419 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6883314181/10000000000 : ℝ), (-2571872209/10000000000 : ℝ), (-65389213/250000000 : ℝ)] ![(31393580512929/50000000000000 : ℝ), (1841111130647/10000000000000 : ℝ), (3760345530419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6883314181/10000000000 : ℝ)|^81 ≤ (31393580512929/50000000000000 : ℝ)^65
        have hw : |(6883314181/10000000000 : ℝ)|=(6883314181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2571872209/10000000000 : ℝ)|^81 ≤ (1841111130647/10000000000000 : ℝ)^65
        have hw : |(-2571872209/10000000000 : ℝ)|=(2571872209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65389213/250000000 : ℝ)|^81 ≤ (3760345530419/20000000000000 : ℝ)^65
        have hw : |(-65389213/250000000 : ℝ)|=(65389213/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2066686203/2500000000 : ℝ)*x 0 + (-157849711/10000000000 : ℝ)*x 1 + (2808787501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066686203/2500000000 : ℝ)^81 ≤ (39441744261593/50000000000000 : ℝ)^65 := by
    have hnat : (2066686203 : ℕ)^81*50000000000000^65 ≤ 39441744261593^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066686203 2500000000 39441744261593 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157849711/10000000000 : ℝ)^81 ≤ (142126342217/25000000000000 : ℝ)^65 := by
    have hnat : (157849711 : ℕ)^81*25000000000000^65 ≤ 142126342217^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157849711 10000000000 142126342217 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2808787501/10000000000 : ℝ)^81 ≤ (20548006103337/100000000000000 : ℝ)^65 := by
    have hnat : (2808787501 : ℕ)^81*100000000000000^65 ≤ 20548006103337^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808787501 10000000000 20548006103337 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066686203/2500000000 : ℝ), (-157849711/10000000000 : ℝ), (2808787501/10000000000 : ℝ)] ![(39441744261593/50000000000000 : ℝ), (142126342217/25000000000000 : ℝ), (20548006103337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066686203/2500000000 : ℝ)|^81 ≤ (39441744261593/50000000000000 : ℝ)^65
        have hw : |(2066686203/2500000000 : ℝ)|=(2066686203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157849711/10000000000 : ℝ)|^81 ≤ (142126342217/25000000000000 : ℝ)^65
        have hw : |(-157849711/10000000000 : ℝ)|=(157849711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2808787501/10000000000 : ℝ)|^81 ≤ (20548006103337/100000000000000 : ℝ)^65
        have hw : |(2808787501/10000000000 : ℝ)|=(2808787501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-12688979/312500000 : ℝ)*x 0 + (-8337469999/10000000000 : ℝ)*x 1 + (1286955573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12688979/312500000 : ℝ)^81 ≤ (369064646431/20000000000000 : ℝ)^65 := by
    have hnat : (12688979 : ℕ)^81*20000000000000^65 ≤ 369064646431^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12688979 312500000 369064646431 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8337469999/10000000000 : ℝ)^81 ≤ (79725374787529/100000000000000 : ℝ)^65 := by
    have hnat : (8337469999 : ℕ)^81*100000000000000^65 ≤ 79725374787529^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8337469999 10000000000 79725374787529 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286955573/5000000000 : ℝ)^81 ≤ (1151831372893/6250000000000 : ℝ)^65 := by
    have hnat : (1286955573 : ℕ)^81*6250000000000^65 ≤ 1151831372893^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286955573 5000000000 1151831372893 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12688979/312500000 : ℝ), (-8337469999/10000000000 : ℝ), (1286955573/5000000000 : ℝ)] ![(369064646431/20000000000000 : ℝ), (79725374787529/100000000000000 : ℝ), (1151831372893/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12688979/312500000 : ℝ)|^81 ≤ (369064646431/20000000000000 : ℝ)^65
        have hw : |(-12688979/312500000 : ℝ)|=(12688979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8337469999/10000000000 : ℝ)|^81 ≤ (79725374787529/100000000000000 : ℝ)^65
        have hw : |(-8337469999/10000000000 : ℝ)|=(8337469999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286955573/5000000000 : ℝ)|^81 ≤ (1151831372893/6250000000000 : ℝ)^65
        have hw : |(1286955573/5000000000 : ℝ)|=(1286955573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6715525671/10000000000 : ℝ)*x 0 + (3148660139/10000000000 : ℝ)*x 1 + (1115585671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6715525671/10000000000 : ℝ)^81 ≤ (30442835307291/50000000000000 : ℝ)^65 := by
    have hnat : (6715525671 : ℕ)^81*50000000000000^65 ≤ 30442835307291^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6715525671 10000000000 30442835307291 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3148660139/10000000000 : ℝ)^81 ≤ (23691225044251/100000000000000 : ℝ)^65 := by
    have hnat : (3148660139 : ℕ)^81*100000000000000^65 ≤ 23691225044251^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3148660139 10000000000 23691225044251 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115585671/5000000000 : ℝ)^81 ≤ (15423104330943/100000000000000 : ℝ)^65 := by
    have hnat : (1115585671 : ℕ)^81*100000000000000^65 ≤ 15423104330943^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115585671 5000000000 15423104330943 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6715525671/10000000000 : ℝ), (3148660139/10000000000 : ℝ), (1115585671/5000000000 : ℝ)] ![(30442835307291/50000000000000 : ℝ), (23691225044251/100000000000000 : ℝ), (15423104330943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6715525671/10000000000 : ℝ)|^81 ≤ (30442835307291/50000000000000 : ℝ)^65
        have hw : |(6715525671/10000000000 : ℝ)|=(6715525671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3148660139/10000000000 : ℝ)|^81 ≤ (23691225044251/100000000000000 : ℝ)^65
        have hw : |(3148660139/10000000000 : ℝ)|=(3148660139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1115585671/5000000000 : ℝ)|^81 ≤ (15423104330943/100000000000000 : ℝ)^65
        have hw : |(1115585671/5000000000 : ℝ)|=(1115585671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2212573663/10000000000 : ℝ)*x 0 + (-6950132383/10000000000 : ℝ)*x 1 + (-575784721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212573663/10000000000 : ℝ)^81 ≤ (3052613305889/20000000000000 : ℝ)^65 := by
    have hnat : (2212573663 : ℕ)^81*20000000000000^65 ≤ 3052613305889^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212573663 10000000000 3052613305889 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6950132383/10000000000 : ℝ)^81 ≤ (3971724193973/6250000000000 : ℝ)^65 := by
    have hnat : (6950132383 : ℕ)^81*6250000000000^65 ≤ 3971724193973^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6950132383 10000000000 3971724193973 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575784721/2000000000 : ℝ)^81 ≤ (10594673176403/50000000000000 : ℝ)^65 := by
    have hnat : (575784721 : ℕ)^81*50000000000000^65 ≤ 10594673176403^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575784721 2000000000 10594673176403 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2212573663/10000000000 : ℝ), (-6950132383/10000000000 : ℝ), (-575784721/2000000000 : ℝ)] ![(3052613305889/20000000000000 : ℝ), (3971724193973/6250000000000 : ℝ), (10594673176403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2212573663/10000000000 : ℝ)|^81 ≤ (3052613305889/20000000000000 : ℝ)^65
        have hw : |(2212573663/10000000000 : ℝ)|=(2212573663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6950132383/10000000000 : ℝ)|^81 ≤ (3971724193973/6250000000000 : ℝ)^65
        have hw : |(-6950132383/10000000000 : ℝ)|=(6950132383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575784721/2000000000 : ℝ)|^81 ≤ (10594673176403/50000000000000 : ℝ)^65
        have hw : |(-575784721/2000000000 : ℝ)|=(575784721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s0_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8236414949/10000000000 : ℝ)*x 0 + (1933/1000000000 : ℝ)*x 1 + (1455121999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8236414949/10000000000 : ℝ)^81 ≤ (78522995093547/100000000000000 : ℝ)^65 := by
    have hnat : (8236414949 : ℕ)^81*100000000000000^65 ≤ 78522995093547^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8236414949 10000000000 78522995093547 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933/1000000000 : ℝ)^81 ≤ (7581687/100000000000000 : ℝ)^65 := by
    have hnat : (1933 : ℕ)^81*100000000000000^65 ≤ 7581687^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933 1000000000 7581687 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455121999/5000000000 : ℝ)^81 ≤ (21476997311877/100000000000000 : ℝ)^65 := by
    have hnat : (1455121999 : ℕ)^81*100000000000000^65 ≤ 21476997311877^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455121999 5000000000 21476997311877 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8236414949/10000000000 : ℝ), (1933/1000000000 : ℝ), (1455121999/5000000000 : ℝ)] ![(78522995093547/100000000000000 : ℝ), (7581687/100000000000000 : ℝ), (21476997311877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8236414949/10000000000 : ℝ)|^81 ≤ (78522995093547/100000000000000 : ℝ)^65
        have hw : |(8236414949/10000000000 : ℝ)|=(8236414949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1933/1000000000 : ℝ)|^81 ≤ (7581687/100000000000000 : ℝ)^65
        have hw : |(1933/1000000000 : ℝ)|=(1933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1455121999/5000000000 : ℝ)|^81 ≤ (21476997311877/100000000000000 : ℝ)^65
        have hw : |(1455121999/5000000000 : ℝ)|=(1455121999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1671108397/10000000000 : ℝ)*x 0 + (-5183030933/10000000000 : ℝ)*x 1 + (66039899/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1671108397/10000000000 : ℝ)^81 ≤ (10758314119537/100000000000000 : ℝ)^65 := by
    have hnat : (1671108397 : ℕ)^81*100000000000000^65 ≤ 10758314119537^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671108397 10000000000 10758314119537 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183030933/10000000000 : ℝ)^81 ≤ (11022180384933/25000000000000 : ℝ)^65 := by
    have hnat : (5183030933 : ℕ)^81*25000000000000^65 ≤ 11022180384933^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183030933 10000000000 11022180384933 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66039899/125000000 : ℝ)^81 ≤ (22576482163493/50000000000000 : ℝ)^65 := by
    have hnat : (66039899 : ℕ)^81*50000000000000^65 ≤ 22576482163493^65*125000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66039899 125000000 22576482163493 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1671108397/10000000000 : ℝ), (-5183030933/10000000000 : ℝ), (66039899/125000000 : ℝ)] ![(10758314119537/100000000000000 : ℝ), (11022180384933/25000000000000 : ℝ), (22576482163493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1671108397/10000000000 : ℝ)|^81 ≤ (10758314119537/100000000000000 : ℝ)^65
        have hw : |(-1671108397/10000000000 : ℝ)|=(1671108397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5183030933/10000000000 : ℝ)|^81 ≤ (11022180384933/25000000000000 : ℝ)^65
        have hw : |(-5183030933/10000000000 : ℝ)|=(5183030933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66039899/125000000 : ℝ)|^81 ≤ (22576482163493/50000000000000 : ℝ)^65
        have hw : |(66039899/125000000 : ℝ)|=(66039899/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4997047799/10000000000 : ℝ)*x 0 + (3959168467/10000000000 : ℝ)*x 1 + (107183731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4997047799/10000000000 : ℝ)^81 ≤ (8425208737703/20000000000000 : ℝ)^65 := by
    have hnat : (4997047799 : ℕ)^81*20000000000000^65 ≤ 8425208737703^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997047799 10000000000 8425208737703 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3959168467/10000000000 : ℝ)^81 ≤ (6303512958527/20000000000000 : ℝ)^65 := by
    have hnat : (3959168467 : ℕ)^81*20000000000000^65 ≤ 6303512958527^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3959168467 10000000000 6303512958527 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107183731/312500000 : ℝ)^81 ≤ (1647274469103/6250000000000 : ℝ)^65 := by
    have hnat : (107183731 : ℕ)^81*6250000000000^65 ≤ 1647274469103^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107183731 312500000 1647274469103 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4997047799/10000000000 : ℝ), (3959168467/10000000000 : ℝ), (107183731/312500000 : ℝ)] ![(8425208737703/20000000000000 : ℝ), (6303512958527/20000000000000 : ℝ), (1647274469103/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4997047799/10000000000 : ℝ)|^81 ≤ (8425208737703/20000000000000 : ℝ)^65
        have hw : |(4997047799/10000000000 : ℝ)|=(4997047799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3959168467/10000000000 : ℝ)|^81 ≤ (6303512958527/20000000000000 : ℝ)^65
        have hw : |(3959168467/10000000000 : ℝ)|=(3959168467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107183731/312500000 : ℝ)|^81 ≤ (1647274469103/6250000000000 : ℝ)^65
        have hw : |(107183731/312500000 : ℝ)|=(107183731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (76094521/156250000 : ℝ)*x 0 + (-4069197403/10000000000 : ℝ)*x 1 + (-86359293/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76094521/156250000 : ℝ)^81 ≤ (40796085821231/100000000000000 : ℝ)^65 := by
    have hnat : (76094521 : ℕ)^81*100000000000000^65 ≤ 40796085821231^65*156250000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76094521 156250000 40796085821231 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4069197403/10000000000 : ℝ)^81 ≤ (32612781269783/100000000000000 : ℝ)^65 := by
    have hnat : (4069197403 : ℕ)^81*100000000000000^65 ≤ 32612781269783^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069197403 10000000000 32612781269783 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86359293/250000000 : ℝ)^81 ≤ (26591132895573/100000000000000 : ℝ)^65 := by
    have hnat : (86359293 : ℕ)^81*100000000000000^65 ≤ 26591132895573^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86359293 250000000 26591132895573 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76094521/156250000 : ℝ), (-4069197403/10000000000 : ℝ), (-86359293/250000000 : ℝ)] ![(40796085821231/100000000000000 : ℝ), (32612781269783/100000000000000 : ℝ), (26591132895573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76094521/156250000 : ℝ)|^81 ≤ (40796085821231/100000000000000 : ℝ)^65
        have hw : |(76094521/156250000 : ℝ)|=(76094521/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4069197403/10000000000 : ℝ)|^81 ≤ (32612781269783/100000000000000 : ℝ)^65
        have hw : |(-4069197403/10000000000 : ℝ)|=(4069197403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86359293/250000000 : ℝ)|^81 ≤ (26591132895573/100000000000000 : ℝ)^65
        have hw : |(-86359293/250000000 : ℝ)|=(86359293/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319047_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (380394283/625000000 : ℝ)*x 0 + (-320138473/2000000000 : ℝ)*x 1 + (4399403307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (380394283/625000000 : ℝ)^81 ≤ (53860683789029/100000000000000 : ℝ)^65 := by
    have hnat : (380394283 : ℕ)^81*100000000000000^65 ≤ 53860683789029^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380394283 625000000 53860683789029 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320138473/2000000000 : ℝ)^81 ≤ (5098180417393/50000000000000 : ℝ)^65 := by
    have hnat : (320138473 : ℕ)^81*50000000000000^65 ≤ 5098180417393^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320138473 2000000000 5098180417393 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399403307/10000000000 : ℝ)^81 ≤ (8985738841063/25000000000000 : ℝ)^65 := by
    have hnat : (4399403307 : ℕ)^81*25000000000000^65 ≤ 8985738841063^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399403307 10000000000 8985738841063 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(380394283/625000000 : ℝ), (-320138473/2000000000 : ℝ), (4399403307/10000000000 : ℝ)] ![(53860683789029/100000000000000 : ℝ), (5098180417393/50000000000000 : ℝ), (8985738841063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(380394283/625000000 : ℝ)|^81 ≤ (53860683789029/100000000000000 : ℝ)^65
        have hw : |(380394283/625000000 : ℝ)|=(380394283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320138473/2000000000 : ℝ)|^81 ≤ (5098180417393/50000000000000 : ℝ)^65
        have hw : |(-320138473/2000000000 : ℝ)|=(320138473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4399403307/10000000000 : ℝ)|^81 ≤ (8985738841063/25000000000000 : ℝ)^65
        have hw : |(4399403307/10000000000 : ℝ)|=(4399403307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319047 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-61286763/2000000000 : ℝ)*X 0 0+(-1543069971/2500000000 : ℝ)*X 0 1+(2582147183/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5125825163/10000000000 : ℝ)*X 1 0+(753846979/2000000000 : ℝ)*X 1 1+(348364133/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5508241269/10000000000 : ℝ)*X 2 0+(-1875803193/5000000000 : ℝ)*X 2 1+(-1535527149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-62639053/5000000000 : ℝ)*X 0 0+(-975170463/1250000000 : ℝ)*X 0 1+(682399689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((762262527/2500000000 : ℝ)*X 1 0+(5338284201/10000000000 : ℝ)*X 1 1+(494657359/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2349331633/5000000000 : ℝ)*X 2 0+(-3313687891/10000000000 : ℝ)*X 2 1+(-4379138071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5065184791/10000000000 : ℝ)*X 0 0+(13268571/10000000000 : ℝ)*X 0 1+(39882011/62500000 : ℝ)*X 0 2+(5065184791/10000000000 : ℝ)*X 1 0+(13268571/10000000000 : ℝ)*X 1 1+(39882011/62500000 : ℝ)*X 1 2+(5065184791/10000000000 : ℝ)*X 2 0+(13268571/10000000000 : ℝ)*X 2 1+(39882011/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((11919/5000000000 : ℝ)*X 0 0+(-4651329363/10000000000 : ℝ)*X 0 1+(3383789909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3041385729/10000000000 : ℝ)*X 1 0+(927332817/2000000000 : ℝ)*X 1 1+(938209493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6883314181/10000000000 : ℝ)*X 2 0+(-2571872209/10000000000 : ℝ)*X 2 1+(-65389213/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2066686203/2500000000 : ℝ)*X 0 0+(-157849711/10000000000 : ℝ)*X 0 1+(2808787501/10000000000 : ℝ)*X 0 2+(2066686203/2500000000 : ℝ)*X 1 0+(-157849711/10000000000 : ℝ)*X 1 1+(2808787501/10000000000 : ℝ)*X 1 2+(2066686203/2500000000 : ℝ)*X 2 0+(-157849711/10000000000 : ℝ)*X 2 1+(2808787501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-12688979/312500000 : ℝ)*X 0 0+(-8337469999/10000000000 : ℝ)*X 0 1+(1286955573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6715525671/10000000000 : ℝ)*X 1 0+(3148660139/10000000000 : ℝ)*X 1 1+(1115585671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2212573663/10000000000 : ℝ)*X 2 0+(-6950132383/10000000000 : ℝ)*X 2 1+(-575784721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8236414949/10000000000 : ℝ)*X 0 0+(1933/1000000000 : ℝ)*X 0 1+(1455121999/5000000000 : ℝ)*X 0 2+(8236414949/10000000000 : ℝ)*X 1 0+(1933/1000000000 : ℝ)*X 1 1+(1455121999/5000000000 : ℝ)*X 1 2+(8236414949/10000000000 : ℝ)*X 2 0+(1933/1000000000 : ℝ)*X 2 1+(1455121999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((62331/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62331/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (92200276032941737772211/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97626895621/250000000000 : ℝ)*(base3) + (228201102391/200000000000 : ℝ)*(base7) + (72406658353/250000000000 : ℝ)*(base50) + (1291229/1000000000000 : ℝ)*(base54) + (2141170805341/1000000000000 : ℝ)*(major_s0_0) + (2141170805341/1000000000000 : ℝ)*(major_s0_1) + (16727886829/7812500000 : ℝ)*(major_s0_2) + (2155427/125000000000 : ℝ)*(sp_s0_0) + (2477539346221/1000000000000 : ℝ)*(sp_s0_7) + (2868005040181/1000000000000 : ℝ)*(sp_s0_8) + (2477531618909/1000000000000 : ℝ)*(sp_s0_9) + (381459696471/200000000000 : ℝ)*(sp_s0_13) + (2956597/50000000000 : ℝ)*(sp_s0_15) + (23679499/1000000000000 : ℝ)*(sp_s0_23) + (72300115257/62500000000 : ℝ)*(f.failure) + (619389147409/250000000000 : ℝ)*(f.sum) + (5986609378909263/10000000000000000000000000000 : ℝ)*base62 + (58979074771301/156250000000000000000000000 : ℝ)*base65 + (1637556311423973/10000000000000000000000000000 : ℝ)*base66 + (73312562514443/156250000000000000000000000 : ℝ)*base68 + (4364129475621647/10000000000000000000000000000 : ℝ)*base70 + (7385803642423973/10000000000000000000000000000 : ℝ)*base72 + (7952323087984911/10000000000000000000000000000 : ℝ)*base74 + (918753679015089/10000000000000000000000000000 : ℝ)*base77 + (1709265906576027/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (523/1562500000000000 : ℝ)*base86 + (523/1562500000000000 : ℝ)*base88 + (523/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6881/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-6881/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40271944576690513852191/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209786123603/250000000000 : ℝ)*(base7) + (540497361727/1000000000000 : ℝ)*(base40) + (2275203/1000000000000 : ℝ)*(base49) + (109426422757/1000000000000 : ℝ)*(base59) + (2109583302331/1000000000000 : ℝ)*(major_s0_0) + (2109583302331/1000000000000 : ℝ)*(major_s0_1) + (2109583302331/1000000000000 : ℝ)*(major_s0_2) + (15272363/500000000000 : ℝ)*(sp_s0_1) + (2624123/1000000000000 : ℝ)*(sp_s0_9) + (1301438786063/500000000000 : ℝ)*(sp_s0_14) + (13014235137/5000000000 : ℝ)*(sp_s0_15) + (2602874948003/1000000000000 : ℝ)*(sp_s0_16) + (989270974689/500000000000 : ℝ)*(sp_s0_20) + (338734393/1000000000000 : ℝ)*(sp_s0_27) + (1139736189359/1000000000000 : ℝ)*(f.failure) + (1301438786063/500000000000 : ℝ)*(f.sum) + (473820861794201/5000000000000000000000000000 : ℝ)*base62 + (2677259494315443/10000000000000000000000000000 : ℝ)*base64 + (5452008960315443/10000000000000000000000000000 : ℝ)*base66 + (3848249952294201/10000000000000000000000000000 : ℝ)*base68 + (2318626280902411/2500000000000000000000000000 : ℝ)*base70 + (1842277527684557/10000000000000000000000000000 : ℝ)*base73 + (3321631275294201/10000000000000000000000000000 : ℝ)*base74 + (2291310833294201/10000000000000000000000000000 : ℝ)*base76 + (35694050184557/5000000000000000000000000000 : ℝ)*base79 + (57373/50000000000000000 : ℝ)*base87 + (57373/50000000000000000 : ℝ)*base89 + (57373/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36183/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36183/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30441168443319676429713/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18280349873/500000000000 : ℝ)*(base3) + (47084050123/40000000000 : ℝ)*(base7) + (2305527/1000000000000 : ℝ)*(base34) + (172713450123/1000000000000 : ℝ)*(base40) + (4408801/1000000000000 : ℝ)*(base43) + (57705484547/500000000000 : ℝ)*(base50) + (441590160879/250000000000 : ℝ)*(major_s0_0) + (883179270121/500000000000 : ℝ)*(major_s0_1) + (1766362949043/1000000000000 : ℝ)*(major_s0_2) + (1143/250000000 : ℝ)*(sp_s0_2) + (1909935460017/1000000000000 : ℝ)*(sp_s0_21) + (194650287409/100000000000 : ℝ)*(sp_s0_22) + (238741649193/125000000000 : ℝ)*(sp_s0_23) + (2094844140507/1000000000000 : ℝ)*(sp_s0_27) + (190861178541/200000000000 : ℝ)*(f.failure) + (238742771793/125000000000 : ℝ)*(f.sum) + (367704856593253/2000000000000000000000000000 : ℝ)*base63 + (1560849953719979/10000000000000000000000000000 : ℝ)*base64 + (627928628920687/5000000000000000000000000000 : ℝ)*base67 + (869555969346847/10000000000000000000000000000 : ℝ)*base69 + (767720468967437/2000000000000000000000000000 : ℝ)*base71 + (340240333836313/2500000000000000000000000000 : ℝ)*base73 + (505190266309709/5000000000000000000000000000 : ℝ)*base75 + (860401958389291/2500000000000000000000000000 : ℝ)*base77 + (2838057019406687/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (3927/10000000000000000 : ℝ)*base87 + (3927/10000000000000000 : ℝ)*base89 + (3927/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (62331/100000 : ℝ) ^ (79/16 : ℝ) ≤ (9690617830135341103/100000000000000000000 : ℝ) := by
    have hpowers : (62331/100000 : ℝ)^79 ≤ (9690617830135341103/100000000000000000000 : ℝ)^16 := by
      have hnat : (62331 : ℕ)^79*100000000000000000000^16 ≤ 9690617830135341103^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62331 100000 9690617830135341103 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62331/100000 : ℝ)) (X := (9690617830135341103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (109690617830135341103/100000000000000000000 : ℝ) ≤ (5094547264606479/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (109690617830135341103/100000000000000000000 : ℝ)^16 ≤ (5094547264606479/5000000000000000 : ℝ)^79 := by
      have hnat : (109690617830135341103 : ℕ)^16*5000000000000000^79 ≤ 5094547264606479^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109690617830135341103 100000000000000000000 5094547264606479 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5094547264606479/5000000000000000 : ℝ)) (X := (109690617830135341103/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (59690617830135341103/50000000000000000000 : ℝ) ≤ (10365302685896353/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (59690617830135341103/50000000000000000000 : ℝ)^16 ≤ (10365302685896353/10000000000000000 : ℝ)^79 := by
      have hnat : (59690617830135341103 : ℕ)^16*10000000000000000^79 ≤ 10365302685896353^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59690617830135341103 50000000000000000000 10365302685896353 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10365302685896353/10000000000000000 : ℝ)) (X := (59690617830135341103/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(94547264606479/3116550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(35241631336679/1246620000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (62331/100000 : ℝ)) (alpha := (94547264606479/3116550000000000 : ℝ)) (beta := (35241631336679/1246620000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62331/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(94547264606479/3116550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(35241631336679/1246620000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6881/12500 : ℝ) ^ (79/16 : ℝ) ≤ (1049400757377909067/20000000000000000000 : ℝ) := by
    have hpowers : (6881/12500 : ℝ)^79 ≤ (1049400757377909067/20000000000000000000 : ℝ)^16 := by
      have hnat : (6881 : ℕ)^79*20000000000000000000^16 ≤ 1049400757377909067^16*12500^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6881 12500 1049400757377909067 20000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6881/12500 : ℝ)) (X := (1049400757377909067/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (21049400757377909067/20000000000000000000 : ℝ) ≤ (5052056277361727/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (21049400757377909067/20000000000000000000 : ℝ)^16 ≤ (5052056277361727/5000000000000000 : ℝ)^79 := by
      have hnat : (21049400757377909067 : ℕ)^16*5000000000000000^79 ≤ 5052056277361727^79*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21049400757377909067 20000000000000000000 5052056277361727 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052056277361727/5000000000000000 : ℝ)) (X := (21049400757377909067/20000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11049400757377909067/10000000000000000000 : ℝ) ≤ (159440074792733/156250000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (11049400757377909067/10000000000000000000 : ℝ)^16 ≤ (159440074792733/156250000000000 : ℝ)^79 := by
      have hnat : (11049400757377909067 : ℕ)^16*156250000000000^79 ≤ 159440074792733^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11049400757377909067 10000000000000000000 159440074792733 156250000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (159440074792733/156250000000000 : ℝ)) (X := (11049400757377909067/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(52056277361727/2752400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(50026116005729/2752400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (6881/12500 : ℝ)) (alpha := (52056277361727/2752400000000000 : ℝ)) (beta := (50026116005729/2752400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6881/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(52056277361727/2752400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(50026116005729/2752400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36183/50000 : ℝ) ^ (79/16 : ℝ) ≤ (20251254369934297421/100000000000000000000 : ℝ) := by
    have hpowers : (36183/50000 : ℝ)^79 ≤ (20251254369934297421/100000000000000000000 : ℝ)^16 := by
      have hnat : (36183 : ℕ)^79*100000000000000000000^16 ≤ 20251254369934297421^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36183 50000 20251254369934297421 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36183/50000 : ℝ)) (X := (20251254369934297421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (120251254369934297421/100000000000000000000 : ℝ) ≤ (324392424225739/312500000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (120251254369934297421/100000000000000000000 : ℝ)^16 ≤ (324392424225739/312500000000000 : ℝ)^79 := by
      have hnat : (120251254369934297421 : ℕ)^16*312500000000000^79 ≤ 324392424225739^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120251254369934297421 100000000000000000000 324392424225739 312500000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (324392424225739/312500000000000 : ℝ)) (X := (120251254369934297421/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (70251254369934297421/50000000000000000000 : ℝ) ≤ (2678247499946107/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (70251254369934297421/50000000000000000000 : ℝ)^16 ≤ (2678247499946107/2500000000000000 : ℝ)^79 := by
      have hnat : (70251254369934297421 : ℕ)^16*2500000000000000^79 ≤ 2678247499946107^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70251254369934297421 50000000000000000000 2678247499946107 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2678247499946107/2500000000000000 : ℝ)) (X := (70251254369934297421/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11892424225739/226143750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16621621228039/361830000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (36183/50000 : ℝ)) (alpha := (11892424225739/226143750000000 : ℝ)) (beta := (16621621228039/361830000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36183/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11892424225739/226143750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16621621228039/361830000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1671108397/10000000000 : ℝ)*X 0 0+(-5183030933/10000000000 : ℝ)*X 0 1+(66039899/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4997047799/10000000000 : ℝ)*X 1 0+(3959168467/10000000000 : ℝ)*X 1 1+(107183731/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((76094521/156250000 : ℝ)*X 2 0+(-4069197403/10000000000 : ℝ)*X 2 1+(-86359293/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((380394283/625000000 : ℝ)*X 0 0+(-320138473/2000000000 : ℝ)*X 0 1+(4399403307/10000000000 : ℝ)*X 0 2+(380394283/625000000 : ℝ)*X 1 0+(-320138473/2000000000 : ℝ)*X 1 1+(4399403307/10000000000 : ℝ)*X 1 2+(380394283/625000000 : ℝ)*X 2 0+(-320138473/2000000000 : ℝ)*X 2 1+(4399403307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-2830215525452911474072074606703521/351901918930000000000000000000000 : ℝ) := by norm_num
    linear_combination (3203/40000000000 : ℝ)*(base5) + (14333/200000000000 : ℝ)*(base10) + (166253/1000000000000 : ℝ)*(base21) + (46611/1000000000000 : ℝ)*(base27) + (11093/250000000000 : ℝ)*(base39) + (27190873359/50000000000 : ℝ)*(base40) + (14141771973/500000000000 : ℝ)*(base50) + (216336929171/1000000000000 : ℝ)*(base59) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (2680875264333/1000000000000 : ℝ)*(sp_s1_0) + (1340437667999/500000000000 : ℝ)*(sp_s1_1) + (2680875249821/1000000000000 : ℝ)*(sp_s1_2) + (499999936657/500000000000 : ℝ)*(sp_s1_6) + (1340437667999/500000000000 : ℝ)*(f.sum) + (5790418762364981/16937090000000000000000000000 : ℝ)*base63 + (2515431304823/17230000000000000000000000 : ℝ)*base64 + (1207561399557/4915000000000000000000000 : ℝ)*base66 + (1191300647869/8615000000000000000000000 : ℝ)*base69 + (4171383111607607/11187115937500000000000000000 : ℝ)*base71 + (11382313255539/103885000000000000000000000 : ℝ)*base72 + (1507764111/4799804687500000000000 : ℝ)*base74 + (47107744801521/207770000000000000000000000 : ℝ)*base77 + (42652029897615449/102118955000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p019_b026 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c319047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

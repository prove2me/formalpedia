-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:40:14.769777+00:00
-- url     : https://prove2.me/submissions/7e8efe67-9385-443a-9917-ea6ba5859730

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
theorem collision_support_c321059_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (739326567/2500000000 : ℝ)*x 0 + (-2957305929/10000000000 : ℝ)*x 1 + (250756219/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739326567/2500000000 : ℝ)^41 ≤ (5502610210753/25000000000000 : ℝ)^33 := by
    have hnat : (739326567 : ℕ)^41*25000000000000^33 ≤ 5502610210753^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739326567 2500000000 5502610210753 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2957305929/10000000000 : ℝ)^41 ≤ (5502609427067/25000000000000 : ℝ)^33 := by
    have hnat : (2957305929 : ℕ)^41*25000000000000^33 ≤ 5502609427067^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957305929 10000000000 5502609427067 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250756219/400000000 : ℝ)^41 ≤ (6997390179259/12500000000000 : ℝ)^33 := by
    have hnat : (250756219 : ℕ)^41*12500000000000^33 ≤ 6997390179259^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250756219 400000000 6997390179259 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(739326567/2500000000 : ℝ), (-2957305929/10000000000 : ℝ), (250756219/400000000 : ℝ)] ![(5502610210753/25000000000000 : ℝ), (5502609427067/25000000000000 : ℝ), (6997390179259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(739326567/2500000000 : ℝ)|^41 ≤ (5502610210753/25000000000000 : ℝ)^33
        have hw : |(739326567/2500000000 : ℝ)|=(739326567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2957305929/10000000000 : ℝ)|^41 ≤ (5502609427067/25000000000000 : ℝ)^33
        have hw : |(-2957305929/10000000000 : ℝ)|=(2957305929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250756219/400000000 : ℝ)|^41 ≤ (6997390179259/12500000000000 : ℝ)^33
        have hw : |(250756219/400000000 : ℝ)|=(250756219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1464416891/5000000000 : ℝ)*x 0 + (6443862449/10000000000 : ℝ)*x 1 + (693431581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1464416891/5000000000 : ℝ)^41 ≤ (543686571643/2500000000000 : ℝ)^33 := by
    have hnat : (1464416891 : ℕ)^41*2500000000000^33 ≤ 543686571643^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464416891 5000000000 543686571643 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6443862449/10000000000 : ℝ)^41 ≤ (1448167167539/2500000000000 : ℝ)^33 := by
    have hnat : (6443862449 : ℕ)^41*2500000000000^33 ≤ 1448167167539^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6443862449 10000000000 1448167167539 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693431581/2500000000 : ℝ)^41 ≤ (10162925212417/50000000000000 : ℝ)^33 := by
    have hnat : (693431581 : ℕ)^41*50000000000000^33 ≤ 10162925212417^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693431581 2500000000 10162925212417 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1464416891/5000000000 : ℝ), (6443862449/10000000000 : ℝ), (693431581/2500000000 : ℝ)] ![(543686571643/2500000000000 : ℝ), (1448167167539/2500000000000 : ℝ), (10162925212417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1464416891/5000000000 : ℝ)|^41 ≤ (543686571643/2500000000000 : ℝ)^33
        have hw : |(1464416891/5000000000 : ℝ)|=(1464416891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6443862449/10000000000 : ℝ)|^41 ≤ (1448167167539/2500000000000 : ℝ)^33
        have hw : |(6443862449/10000000000 : ℝ)|=(6443862449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(693431581/2500000000 : ℝ)|^41 ≤ (10162925212417/50000000000000 : ℝ)^33
        have hw : |(693431581/2500000000 : ℝ)|=(693431581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097210129/5000000000 : ℝ)*x 0 + (32385321/625000000 : ℝ)*x 1 + (1709414461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097210129/5000000000 : ℝ)^41 ≤ (3798216927523/25000000000000 : ℝ)^33 := by
    have hnat : (1097210129 : ℕ)^41*25000000000000^33 ≤ 3798216927523^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097210129 5000000000 3798216927523 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32385321/625000000 : ℝ)^41 ≤ (252827385307/10000000000000 : ℝ)^33 := by
    have hnat : (32385321 : ℕ)^41*10000000000000^33 ≤ 252827385307^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32385321 625000000 252827385307 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709414461/2000000000 : ℝ)^41 ≤ (16455771684287/20000000000000 : ℝ)^33 := by
    have hnat : (1709414461 : ℕ)^41*20000000000000^33 ≤ 16455771684287^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709414461 2000000000 16455771684287 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097210129/5000000000 : ℝ), (32385321/625000000 : ℝ), (1709414461/2000000000 : ℝ)] ![(3798216927523/25000000000000 : ℝ), (252827385307/10000000000000 : ℝ), (16455771684287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097210129/5000000000 : ℝ)|^41 ≤ (3798216927523/25000000000000 : ℝ)^33
        have hw : |(-1097210129/5000000000 : ℝ)|=(1097210129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32385321/625000000 : ℝ)|^41 ≤ (252827385307/10000000000000 : ℝ)^33
        have hw : |(32385321/625000000 : ℝ)|=(32385321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1709414461/2000000000 : ℝ)|^41 ≤ (16455771684287/20000000000000 : ℝ)^33
        have hw : |(1709414461/2000000000 : ℝ)|=(1709414461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (359446499/2500000000 : ℝ)*x 0 + (-1405734873/10000000000 : ℝ)*x 1 + (8547080417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359446499/2500000000 : ℝ)^41 ≤ (8984603495339/100000000000000 : ℝ)^33 := by
    have hnat : (359446499 : ℕ)^41*100000000000000^33 ≤ 8984603495339^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359446499 2500000000 8984603495339 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1405734873/10000000000 : ℝ)^41 ≤ (4368220523151/50000000000000 : ℝ)^33 := by
    have hnat : (1405734873 : ℕ)^41*50000000000000^33 ≤ 4368220523151^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405734873 10000000000 4368220523151 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8547080417/10000000000 : ℝ)^41 ≤ (16455791088623/20000000000000 : ℝ)^33 := by
    have hnat : (8547080417 : ℕ)^41*20000000000000^33 ≤ 16455791088623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8547080417 10000000000 16455791088623 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(359446499/2500000000 : ℝ), (-1405734873/10000000000 : ℝ), (8547080417/10000000000 : ℝ)] ![(8984603495339/100000000000000 : ℝ), (4368220523151/50000000000000 : ℝ), (16455791088623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(359446499/2500000000 : ℝ)|^41 ≤ (8984603495339/100000000000000 : ℝ)^33
        have hw : |(359446499/2500000000 : ℝ)|=(359446499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1405734873/10000000000 : ℝ)|^41 ≤ (4368220523151/50000000000000 : ℝ)^33
        have hw : |(-1405734873/10000000000 : ℝ)|=(1405734873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8547080417/10000000000 : ℝ)|^41 ≤ (16455791088623/20000000000000 : ℝ)^33
        have hw : |(8547080417/10000000000 : ℝ)|=(8547080417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (421201929/1000000000 : ℝ)*x 0 + (285743261/400000000 : ℝ)*x 1 + (-1122851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421201929/1000000000 : ℝ)^41 ≤ (17077634472983/50000000000000 : ℝ)^33 := by
    have hnat : (421201929 : ℕ)^41*50000000000000^33 ≤ 17077634472983^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421201929 1000000000 17077634472983 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285743261/400000000 : ℝ)^41 ≤ (32920900642313/50000000000000 : ℝ)^33 := by
    have hnat : (285743261 : ℕ)^41*50000000000000^33 ≤ 32920900642313^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285743261 400000000 32920900642313 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122851/5000000000 : ℝ)^41 ≤ (2929755843/100000000000000 : ℝ)^33 := by
    have hnat : (1122851 : ℕ)^41*100000000000000^33 ≤ 2929755843^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122851 5000000000 2929755843 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421201929/1000000000 : ℝ), (285743261/400000000 : ℝ), (-1122851/5000000000 : ℝ)] ![(17077634472983/50000000000000 : ℝ), (32920900642313/50000000000000 : ℝ), (2929755843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421201929/1000000000 : ℝ)|^41 ≤ (17077634472983/50000000000000 : ℝ)^33
        have hw : |(421201929/1000000000 : ℝ)|=(421201929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285743261/400000000 : ℝ)|^41 ≤ (32920900642313/50000000000000 : ℝ)^33
        have hw : |(285743261/400000000 : ℝ)|=(285743261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122851/5000000000 : ℝ)|^41 ≤ (2929755843/100000000000000 : ℝ)^33
        have hw : |(-1122851/5000000000 : ℝ)|=(1122851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (183180071/1000000000 : ℝ)*x 0 + (513323217/625000000 : ℝ)*x 1 + (1511015407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183180071/1000000000 : ℝ)^41 ≤ (1213897549343/10000000000000 : ℝ)^33 := by
    have hnat : (183180071 : ℕ)^41*10000000000000^33 ≤ 1213897549343^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183180071 1000000000 1213897549343 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513323217/625000000 : ℝ)^41 ≤ (78304416422561/100000000000000 : ℝ)^33 := by
    have hnat : (513323217 : ℕ)^41*100000000000000^33 ≤ 78304416422561^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513323217 625000000 78304416422561 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511015407/10000000000 : ℝ)^41 ≤ (9556608077541/100000000000000 : ℝ)^33 := by
    have hnat : (1511015407 : ℕ)^41*100000000000000^33 ≤ 9556608077541^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511015407 10000000000 9556608077541 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183180071/1000000000 : ℝ), (513323217/625000000 : ℝ), (1511015407/10000000000 : ℝ)] ![(1213897549343/10000000000000 : ℝ), (78304416422561/100000000000000 : ℝ), (9556608077541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183180071/1000000000 : ℝ)|^41 ≤ (1213897549343/10000000000000 : ℝ)^33
        have hw : |(183180071/1000000000 : ℝ)|=(183180071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513323217/625000000 : ℝ)|^41 ≤ (78304416422561/100000000000000 : ℝ)^33
        have hw : |(513323217/625000000 : ℝ)|=(513323217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1511015407/10000000000 : ℝ)|^41 ≤ (9556608077541/100000000000000 : ℝ)^33
        have hw : |(1511015407/10000000000 : ℝ)|=(1511015407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-952204341/10000000000 : ℝ)*x 0 + (175117289/1000000000 : ℝ)*x 1 + (8618725881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952204341/10000000000 : ℝ)^41 ≤ (2692276084597/50000000000000 : ℝ)^33 := by
    have hnat : (952204341 : ℕ)^41*50000000000000^33 ≤ 2692276084597^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952204341 10000000000 2692276084597 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175117289/1000000000 : ℝ)^41 ≤ (11478724630141/100000000000000 : ℝ)^33 := by
    have hnat : (175117289 : ℕ)^41*100000000000000^33 ≤ 11478724630141^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175117289 1000000000 11478724630141 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8618725881/10000000000 : ℝ)^41 ≤ (83136723183713/100000000000000 : ℝ)^33 := by
    have hnat : (8618725881 : ℕ)^41*100000000000000^33 ≤ 83136723183713^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8618725881 10000000000 83136723183713 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952204341/10000000000 : ℝ), (175117289/1000000000 : ℝ), (8618725881/10000000000 : ℝ)] ![(2692276084597/50000000000000 : ℝ), (11478724630141/100000000000000 : ℝ), (83136723183713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952204341/10000000000 : ℝ)|^41 ≤ (2692276084597/50000000000000 : ℝ)^33
        have hw : |(-952204341/10000000000 : ℝ)|=(952204341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175117289/1000000000 : ℝ)|^41 ≤ (11478724630141/100000000000000 : ℝ)^33
        have hw : |(175117289/1000000000 : ℝ)|=(175117289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8618725881/10000000000 : ℝ)|^41 ≤ (83136723183713/100000000000000 : ℝ)^33
        have hw : |(8618725881/10000000000 : ℝ)|=(8618725881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (85206013/1000000000 : ℝ)*x 0 + (-458986127/2500000000 : ℝ)*x 1 + (67333787/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85206013/1000000000 : ℝ)^41 ≤ (4690188562139/100000000000000 : ℝ)^33 := by
    have hnat : (85206013 : ℕ)^41*100000000000000^33 ≤ 4690188562139^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85206013 1000000000 4690188562139 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458986127/2500000000 : ℝ)^41 ≤ (6086550979209/50000000000000 : ℝ)^33 := by
    have hnat : (458986127 : ℕ)^41*50000000000000^33 ≤ 6086550979209^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458986127 2500000000 6086550979209 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67333787/78125000 : ℝ)^41 ≤ (83136709461467/100000000000000 : ℝ)^33 := by
    have hnat : (67333787 : ℕ)^41*100000000000000^33 ≤ 83136709461467^33*78125000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67333787 78125000 83136709461467 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85206013/1000000000 : ℝ), (-458986127/2500000000 : ℝ), (67333787/78125000 : ℝ)] ![(4690188562139/100000000000000 : ℝ), (6086550979209/50000000000000 : ℝ), (83136709461467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85206013/1000000000 : ℝ)|^41 ≤ (4690188562139/100000000000000 : ℝ)^33
        have hw : |(85206013/1000000000 : ℝ)|=(85206013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458986127/2500000000 : ℝ)|^41 ≤ (6086550979209/50000000000000 : ℝ)^33
        have hw : |(-458986127/2500000000 : ℝ)|=(458986127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67333787/78125000 : ℝ)|^41 ≤ (83136709461467/100000000000000 : ℝ)^33
        have hw : |(67333787/78125000 : ℝ)|=(67333787/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (66685299/78125000 : ℝ)*x 0 + (49982807/200000000 : ℝ)*x 1 + (-30557/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66685299/78125000 : ℝ)^41 ≤ (41071541526579/50000000000000 : ℝ)^33 := by
    have hnat : (66685299 : ℕ)^41*50000000000000^33 ≤ 41071541526579^33*78125000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66685299 78125000 41071541526579 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49982807/200000000 : ℝ)^41 ≤ (3571334225821/20000000000000 : ℝ)^33 := by
    have hnat : (49982807 : ℕ)^41*20000000000000^33 ≤ 3571334225821^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49982807 200000000 3571334225821 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30557/1000000000 : ℝ)^41 ≤ (49161157/20000000000000 : ℝ)^33 := by
    have hnat : (30557 : ℕ)^41*20000000000000^33 ≤ 49161157^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30557 1000000000 49161157 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66685299/78125000 : ℝ), (49982807/200000000 : ℝ), (-30557/1000000000 : ℝ)] ![(41071541526579/50000000000000 : ℝ), (3571334225821/20000000000000 : ℝ), (49161157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66685299/78125000 : ℝ)|^41 ≤ (41071541526579/50000000000000 : ℝ)^33
        have hw : |(66685299/78125000 : ℝ)|=(66685299/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49982807/200000000 : ℝ)|^41 ≤ (3571334225821/20000000000000 : ℝ)^33
        have hw : |(49982807/200000000 : ℝ)|=(49982807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30557/1000000000 : ℝ)|^41 ≤ (49161157/20000000000000 : ℝ)^33
        have hw : |(-30557/1000000000 : ℝ)|=(30557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3357536853/5000000000 : ℝ)*x 0 + (676406717/2000000000 : ℝ)*x 1 + (1938670831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3357536853/5000000000 : ℝ)^41 ≤ (15242763449583/25000000000000 : ℝ)^33 := by
    have hnat : (3357536853 : ℕ)^41*25000000000000^33 ≤ 15242763449583^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357536853 5000000000 15242763449583 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676406717/2000000000 : ℝ)^41 ≤ (6500986102879/25000000000000 : ℝ)^33 := by
    have hnat : (676406717 : ℕ)^41*25000000000000^33 ≤ 6500986102879^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676406717 2000000000 6500986102879 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938670831/10000000000 : ℝ)^41 ≤ (13025001782601/100000000000000 : ℝ)^33 := by
    have hnat : (1938670831 : ℕ)^41*100000000000000^33 ≤ 13025001782601^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938670831 10000000000 13025001782601 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3357536853/5000000000 : ℝ), (676406717/2000000000 : ℝ), (1938670831/10000000000 : ℝ)] ![(15242763449583/25000000000000 : ℝ), (6500986102879/25000000000000 : ℝ), (13025001782601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3357536853/5000000000 : ℝ)|^41 ≤ (15242763449583/25000000000000 : ℝ)^33
        have hw : |(3357536853/5000000000 : ℝ)|=(3357536853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676406717/2000000000 : ℝ)|^41 ≤ (6500986102879/25000000000000 : ℝ)^33
        have hw : |(676406717/2000000000 : ℝ)|=(676406717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1938670831/10000000000 : ℝ)|^41 ≤ (13025001782601/100000000000000 : ℝ)^33
        have hw : |(1938670831/10000000000 : ℝ)|=(1938670831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-183399537/312500000 : ℝ)*x 0 + (2035406061/10000000000 : ℝ)*x 1 + (1063723763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183399537/312500000 : ℝ)^41 ≤ (51574934987987/100000000000000 : ℝ)^33 := by
    have hnat : (183399537 : ℕ)^41*100000000000000^33 ≤ 51574934987987^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183399537 312500000 51574934987987 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035406061/10000000000 : ℝ)^41 ≤ (3459324716761/25000000000000 : ℝ)^33 := by
    have hnat : (2035406061 : ℕ)^41*25000000000000^33 ≤ 3459324716761^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035406061 10000000000 3459324716761 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063723763/2500000000 : ℝ)^41 ≤ (34587766132829/100000000000000 : ℝ)^33 := by
    have hnat : (1063723763 : ℕ)^41*100000000000000^33 ≤ 34587766132829^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063723763 2500000000 34587766132829 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183399537/312500000 : ℝ), (2035406061/10000000000 : ℝ), (1063723763/2500000000 : ℝ)] ![(51574934987987/100000000000000 : ℝ), (3459324716761/25000000000000 : ℝ), (34587766132829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183399537/312500000 : ℝ)|^41 ≤ (51574934987987/100000000000000 : ℝ)^33
        have hw : |(-183399537/312500000 : ℝ)|=(183399537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2035406061/10000000000 : ℝ)|^41 ≤ (3459324716761/25000000000000 : ℝ)^33
        have hw : |(2035406061/10000000000 : ℝ)|=(2035406061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063723763/2500000000 : ℝ)|^41 ≤ (34587766132829/100000000000000 : ℝ)^33
        have hw : |(1063723763/2500000000 : ℝ)|=(1063723763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (50355407/312500000 : ℝ)*x 0 + (-872695779/5000000000 : ℝ)*x 1 + (8205781443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50355407/312500000 : ℝ)^41 ≤ (2070290059927/20000000000000 : ℝ)^33 := by
    have hnat : (50355407 : ℕ)^41*20000000000000^33 ≤ 2070290059927^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50355407 312500000 2070290059927 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872695779/5000000000 : ℝ)^41 ≤ (11431660670031/100000000000000 : ℝ)^33 := by
    have hnat : (872695779 : ℕ)^41*100000000000000^33 ≤ 11431660670031^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872695779 5000000000 11431660670031 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8205781443/10000000000 : ℝ)^41 ≤ (78216889018613/100000000000000 : ℝ)^33 := by
    have hnat : (8205781443 : ℕ)^41*100000000000000^33 ≤ 78216889018613^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8205781443 10000000000 78216889018613 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50355407/312500000 : ℝ), (-872695779/5000000000 : ℝ), (8205781443/10000000000 : ℝ)] ![(2070290059927/20000000000000 : ℝ), (11431660670031/100000000000000 : ℝ), (78216889018613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50355407/312500000 : ℝ)|^41 ≤ (2070290059927/20000000000000 : ℝ)^33
        have hw : |(50355407/312500000 : ℝ)|=(50355407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-872695779/5000000000 : ℝ)|^41 ≤ (11431660670031/100000000000000 : ℝ)^33
        have hw : |(-872695779/5000000000 : ℝ)|=(872695779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8205781443/10000000000 : ℝ)|^41 ≤ (78216889018613/100000000000000 : ℝ)^33
        have hw : |(8205781443/10000000000 : ℝ)|=(8205781443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8609738779/10000000000 : ℝ)*x 0 + (2398875919/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8609738779/10000000000 : ℝ)^41 ≤ (1660580618367/2000000000000 : ℝ)^33 := by
    have hnat : (8609738779 : ℕ)^41*2000000000000^33 ≤ 1660580618367^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8609738779 10000000000 1660580618367 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2398875919/10000000000 : ℝ)^41 ≤ (16970969062173/100000000000000 : ℝ)^33 := by
    have hnat : (2398875919 : ℕ)^41*100000000000000^33 ≤ 16970969062173^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398875919 10000000000 16970969062173 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^41 ≤ (0 : ℝ)^33 := by
    have hnat : (0 : ℕ)^41*1^33 ≤ 0^33*1^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8609738779/10000000000 : ℝ), (2398875919/10000000000 : ℝ), (0 : ℝ)] ![(1660580618367/2000000000000 : ℝ), (16970969062173/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8609738779/10000000000 : ℝ)|^41 ≤ (1660580618367/2000000000000 : ℝ)^33
        have hw : |(8609738779/10000000000 : ℝ)|=(8609738779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2398875919/10000000000 : ℝ)|^41 ≤ (16970969062173/100000000000000 : ℝ)^33
        have hw : |(2398875919/10000000000 : ℝ)|=(2398875919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^41 ≤ (0 : ℝ)^33
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1179192113/10000000000 : ℝ)*x 0 + (8445436047/10000000000 : ℝ)*x 1 + (451049117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1179192113/10000000000 : ℝ)^41 ≤ (109732224533/1562500000000 : ℝ)^33 := by
    have hnat : (1179192113 : ℕ)^41*1562500000000^33 ≤ 109732224533^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179192113 10000000000 109732224533 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8445436047/10000000000 : ℝ)^41 ≤ (40532509639909/50000000000000 : ℝ)^33 := by
    have hnat : (8445436047 : ℕ)^41*50000000000000^33 ≤ 40532509639909^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8445436047 10000000000 40532509639909 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451049117/2500000000 : ℝ)^41 ≤ (11912118327611/100000000000000 : ℝ)^33 := by
    have hnat : (451049117 : ℕ)^41*100000000000000^33 ≤ 11912118327611^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451049117 2500000000 11912118327611 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1179192113/10000000000 : ℝ), (8445436047/10000000000 : ℝ), (451049117/2500000000 : ℝ)] ![(109732224533/1562500000000 : ℝ), (40532509639909/50000000000000 : ℝ), (11912118327611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1179192113/10000000000 : ℝ)|^41 ≤ (109732224533/1562500000000 : ℝ)^33
        have hw : |(1179192113/10000000000 : ℝ)|=(1179192113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8445436047/10000000000 : ℝ)|^41 ≤ (40532509639909/50000000000000 : ℝ)^33
        have hw : |(8445436047/10000000000 : ℝ)|=(8445436047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451049117/2500000000 : ℝ)|^41 ≤ (11912118327611/100000000000000 : ℝ)^33
        have hw : |(451049117/2500000000 : ℝ)|=(451049117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3234372239/10000000000 : ℝ)*x 0 + (1615670117/5000000000 : ℝ)*x 1 + (5800169549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3234372239/10000000000 : ℝ)^41 ≤ (307511403939/1250000000000 : ℝ)^33 := by
    have hnat : (3234372239 : ℕ)^41*1250000000000^33 ≤ 307511403939^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3234372239 10000000000 307511403939 1250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615670117/5000000000 : ℝ)^41 ≤ (12286131584591/50000000000000 : ℝ)^33 := by
    have hnat : (1615670117 : ℕ)^41*50000000000000^33 ≤ 12286131584591^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615670117 5000000000 12286131584591 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5800169549/10000000000 : ℝ)^41 ≤ (50826824494753/100000000000000 : ℝ)^33 := by
    have hnat : (5800169549 : ℕ)^41*100000000000000^33 ≤ 50826824494753^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5800169549 10000000000 50826824494753 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3234372239/10000000000 : ℝ), (1615670117/5000000000 : ℝ), (5800169549/10000000000 : ℝ)] ![(307511403939/1250000000000 : ℝ), (12286131584591/50000000000000 : ℝ), (50826824494753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3234372239/10000000000 : ℝ)|^41 ≤ (307511403939/1250000000000 : ℝ)^33
        have hw : |(-3234372239/10000000000 : ℝ)|=(3234372239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1615670117/5000000000 : ℝ)|^41 ≤ (12286131584591/50000000000000 : ℝ)^33
        have hw : |(1615670117/5000000000 : ℝ)|=(1615670117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5800169549/10000000000 : ℝ)|^41 ≤ (50826824494753/100000000000000 : ℝ)^33
        have hw : |(5800169549/10000000000 : ℝ)|=(5800169549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3231764049/10000000000 : ℝ)*x 0 + (-1614313619/5000000000 : ℝ)*x 1 + (2902393391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3231764049/10000000000 : ℝ)^41 ≤ (24576267367827/100000000000000 : ℝ)^33 := by
    have hnat : (3231764049 : ℕ)^41*100000000000000^33 ≤ 24576267367827^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3231764049 10000000000 24576267367827 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614313619/5000000000 : ℝ)^41 ≤ (981865353383/4000000000000 : ℝ)^33 := by
    have hnat : (1614313619 : ℕ)^41*4000000000000^33 ≤ 981865353383^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614313619 5000000000 981865353383 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2902393391/5000000000 : ℝ)^41 ≤ (50877098778403/100000000000000 : ℝ)^33 := by
    have hnat : (2902393391 : ℕ)^41*100000000000000^33 ≤ 50877098778403^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902393391 5000000000 50877098778403 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3231764049/10000000000 : ℝ), (-1614313619/5000000000 : ℝ), (2902393391/5000000000 : ℝ)] ![(24576267367827/100000000000000 : ℝ), (981865353383/4000000000000 : ℝ), (50877098778403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3231764049/10000000000 : ℝ)|^41 ≤ (24576267367827/100000000000000 : ℝ)^33
        have hw : |(3231764049/10000000000 : ℝ)|=(3231764049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614313619/5000000000 : ℝ)|^41 ≤ (981865353383/4000000000000 : ℝ)^33
        have hw : |(-1614313619/5000000000 : ℝ)|=(1614313619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2902393391/5000000000 : ℝ)|^41 ≤ (50877098778403/100000000000000 : ℝ)^33
        have hw : |(2902393391/5000000000 : ℝ)|=(2902393391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2834934967/5000000000 : ℝ)*x 0 + (5437794679/10000000000 : ℝ)*x 1 + (-87541601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2834934967/5000000000 : ℝ)^41 ≤ (24706045975369/50000000000000 : ℝ)^33 := by
    have hnat : (2834934967 : ℕ)^41*50000000000000^33 ≤ 24706045975369^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834934967 5000000000 24706045975369 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437794679/10000000000 : ℝ)^41 ≤ (46911884508963/100000000000000 : ℝ)^33 := by
    have hnat : (5437794679 : ℕ)^41*100000000000000^33 ≤ 46911884508963^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437794679 10000000000 46911884508963 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87541601/1250000000 : ℝ)^41 ≤ (919005883921/25000000000000 : ℝ)^33 := by
    have hnat : (87541601 : ℕ)^41*25000000000000^33 ≤ 919005883921^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87541601 1250000000 919005883921 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2834934967/5000000000 : ℝ), (5437794679/10000000000 : ℝ), (-87541601/1250000000 : ℝ)] ![(24706045975369/50000000000000 : ℝ), (46911884508963/100000000000000 : ℝ), (919005883921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2834934967/5000000000 : ℝ)|^41 ≤ (24706045975369/50000000000000 : ℝ)^33
        have hw : |(2834934967/5000000000 : ℝ)|=(2834934967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437794679/10000000000 : ℝ)|^41 ≤ (46911884508963/100000000000000 : ℝ)^33
        have hw : |(5437794679/10000000000 : ℝ)|=(5437794679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87541601/1250000000 : ℝ)|^41 ≤ (919005883921/25000000000000 : ℝ)^33
        have hw : |(-87541601/1250000000 : ℝ)|=(87541601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321059_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (811879377/2000000000 : ℝ)*x 0 + (4727071507/10000000000 : ℝ)*x 1 + (3584982833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811879377/2000000000 : ℝ)^41 ≤ (1019513814749/3125000000000 : ℝ)^33 := by
    have hnat : (811879377 : ℕ)^41*3125000000000^33 ≤ 1019513814749^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811879377 2000000000 1019513814749 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4727071507/10000000000 : ℝ)^41 ≤ (985474598587/2500000000000 : ℝ)^33 := by
    have hnat : (4727071507 : ℕ)^41*2500000000000^33 ≤ 985474598587^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4727071507 10000000000 985474598587 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3584982833/10000000000 : ℝ)^41 ≤ (27956573971463/100000000000000 : ℝ)^33 := by
    have hnat : (3584982833 : ℕ)^41*100000000000000^33 ≤ 27956573971463^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584982833 10000000000 27956573971463 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811879377/2000000000 : ℝ), (4727071507/10000000000 : ℝ), (3584982833/10000000000 : ℝ)] ![(1019513814749/3125000000000 : ℝ), (985474598587/2500000000000 : ℝ), (27956573971463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811879377/2000000000 : ℝ)|^41 ≤ (1019513814749/3125000000000 : ℝ)^33
        have hw : |(811879377/2000000000 : ℝ)|=(811879377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4727071507/10000000000 : ℝ)|^41 ≤ (985474598587/2500000000000 : ℝ)^33
        have hw : |(4727071507/10000000000 : ℝ)|=(4727071507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3584982833/10000000000 : ℝ)|^41 ≤ (27956573971463/100000000000000 : ℝ)^33
        have hw : |(3584982833/10000000000 : ℝ)|=(3584982833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321059 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((739326567/2500000000 : ℝ)*X 1 0+(-2957305929/10000000000 : ℝ)*X 1 1+(250756219/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1464416891/5000000000 : ℝ)*X 0 0+(6443862449/10000000000 : ℝ)*X 0 1+(693431581/2500000000 : ℝ)*X 0 2+(1464416891/5000000000 : ℝ)*X 1 0+(6443862449/10000000000 : ℝ)*X 1 1+(693431581/2500000000 : ℝ)*X 1 2+(1464416891/5000000000 : ℝ)*X 2 0+(6443862449/10000000000 : ℝ)*X 2 1+(693431581/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1097210129/5000000000 : ℝ)*X 0 0+(32385321/625000000 : ℝ)*X 0 1+(1709414461/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((359446499/2500000000 : ℝ)*X 1 0+(-1405734873/10000000000 : ℝ)*X 1 1+(8547080417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((421201929/1000000000 : ℝ)*X 2 0+(285743261/400000000 : ℝ)*X 2 1+(-1122851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((183180071/1000000000 : ℝ)*X 0 0+(513323217/625000000 : ℝ)*X 0 1+(1511015407/10000000000 : ℝ)*X 0 2+(183180071/1000000000 : ℝ)*X 1 0+(513323217/625000000 : ℝ)*X 1 1+(1511015407/10000000000 : ℝ)*X 1 2+(183180071/1000000000 : ℝ)*X 2 0+(513323217/625000000 : ℝ)*X 2 1+(1511015407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-952204341/10000000000 : ℝ)*X 0 0+(175117289/1000000000 : ℝ)*X 0 1+(8618725881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((85206013/1000000000 : ℝ)*X 1 0+(-458986127/2500000000 : ℝ)*X 1 1+(67333787/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((66685299/78125000 : ℝ)*X 2 0+(49982807/200000000 : ℝ)*X 2 1+(-30557/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3357536853/5000000000 : ℝ)*X 0 0+(676406717/2000000000 : ℝ)*X 0 1+(1938670831/10000000000 : ℝ)*X 0 2+(3357536853/5000000000 : ℝ)*X 1 0+(676406717/2000000000 : ℝ)*X 1 1+(1938670831/10000000000 : ℝ)*X 1 2+(3357536853/5000000000 : ℝ)*X 2 0+(676406717/2000000000 : ℝ)*X 2 1+(1938670831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-183399537/312500000 : ℝ)*X 0 0+(2035406061/10000000000 : ℝ)*X 0 1+(1063723763/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((50355407/312500000 : ℝ)*X 1 0+(-872695779/5000000000 : ℝ)*X 1 1+(8205781443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8609738779/10000000000 : ℝ)*X 2 0+(2398875919/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1179192113/10000000000 : ℝ)*X 0 0+(8445436047/10000000000 : ℝ)*X 0 1+(451049117/2500000000 : ℝ)*X 0 2+(1179192113/10000000000 : ℝ)*X 1 0+(8445436047/10000000000 : ℝ)*X 1 1+(451049117/2500000000 : ℝ)*X 1 2+(1179192113/10000000000 : ℝ)*X 2 0+(8445436047/10000000000 : ℝ)*X 2 1+(451049117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((18047/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18047/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4518229042897237057059/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570913583569/500000000000 : ℝ)*(base7) + (164777/100000000000 : ℝ)*(base29) + (232493/500000000000 : ℝ)*(base39) + (384765130083/250000000000 : ℝ)*(major_s0_0) + (384765130083/250000000000 : ℝ)*(major_s0_1) + (384765130083/250000000000 : ℝ)*(major_s0_2) + (1628056366007/1000000000000 : ℝ)*(sp_s0_7) + (325609762457/200000000000 : ℝ)*(sp_s0_8) + (81403657059/50000000000 : ℝ)*(sp_s0_9) + (1950338014479/1000000000000 : ℝ)*(sp_s0_13) + (8387587/500000000000 : ℝ)*(sp_s0_14) + (1148297/500000000000 : ℝ)*(sp_s0_15) + (22032301/1000000000000 : ℝ)*(sp_s0_22) + (2144219/100000000000 : ℝ)*(sp_s0_27) + (808533937301/1000000000000 : ℝ)*(f.failure) + (81403657059/50000000000 : ℝ)*(f.sum) + (58563629/500000000000000000000 : ℝ)*base63 + (668168759744679/1250000000000000000000000000 : ℝ)*base65 + (81625450744679/1250000000000000000000000000 : ℝ)*base67 + (1120440932216711/2500000000000000000000000000 : ℝ)*base69 + (403463203022647/2500000000000000000000000000 : ℝ)*base71 + (612119457869679/1250000000000000000000000000 : ℝ)*base73 + (1769253161783289/2500000000000000000000000000 : ℝ)*base75 + (2380809222283289/2500000000000000000000000000 : ℝ)*base77 + (187943293567821/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (5003/6250000000000000 : ℝ)*base86 + (5003/6250000000000000 : ℝ)*base88 + (5003/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35913/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35913/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18460554929672865571323/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13922368511/31250000000 : ℝ)*(base5) + (570182298791/500000000000 : ℝ)*(base7) + (8007873/1000000000000 : ℝ)*(base19) + (1091/1600000000 : ℝ)*(base53) + (152560198513/1000000000000 : ℝ)*(base60) + (150614775871/100000000000 : ℝ)*(major_s0_0) + (150614775871/100000000000 : ℝ)*(major_s0_1) + (301229415367/200000000000 : ℝ)*(major_s0_2) + (8070747/62500000000 : ℝ)*(sp_s0_8) + (1580354176099/1000000000000 : ℝ)*(sp_s0_14) + (63208681451/40000000000 : ℝ)*(sp_s0_15) + (2025475880939/1000000000000 : ℝ)*(sp_s0_16) + (1486092269291/1000000000000 : ℝ)*(sp_s0_20) + (394769387/1000000000000 : ℝ)*(sp_s0_23) + (791243464061/1000000000000 : ℝ)*(f.failure) + (790177428987/500000000000 : ℝ)*(f.sum) + (9615920104153/16000000000000000000000000 : ℝ)*base63 + (419339745236171/1000000000000000000000000000 : ℝ)*base65 + (118164833579523/500000000000000000000000000 : ℝ)*base67 + (949399232550939/2000000000000000000000000000 : ℝ)*base69 + (71498644496283/125000000000000000000000000 : ℝ)*base71 + (342688374670477/500000000000000000000000000 : ℝ)*base72 + (120360987434093/1000000000000000000000000000 : ℝ)*base75 + (10587033665907/1000000000000000000000000000 : ℝ)*base76 + (12242770804523/250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (3783/6250000000000000 : ℝ)*base86 + (3783/6250000000000000 : ℝ)*base88 + (3783/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13903/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13903/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2424673242342308619957/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18270878179/500000000000 : ℝ)*(base5) + (121952567759/200000000000 : ℝ)*(base7) + (343877863823/500000000000 : ℝ)*(base44) + (97837825851/1000000000000 : ℝ)*(base50) + (1481812600393/1000000000000 : ℝ)*(major_s0_0) + (198514218187/250000000000 : ℝ)*(major_s0_1) + (1481812600393/1000000000000 : ℝ)*(major_s0_2) + (16859607/100000000000 : ℝ)*(sp_s0_1) + (9386073/1000000000000 : ℝ)*(sp_s0_6) + (247697401/1000000000000 : ℝ)*(sp_s0_15) + (73703189663/40000000000 : ℝ)*(sp_s0_21) + (1154407720459/1000000000000 : ℝ)*(sp_s0_22) + (939560748967/500000000000 : ℝ)*(sp_s0_23) + (663915139303/1000000000000 : ℝ)*(sp_s0_27) + (389229585293/500000000000 : ℝ)*(f.failure) + (73703189663/40000000000 : ℝ)*(f.sum) + (873696529462107/2000000000000000000000000000 : ℝ)*base62 + (3858345573760709/5000000000000000000000000000 : ℝ)*base65 + (450459135216831/1250000000000000000000000000 : ℝ)*base67 + (1736775663467019/10000000000000000000000000000 : ℝ)*base68 + (2303538514988437/10000000000000000000000000000 : ℝ)*base71 + (2232549469239291/5000000000000000000000000000 : ℝ)*base72 + (1444684150210879/2500000000000000000000000000 : ℝ)*base74 + (6414974068467019/10000000000000000000000000000 : ℝ)*base77 + (1863082611128033/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (337/390625000000000 : ℝ)*base87 + (429/3125000000000000 : ℝ)*base88 + (337/390625000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (18047/25000 : ℝ) ^ (81/16 : ℝ) ≤ (600245804383237021/3125000000000000000 : ℝ) := by
    have hpowers : (18047/25000 : ℝ)^81 ≤ (600245804383237021/3125000000000000000 : ℝ)^16 := by
      have hnat : (18047 : ℕ)^81*3125000000000000000^16 ≤ 600245804383237021^16*25000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18047 25000 600245804383237021 3125000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18047/25000 : ℝ)) (X := (600245804383237021/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3725245804383237021/3125000000000000000 : ℝ) ≤ (82825213170393/80000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3725245804383237021/3125000000000000000 : ℝ)^16 ≤ (82825213170393/80000000000000 : ℝ)^81 := by
      have hnat : (3725245804383237021 : ℕ)^16*80000000000000^81 ≤ 82825213170393^81*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3725245804383237021 3125000000000000000 82825213170393 80000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (82825213170393/80000000000000 : ℝ)) (X := (3725245804383237021/3125000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2162745804383237021/1562500000000000000 : ℝ) ≤ (10663222820146507/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2162745804383237021/1562500000000000000 : ℝ)^16 ≤ (10663222820146507/10000000000000000 : ℝ)^81 := by
      have hnat : (2162745804383237021 : ℕ)^16*10000000000000000^81 ≤ 10663222820146507^81*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2162745804383237021 1562500000000000000 10663222820146507 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10663222820146507/10000000000000000 : ℝ)) (X := (2162745804383237021/1562500000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2825213170393/57750400000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(155035586923691/3609400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (18047/25000 : ℝ)) (alpha := (2825213170393/57750400000000 : ℝ)) (beta := (155035586923691/3609400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18047/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2825213170393/57750400000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(155035586923691/3609400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (35913/50000 : ℝ) ^ (81/16 : ℝ) ≤ (749007217005630873/4000000000000000000 : ℝ) := by
    have hpowers : (35913/50000 : ℝ)^81 ≤ (749007217005630873/4000000000000000000 : ℝ)^16 := by
      have hnat : (35913 : ℕ)^81*4000000000000000000^16 ≤ 749007217005630873^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35913 50000 749007217005630873 4000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35913/50000 : ℝ)) (X := (749007217005630873/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (4749007217005630873/4000000000000000000 : ℝ) ≤ (80819198959107/78125000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (4749007217005630873/4000000000000000000 : ℝ)^16 ≤ (80819198959107/78125000000000 : ℝ)^81 := by
      have hnat : (4749007217005630873 : ℕ)^16*78125000000000^81 ≤ 80819198959107^81*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4749007217005630873 4000000000000000000 80819198959107 78125000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80819198959107/78125000000000 : ℝ)) (X := (4749007217005630873/4000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2749007217005630873/2000000000000000000 : ℝ) ≤ (10648491190034247/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2749007217005630873/2000000000000000000 : ℝ)^16 ≤ (10648491190034247/10000000000000000 : ℝ)^81 := by
      have hnat : (2749007217005630873 : ℕ)^16*10000000000000000^81 ≤ 10648491190034247^81*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2749007217005630873 2000000000000000000 10648491190034247 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10648491190034247/10000000000000000 : ℝ)) (X := (2749007217005630873/2000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2694198959107/56114062500000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(101211241089517/2394200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (35913/50000 : ℝ)) (alpha := (2694198959107/56114062500000 : ℝ)) (beta := (101211241089517/2394200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35913/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2694198959107/56114062500000 : ℝ)*((1 : ℝ)*pair X 1 0)+(101211241089517/2394200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13903/25000 : ℝ) ^ (81/16 : ℝ) ≤ (640952160220324413/12500000000000000000 : ℝ) := by
    have hpowers : (13903/25000 : ℝ)^81 ≤ (640952160220324413/12500000000000000000 : ℝ)^16 := by
      have hnat : (13903 : ℕ)^81*12500000000000000000^16 ≤ 640952160220324413^16*25000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13903 25000 640952160220324413 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13903/25000 : ℝ)) (X := (640952160220324413/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13140952160220324413/12500000000000000000 : ℝ) ≤ (2019852881088583/2000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (13140952160220324413/12500000000000000000 : ℝ)^16 ≤ (2019852881088583/2000000000000000 : ℝ)^81 := by
      have hnat : (13140952160220324413 : ℕ)^16*2000000000000000^81 ≤ 2019852881088583^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13140952160220324413 12500000000000000000 2019852881088583 2000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2019852881088583/2000000000000000 : ℝ)) (X := (13140952160220324413/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6890952160220324413/6250000000000000000 : ℝ) ≤ (10194716520803851/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (6890952160220324413/6250000000000000000 : ℝ)^16 ≤ (10194716520803851/10000000000000000 : ℝ)^81 := by
      have hnat : (6890952160220324413 : ℕ)^16*10000000000000000^81 ≤ 10194716520803851^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6890952160220324413 6250000000000000000 10194716520803851 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10194716520803851/10000000000000000 : ℝ)) (X := (6890952160220324413/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(19852881088583/1112240000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(11931514420117/695150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (13903/25000 : ℝ)) (alpha := (19852881088583/1112240000000000 : ℝ)) (beta := (11931514420117/695150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13903/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(19852881088583/1112240000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(11931514420117/695150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3234372239/10000000000 : ℝ)*X 0 0+(1615670117/5000000000 : ℝ)*X 0 1+(5800169549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3231764049/10000000000 : ℝ)*X 1 0+(-1614313619/5000000000 : ℝ)*X 1 1+(2902393391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2834934967/5000000000 : ℝ)*X 2 0+(5437794679/10000000000 : ℝ)*X 2 1+(-87541601/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((811879377/2000000000 : ℝ)*X 0 0+(4727071507/10000000000 : ℝ)*X 0 1+(3584982833/10000000000 : ℝ)*X 0 2+(811879377/2000000000 : ℝ)*X 1 0+(4727071507/10000000000 : ℝ)*X 1 1+(3584982833/10000000000 : ℝ)*X 1 2+(811879377/2000000000 : ℝ)*X 2 0+(4727071507/10000000000 : ℝ)*X 2 1+(3584982833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-2525276222675363134044882030085527171/300361297621100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1273/500000000000 : ℝ)*(base5) + (107/3125000000 : ℝ)*(base7) + (11749/200000000000 : ℝ)*(base13) + (32003/500000000000 : ℝ)*(base23) + (19909/1000000000000 : ℝ)*(base29) + (12607/500000000000 : ℝ)*(base43) + (151/100000000000 : ℝ)*(base53) + (111581144513/200000000000 : ℝ)*(base60) + (11897/6250 : ℝ)*(major_s1_0) + (951759987393/500000000000 : ℝ)*(major_s1_1) + (190351999849/100000000000 : ℝ)*(major_s1_2) + (560497451641/200000000000 : ℝ)*(sp_s1_0) + (560497468433/200000000000 : ℝ)*(sp_s1_1) + (2802487257/1000000000 : ℝ)*(sp_s1_2) + (200000002357/200000000000 : ℝ)*(sp_s1_6) + (1401243671837/500000000000 : ℝ)*(f.sum) + (16149681723915839869/33286562600000000000000000000000 : ℝ)*base62 + (24067374121271/139030000000000000000000000 : ℝ)*base65 + (315940715529681/1197100000000000000000000000 : ℝ)*base67 + (54569942109111/111224000000000000000000000 : ℝ)*base68 + (160137267386773577/2509074410000000000000000000000 : ℝ)*base71 + (10955320495389/36094000000000000000000000 : ℝ)*base72 + (104475293165213/598550000000000000000000000 : ℝ)*base75 + (22219167015847/36094000000000000000000000 : ℝ)*base77 + (1078050550825974657/21604063700000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p021_b035 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c321059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:48:43.028209+00:00
-- url     : https://prove2.me/submissions/044d3358-ba75-487d-baf5-44f4535b8144

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
theorem collision_support_c322009_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4126708973/10000000000 : ℝ)*x 0 + (455251361/1000000000 : ℝ)*x 1 + (909084653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4126708973/10000000000 : ℝ)^21 ≤ (16754354175349/50000000000000 : ℝ)^17 := by
    have hnat : (4126708973 : ℕ)^21*50000000000000^17 ≤ 16754354175349^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126708973 10000000000 16754354175349 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455251361/1000000000 : ℝ)^21 ≤ (18915149893921/50000000000000 : ℝ)^17 := by
    have hnat : (455251361 : ℕ)^21*50000000000000^17 ≤ 18915149893921^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455251361 1000000000 18915149893921 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909084653/2500000000 : ℝ)^21 ≤ (28660991854713/100000000000000 : ℝ)^17 := by
    have hnat : (909084653 : ℕ)^21*100000000000000^17 ≤ 28660991854713^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909084653 2500000000 28660991854713 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4126708973/10000000000 : ℝ), (455251361/1000000000 : ℝ), (909084653/2500000000 : ℝ)] ![(16754354175349/50000000000000 : ℝ), (18915149893921/50000000000000 : ℝ), (28660991854713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4126708973/10000000000 : ℝ)|^21 ≤ (16754354175349/50000000000000 : ℝ)^17
        have hw : |(4126708973/10000000000 : ℝ)|=(4126708973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(455251361/1000000000 : ℝ)|^21 ≤ (18915149893921/50000000000000 : ℝ)^17
        have hw : |(455251361/1000000000 : ℝ)|=(455251361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(909084653/2500000000 : ℝ)|^21 ≤ (28660991854713/100000000000000 : ℝ)^17
        have hw : |(909084653/2500000000 : ℝ)|=(909084653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5115624721/10000000000 : ℝ)*x 0 + (-4299884877/10000000000 : ℝ)*x 1 + (-1106561/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5115624721/10000000000 : ℝ)^21 ≤ (10923058440809/25000000000000 : ℝ)^17 := by
    have hnat : (5115624721 : ℕ)^21*25000000000000^17 ≤ 10923058440809^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115624721 10000000000 10923058440809 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299884877/10000000000 : ℝ)^21 ≤ (440678019503/1250000000000 : ℝ)^17 := by
    have hnat : (4299884877 : ℕ)^21*1250000000000^17 ≤ 440678019503^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299884877 10000000000 440678019503 1250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106561/3906250 : ℝ)^21 ≤ (21053524657319/100000000000000 : ℝ)^17 := by
    have hnat : (1106561 : ℕ)^21*100000000000000^17 ≤ 21053524657319^17*3906250^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106561 3906250 21053524657319 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5115624721/10000000000 : ℝ), (-4299884877/10000000000 : ℝ), (-1106561/3906250 : ℝ)] ![(10923058440809/25000000000000 : ℝ), (440678019503/1250000000000 : ℝ), (21053524657319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5115624721/10000000000 : ℝ)|^21 ≤ (10923058440809/25000000000000 : ℝ)^17
        have hw : |(5115624721/10000000000 : ℝ)|=(5115624721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4299884877/10000000000 : ℝ)|^21 ≤ (440678019503/1250000000000 : ℝ)^17
        have hw : |(-4299884877/10000000000 : ℝ)|=(4299884877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106561/3906250 : ℝ)|^21 ≤ (21053524657319/100000000000000 : ℝ)^17
        have hw : |(-1106561/3906250 : ℝ)|=(1106561/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1212259/2500000000 : ℝ)*x 0 + (-1516771839/10000000000 : ℝ)*x 1 + (920391883/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1212259/2500000000 : ℝ)^21 ≤ (8050254719/100000000000000 : ℝ)^17 := by
    have hnat : (1212259 : ℕ)^21*100000000000000^17 ≤ 8050254719^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212259 2500000000 8050254719 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1516771839/10000000000 : ℝ)^21 ≤ (4865927295997/50000000000000 : ℝ)^17 := by
    have hnat : (1516771839 : ℕ)^21*50000000000000^17 ≤ 4865927295997^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516771839 10000000000 4865927295997 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920391883/1000000000 : ℝ)^21 ≤ (90260095145423/100000000000000 : ℝ)^17 := by
    have hnat : (920391883 : ℕ)^21*100000000000000^17 ≤ 90260095145423^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920391883 1000000000 90260095145423 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1212259/2500000000 : ℝ), (-1516771839/10000000000 : ℝ), (920391883/1000000000 : ℝ)] ![(8050254719/100000000000000 : ℝ), (4865927295997/50000000000000 : ℝ), (90260095145423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1212259/2500000000 : ℝ)|^21 ≤ (8050254719/100000000000000 : ℝ)^17
        have hw : |(-1212259/2500000000 : ℝ)|=(1212259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1516771839/10000000000 : ℝ)|^21 ≤ (4865927295997/50000000000000 : ℝ)^17
        have hw : |(-1516771839/10000000000 : ℝ)|=(1516771839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920391883/1000000000 : ℝ)|^21 ≤ (90260095145423/100000000000000 : ℝ)^17
        have hw : |(920391883/1000000000 : ℝ)|=(920391883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-408779231/1000000000 : ℝ)*x 0 + (-8084161/16000000 : ℝ)*x 1 + (3134047249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408779231/1000000000 : ℝ)^21 ≤ (33118787421603/100000000000000 : ℝ)^17 := by
    have hnat : (408779231 : ℕ)^21*100000000000000^17 ≤ 33118787421603^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408779231 1000000000 33118787421603 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8084161/16000000 : ℝ)^21 ≤ (21514130201639/50000000000000 : ℝ)^17 := by
    have hnat : (8084161 : ℕ)^21*50000000000000^17 ≤ 21514130201639^17*16000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8084161 16000000 21514130201639 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134047249/10000000000 : ℝ)^21 ≤ (23852952161633/100000000000000 : ℝ)^17 := by
    have hnat : (3134047249 : ℕ)^21*100000000000000^17 ≤ 23852952161633^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134047249 10000000000 23852952161633 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408779231/1000000000 : ℝ), (-8084161/16000000 : ℝ), (3134047249/10000000000 : ℝ)] ![(33118787421603/100000000000000 : ℝ), (21514130201639/50000000000000 : ℝ), (23852952161633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408779231/1000000000 : ℝ)|^21 ≤ (33118787421603/100000000000000 : ℝ)^17
        have hw : |(-408779231/1000000000 : ℝ)|=(408779231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8084161/16000000 : ℝ)|^21 ≤ (21514130201639/50000000000000 : ℝ)^17
        have hw : |(-8084161/16000000 : ℝ)|=(8084161/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134047249/10000000000 : ℝ)|^21 ≤ (23852952161633/100000000000000 : ℝ)^17
        have hw : |(3134047249/10000000000 : ℝ)|=(3134047249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3471817009/10000000000 : ℝ)*x 0 + (5241169007/10000000000 : ℝ)*x 1 + (3559179473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3471817009/10000000000 : ℝ)^21 ≤ (13533887270069/50000000000000 : ℝ)^17 := by
    have hnat : (3471817009 : ℕ)^21*50000000000000^17 ≤ 13533887270069^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3471817009 10000000000 13533887270069 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241169007/10000000000 : ℝ)^21 ≤ (22510299120143/50000000000000 : ℝ)^17 := by
    have hnat : (5241169007 : ℕ)^21*50000000000000^17 ≤ 22510299120143^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241169007 10000000000 22510299120143 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3559179473/10000000000 : ℝ)^21 ≤ (1744476699771/6250000000000 : ℝ)^17 := by
    have hnat : (3559179473 : ℕ)^21*6250000000000^17 ≤ 1744476699771^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3559179473 10000000000 1744476699771 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3471817009/10000000000 : ℝ), (5241169007/10000000000 : ℝ), (3559179473/10000000000 : ℝ)] ![(13533887270069/50000000000000 : ℝ), (22510299120143/50000000000000 : ℝ), (1744476699771/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3471817009/10000000000 : ℝ)|^21 ≤ (13533887270069/50000000000000 : ℝ)^17
        have hw : |(3471817009/10000000000 : ℝ)|=(3471817009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241169007/10000000000 : ℝ)|^21 ≤ (22510299120143/50000000000000 : ℝ)^17
        have hw : |(5241169007/10000000000 : ℝ)|=(5241169007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3559179473/10000000000 : ℝ)|^21 ≤ (1744476699771/6250000000000 : ℝ)^17
        have hw : |(3559179473/10000000000 : ℝ)|=(3559179473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1175524021/2000000000 : ℝ)*x 0 + (-406910103/1000000000 : ℝ)*x 1 + (-272023701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1175524021/2000000000 : ℝ)^21 ≤ (10373516010073/20000000000000 : ℝ)^17 := by
    have hnat : (1175524021 : ℕ)^21*20000000000000^17 ≤ 10373516010073^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175524021 2000000000 10373516010073 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406910103/1000000000 : ℝ)^21 ≤ (8232955524761/25000000000000 : ℝ)^17 := by
    have hnat : (406910103 : ℕ)^21*25000000000000^17 ≤ 8232955524761^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406910103 1000000000 8232955524761 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272023701/1250000000 : ℝ)^21 ≤ (3800149459443/25000000000000 : ℝ)^17 := by
    have hnat : (272023701 : ℕ)^21*25000000000000^17 ≤ 3800149459443^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272023701 1250000000 3800149459443 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1175524021/2000000000 : ℝ), (-406910103/1000000000 : ℝ), (-272023701/1250000000 : ℝ)] ![(10373516010073/20000000000000 : ℝ), (8232955524761/25000000000000 : ℝ), (3800149459443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1175524021/2000000000 : ℝ)|^21 ≤ (10373516010073/20000000000000 : ℝ)^17
        have hw : |(1175524021/2000000000 : ℝ)|=(1175524021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406910103/1000000000 : ℝ)|^21 ≤ (8232955524761/25000000000000 : ℝ)^17
        have hw : |(-406910103/1000000000 : ℝ)|=(406910103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272023701/1250000000 : ℝ)|^21 ≤ (3800149459443/25000000000000 : ℝ)^17
        have hw : |(-272023701/1250000000 : ℝ)|=(272023701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5055659/10000000000 : ℝ)*x 0 + (-651834419/5000000000 : ℝ)*x 1 + (9340678243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5055659/10000000000 : ℝ)^21 ≤ (339044001/4000000000000 : ℝ)^17 := by
    have hnat : (5055659 : ℕ)^21*4000000000000^17 ≤ 339044001^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055659 10000000000 339044001 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651834419/5000000000 : ℝ)^21 ≤ (2017954455793/25000000000000 : ℝ)^17 := by
    have hnat : (651834419 : ℕ)^21*25000000000000^17 ≤ 2017954455793^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651834419 5000000000 2017954455793 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9340678243/10000000000 : ℝ)^21 ≤ (91919706061497/100000000000000 : ℝ)^17 := by
    have hnat : (9340678243 : ℕ)^21*100000000000000^17 ≤ 91919706061497^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9340678243 10000000000 91919706061497 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5055659/10000000000 : ℝ), (-651834419/5000000000 : ℝ), (9340678243/10000000000 : ℝ)] ![(339044001/4000000000000 : ℝ), (2017954455793/25000000000000 : ℝ), (91919706061497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5055659/10000000000 : ℝ)|^21 ≤ (339044001/4000000000000 : ℝ)^17
        have hw : |(-5055659/10000000000 : ℝ)|=(5055659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651834419/5000000000 : ℝ)|^21 ≤ (2017954455793/25000000000000 : ℝ)^17
        have hw : |(-651834419/5000000000 : ℝ)|=(651834419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9340678243/10000000000 : ℝ)|^21 ≤ (91919706061497/100000000000000 : ℝ)^17
        have hw : |(9340678243/10000000000 : ℝ)|=(9340678243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2347394963/5000000000 : ℝ)*x 0 + (-4021043291/10000000000 : ℝ)*x 1 + (3594260999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2347394963/5000000000 : ℝ)^21 ≤ (39296093554019/100000000000000 : ℝ)^17 := by
    have hnat : (2347394963 : ℕ)^21*100000000000000^17 ≤ 39296093554019^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347394963 5000000000 39296093554019 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021043291/10000000000 : ℝ)^21 ≤ (32452038594307/100000000000000 : ℝ)^17 := by
    have hnat : (4021043291 : ℕ)^21*100000000000000^17 ≤ 32452038594307^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021043291 10000000000 32452038594307 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3594260999/10000000000 : ℝ)^21 ≤ (28251867828711/100000000000000 : ℝ)^17 := by
    have hnat : (3594260999 : ℕ)^21*100000000000000^17 ≤ 28251867828711^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594260999 10000000000 28251867828711 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2347394963/5000000000 : ℝ), (-4021043291/10000000000 : ℝ), (3594260999/10000000000 : ℝ)] ![(39296093554019/100000000000000 : ℝ), (32452038594307/100000000000000 : ℝ), (28251867828711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2347394963/5000000000 : ℝ)|^21 ≤ (39296093554019/100000000000000 : ℝ)^17
        have hw : |(-2347394963/5000000000 : ℝ)|=(2347394963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4021043291/10000000000 : ℝ)|^21 ≤ (32452038594307/100000000000000 : ℝ)^17
        have hw : |(-4021043291/10000000000 : ℝ)|=(4021043291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3594260999/10000000000 : ℝ)|^21 ≤ (28251867828711/100000000000000 : ℝ)^17
        have hw : |(3594260999/10000000000 : ℝ)|=(3594260999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5357087793/10000000000 : ℝ)*x 0 + (3997562207/10000000000 : ℝ)*x 1 + (36054741/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357087793/10000000000 : ℝ)^21 ≤ (46253787027287/100000000000000 : ℝ)^17 := by
    have hnat : (5357087793 : ℕ)^21*100000000000000^17 ≤ 46253787027287^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357087793 10000000000 46253787027287 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3997562207/10000000000 : ℝ)^21 ≤ (32218104867547/100000000000000 : ℝ)^17 := by
    have hnat : (3997562207 : ℕ)^21*100000000000000^17 ≤ 32218104867547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997562207 10000000000 32218104867547 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36054741/125000000 : ℝ)^21 ≤ (21528108089281/100000000000000 : ℝ)^17 := by
    have hnat : (36054741 : ℕ)^21*100000000000000^17 ≤ 21528108089281^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36054741 125000000 21528108089281 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357087793/10000000000 : ℝ), (3997562207/10000000000 : ℝ), (36054741/125000000 : ℝ)] ![(46253787027287/100000000000000 : ℝ), (32218104867547/100000000000000 : ℝ), (21528108089281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357087793/10000000000 : ℝ)|^21 ≤ (46253787027287/100000000000000 : ℝ)^17
        have hw : |(5357087793/10000000000 : ℝ)|=(5357087793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3997562207/10000000000 : ℝ)|^21 ≤ (32218104867547/100000000000000 : ℝ)^17
        have hw : |(3997562207/10000000000 : ℝ)|=(3997562207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36054741/125000000 : ℝ)|^21 ≤ (21528108089281/100000000000000 : ℝ)^17
        have hw : |(36054741/125000000 : ℝ)|=(36054741/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5472177561/10000000000 : ℝ)*x 0 + (-549124399/1250000000 : ℝ)*x 1 + (-115228843/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472177561/10000000000 : ℝ)^21 ≤ (296777402257/625000000000 : ℝ)^17 := by
    have hnat : (5472177561 : ℕ)^21*625000000000^17 ≤ 296777402257^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472177561 10000000000 296777402257 625000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549124399/1250000000 : ℝ)^21 ≤ (3619965475969/10000000000000 : ℝ)^17 := by
    have hnat : (549124399 : ℕ)^21*10000000000000^17 ≤ 3619965475969^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549124399 1250000000 3619965475969 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115228843/500000000 : ℝ)^21 ≤ (8157980432403/50000000000000 : ℝ)^17 := by
    have hnat : (115228843 : ℕ)^21*50000000000000^17 ≤ 8157980432403^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115228843 500000000 8157980432403 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472177561/10000000000 : ℝ), (-549124399/1250000000 : ℝ), (-115228843/500000000 : ℝ)] ![(296777402257/625000000000 : ℝ), (3619965475969/10000000000000 : ℝ), (8157980432403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472177561/10000000000 : ℝ)|^21 ≤ (296777402257/625000000000 : ℝ)^17
        have hw : |(5472177561/10000000000 : ℝ)|=(5472177561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549124399/1250000000 : ℝ)|^21 ≤ (3619965475969/10000000000000 : ℝ)^17
        have hw : |(-549124399/1250000000 : ℝ)|=(549124399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115228843/500000000 : ℝ)|^21 ≤ (8157980432403/50000000000000 : ℝ)^17
        have hw : |(-115228843/500000000 : ℝ)|=(115228843/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-224343/625000000 : ℝ)*x 0 + (-120186831/1000000000 : ℝ)*x 1 + (9404318007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224343/625000000 : ℝ)^21 ≤ (1388007867/25000000000000 : ℝ)^17 := by
    have hnat : (224343 : ℕ)^21*25000000000000^17 ≤ 1388007867^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224343 625000000 1388007867 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120186831/1000000000 : ℝ)^21 ≤ (7300500274203/100000000000000 : ℝ)^17 := by
    have hnat : (120186831 : ℕ)^21*100000000000000^17 ≤ 7300500274203^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120186831 1000000000 7300500274203 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9404318007/10000000000 : ℝ)^21 ≤ (18538789537193/20000000000000 : ℝ)^17 := by
    have hnat : (9404318007 : ℕ)^21*20000000000000^17 ≤ 18538789537193^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9404318007 10000000000 18538789537193 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224343/625000000 : ℝ), (-120186831/1000000000 : ℝ), (9404318007/10000000000 : ℝ)] ![(1388007867/25000000000000 : ℝ), (7300500274203/100000000000000 : ℝ), (18538789537193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224343/625000000 : ℝ)|^21 ≤ (1388007867/25000000000000 : ℝ)^17
        have hw : |(-224343/625000000 : ℝ)|=(224343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120186831/1000000000 : ℝ)|^21 ≤ (7300500274203/100000000000000 : ℝ)^17
        have hw : |(-120186831/1000000000 : ℝ)|=(120186831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9404318007/10000000000 : ℝ)|^21 ≤ (18538789537193/20000000000000 : ℝ)^17
        have hw : |(9404318007/10000000000 : ℝ)|=(9404318007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-257338899/625000000 : ℝ)*x 0 + (-46321961/100000000 : ℝ)*x 1 + (3561540299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257338899/625000000 : ℝ)^21 ≤ (16707791772053/50000000000000 : ℝ)^17 := by
    have hnat : (257338899 : ℕ)^21*50000000000000^17 ≤ 16707791772053^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257338899 625000000 16707791772053 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46321961/100000000 : ℝ)^21 ≤ (38649917276867/100000000000000 : ℝ)^17 := by
    have hnat : (46321961 : ℕ)^21*100000000000000^17 ≤ 38649917276867^17*100000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46321961 100000000 38649917276867 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3561540299/10000000000 : ℝ)^21 ≤ (6983624790681/25000000000000 : ℝ)^17 := by
    have hnat : (3561540299 : ℕ)^21*25000000000000^17 ≤ 6983624790681^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561540299 10000000000 6983624790681 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257338899/625000000 : ℝ), (-46321961/100000000 : ℝ), (3561540299/10000000000 : ℝ)] ![(16707791772053/50000000000000 : ℝ), (38649917276867/100000000000000 : ℝ), (6983624790681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257338899/625000000 : ℝ)|^21 ≤ (16707791772053/50000000000000 : ℝ)^17
        have hw : |(-257338899/625000000 : ℝ)|=(257338899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46321961/100000000 : ℝ)|^21 ≤ (38649917276867/100000000000000 : ℝ)^17
        have hw : |(-46321961/100000000 : ℝ)|=(46321961/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3561540299/10000000000 : ℝ)|^21 ≤ (6983624790681/25000000000000 : ℝ)^17
        have hw : |(3561540299/10000000000 : ℝ)|=(3561540299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1734161433/5000000000 : ℝ)*x 0 + (4455434697/10000000000 : ℝ)*x 1 + (4386109283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1734161433/5000000000 : ℝ)^21 ≤ (6758531710993/25000000000000 : ℝ)^17 := by
    have hnat : (1734161433 : ℕ)^21*25000000000000^17 ≤ 6758531710993^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734161433 5000000000 6758531710993 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4455434697/10000000000 : ℝ)^21 ≤ (9209074642769/25000000000000 : ℝ)^17 := by
    have hnat : (4455434697 : ℕ)^21*25000000000000^17 ≤ 9209074642769^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455434697 10000000000 9209074642769 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386109283/10000000000 : ℝ)^21 ≤ (36129574576897/100000000000000 : ℝ)^17 := by
    have hnat : (4386109283 : ℕ)^21*100000000000000^17 ≤ 36129574576897^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386109283 10000000000 36129574576897 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1734161433/5000000000 : ℝ), (4455434697/10000000000 : ℝ), (4386109283/10000000000 : ℝ)] ![(6758531710993/25000000000000 : ℝ), (9209074642769/25000000000000 : ℝ), (36129574576897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1734161433/5000000000 : ℝ)|^21 ≤ (6758531710993/25000000000000 : ℝ)^17
        have hw : |(1734161433/5000000000 : ℝ)|=(1734161433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4455434697/10000000000 : ℝ)|^21 ≤ (9209074642769/25000000000000 : ℝ)^17
        have hw : |(4455434697/10000000000 : ℝ)|=(4455434697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386109283/10000000000 : ℝ)|^21 ≤ (36129574576897/100000000000000 : ℝ)^17
        have hw : |(4386109283/10000000000 : ℝ)|=(4386109283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2689584871/5000000000 : ℝ)*x 0 + (-3484212483/10000000000 : ℝ)*x 1 + (-1697159711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689584871/5000000000 : ℝ)^21 ≤ (23244710157883/50000000000000 : ℝ)^17 := by
    have hnat : (2689584871 : ℕ)^21*50000000000000^17 ≤ 23244710157883^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689584871 5000000000 23244710157883 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3484212483/10000000000 : ℝ)^21 ≤ (1699200249717/6250000000000 : ℝ)^17 := by
    have hnat : (3484212483 : ℕ)^21*6250000000000^17 ≤ 1699200249717^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3484212483 10000000000 1699200249717 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1697159711/5000000000 : ℝ)^21 ≤ (5264675135047/20000000000000 : ℝ)^17 := by
    have hnat : (1697159711 : ℕ)^21*20000000000000^17 ≤ 5264675135047^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697159711 5000000000 5264675135047 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689584871/5000000000 : ℝ), (-3484212483/10000000000 : ℝ), (-1697159711/5000000000 : ℝ)] ![(23244710157883/50000000000000 : ℝ), (1699200249717/6250000000000 : ℝ), (5264675135047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689584871/5000000000 : ℝ)|^21 ≤ (23244710157883/50000000000000 : ℝ)^17
        have hw : |(2689584871/5000000000 : ℝ)|=(2689584871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3484212483/10000000000 : ℝ)|^21 ≤ (1699200249717/6250000000000 : ℝ)^17
        have hw : |(-3484212483/10000000000 : ℝ)|=(3484212483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1697159711/5000000000 : ℝ)|^21 ≤ (5264675135047/20000000000000 : ℝ)^17
        have hw : |(-1697159711/5000000000 : ℝ)|=(1697159711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-4109216093/10000000000 : ℝ)*x 0 + (-4109216169/10000000000 : ℝ)*x 1 + (4109216129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109216093/10000000000 : ℝ)^21 ≤ (333333329547/1000000000000 : ℝ)^17 := by
    have hnat : (4109216093 : ℕ)^21*1000000000000^17 ≤ 333333329547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216093 10000000000 333333329547 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4109216169/10000000000 : ℝ)^21 ≤ (1666666685813/5000000000000 : ℝ)^17 := by
    have hnat : (4109216169 : ℕ)^21*5000000000000^17 ≤ 1666666685813^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216169 10000000000 1666666685813 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4109216129/10000000000 : ℝ)^21 ≤ (33333333315439/100000000000000 : ℝ)^17 := by
    have hnat : (4109216129 : ℕ)^21*100000000000000^17 ≤ 33333333315439^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216129 10000000000 33333333315439 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4109216093/10000000000 : ℝ), (-4109216169/10000000000 : ℝ), (4109216129/10000000000 : ℝ)] ![(333333329547/1000000000000 : ℝ), (1666666685813/5000000000000 : ℝ), (33333333315439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4109216093/10000000000 : ℝ)|^21 ≤ (333333329547/1000000000000 : ℝ)^17
        have hw : |(-4109216093/10000000000 : ℝ)|=(4109216093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4109216169/10000000000 : ℝ)|^21 ≤ (1666666685813/5000000000000 : ℝ)^17
        have hw : |(-4109216169/10000000000 : ℝ)|=(4109216169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4109216129/10000000000 : ℝ)|^21 ≤ (33333333315439/100000000000000 : ℝ)^17
        have hw : |(4109216129/10000000000 : ℝ)|=(4109216129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4109216093/10000000000 : ℝ)*x 0 + (4109216169/10000000000 : ℝ)*x 1 + (4109216129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109216093/10000000000 : ℝ)^21 ≤ (333333329547/1000000000000 : ℝ)^17 := by
    have hnat : (4109216093 : ℕ)^21*1000000000000^17 ≤ 333333329547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216093 10000000000 333333329547 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4109216169/10000000000 : ℝ)^21 ≤ (1666666685813/5000000000000 : ℝ)^17 := by
    have hnat : (4109216169 : ℕ)^21*5000000000000^17 ≤ 1666666685813^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216169 10000000000 1666666685813 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4109216129/10000000000 : ℝ)^21 ≤ (33333333315439/100000000000000 : ℝ)^17 := by
    have hnat : (4109216129 : ℕ)^21*100000000000000^17 ≤ 33333333315439^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216129 10000000000 33333333315439 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109216093/10000000000 : ℝ), (4109216169/10000000000 : ℝ), (4109216129/10000000000 : ℝ)] ![(333333329547/1000000000000 : ℝ), (1666666685813/5000000000000 : ℝ), (33333333315439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109216093/10000000000 : ℝ)|^21 ≤ (333333329547/1000000000000 : ℝ)^17
        have hw : |(4109216093/10000000000 : ℝ)|=(4109216093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4109216169/10000000000 : ℝ)|^21 ≤ (1666666685813/5000000000000 : ℝ)^17
        have hw : |(4109216169/10000000000 : ℝ)|=(4109216169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4109216129/10000000000 : ℝ)|^21 ≤ (33333333315439/100000000000000 : ℝ)^17
        have hw : |(4109216129/10000000000 : ℝ)|=(4109216129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322009_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4109216093/10000000000 : ℝ)*x 0 + (-4109216169/10000000000 : ℝ)*x 1 + (-4109216129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109216093/10000000000 : ℝ)^21 ≤ (333333329547/1000000000000 : ℝ)^17 := by
    have hnat : (4109216093 : ℕ)^21*1000000000000^17 ≤ 333333329547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216093 10000000000 333333329547 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4109216169/10000000000 : ℝ)^21 ≤ (1666666685813/5000000000000 : ℝ)^17 := by
    have hnat : (4109216169 : ℕ)^21*5000000000000^17 ≤ 1666666685813^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216169 10000000000 1666666685813 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4109216129/10000000000 : ℝ)^21 ≤ (33333333315439/100000000000000 : ℝ)^17 := by
    have hnat : (4109216129 : ℕ)^21*100000000000000^17 ≤ 33333333315439^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109216129 10000000000 33333333315439 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109216093/10000000000 : ℝ), (-4109216169/10000000000 : ℝ), (-4109216129/10000000000 : ℝ)] ![(333333329547/1000000000000 : ℝ), (1666666685813/5000000000000 : ℝ), (33333333315439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109216093/10000000000 : ℝ)|^21 ≤ (333333329547/1000000000000 : ℝ)^17
        have hw : |(4109216093/10000000000 : ℝ)|=(4109216093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4109216169/10000000000 : ℝ)|^21 ≤ (1666666685813/5000000000000 : ℝ)^17
        have hw : |(-4109216169/10000000000 : ℝ)|=(4109216169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4109216129/10000000000 : ℝ)|^21 ≤ (33333333315439/100000000000000 : ℝ)^17
        have hw : |(-4109216129/10000000000 : ℝ)|=(4109216129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322009 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4126708973/10000000000 : ℝ)*X 1 0+(455251361/1000000000 : ℝ)*X 1 1+(909084653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5115624721/10000000000 : ℝ)*X 2 0+(-4299884877/10000000000 : ℝ)*X 2 1+(-1106561/3906250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-1212259/2500000000 : ℝ)*X 0 0+(-1516771839/10000000000 : ℝ)*X 0 1+(920391883/1000000000 : ℝ)*X 0 2+(-1212259/2500000000 : ℝ)*X 1 0+(-1516771839/10000000000 : ℝ)*X 1 1+(920391883/1000000000 : ℝ)*X 1 2+(-1212259/2500000000 : ℝ)*X 2 0+(-1516771839/10000000000 : ℝ)*X 2 1+(920391883/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-408779231/1000000000 : ℝ)*X 0 0+(-8084161/16000000 : ℝ)*X 0 1+(3134047249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3471817009/10000000000 : ℝ)*X 1 0+(5241169007/10000000000 : ℝ)*X 1 1+(3559179473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1175524021/2000000000 : ℝ)*X 2 0+(-406910103/1000000000 : ℝ)*X 2 1+(-272023701/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5055659/10000000000 : ℝ)*X 0 0+(-651834419/5000000000 : ℝ)*X 0 1+(9340678243/10000000000 : ℝ)*X 0 2+(-5055659/10000000000 : ℝ)*X 1 0+(-651834419/5000000000 : ℝ)*X 1 1+(9340678243/10000000000 : ℝ)*X 1 2+(-5055659/10000000000 : ℝ)*X 2 0+(-651834419/5000000000 : ℝ)*X 2 1+(9340678243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2347394963/5000000000 : ℝ)*X 0 0+(-4021043291/10000000000 : ℝ)*X 0 1+(3594260999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5357087793/10000000000 : ℝ)*X 1 0+(3997562207/10000000000 : ℝ)*X 1 1+(36054741/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5472177561/10000000000 : ℝ)*X 2 0+(-549124399/1250000000 : ℝ)*X 2 1+(-115228843/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-224343/625000000 : ℝ)*X 0 0+(-120186831/1000000000 : ℝ)*X 0 1+(9404318007/10000000000 : ℝ)*X 0 2+(-224343/625000000 : ℝ)*X 1 0+(-120186831/1000000000 : ℝ)*X 1 1+(9404318007/10000000000 : ℝ)*X 1 2+(-224343/625000000 : ℝ)*X 2 0+(-120186831/1000000000 : ℝ)*X 2 1+(9404318007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-257338899/625000000 : ℝ)*X 0 0+(-46321961/100000000 : ℝ)*X 0 1+(3561540299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1734161433/5000000000 : ℝ)*X 1 0+(4455434697/10000000000 : ℝ)*X 1 1+(4386109283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2689584871/5000000000 : ℝ)*X 2 0+(-3484212483/10000000000 : ℝ)*X 2 1+(-1697159711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((36177/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36177/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3491865579206838900513/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187609270501/1000000000000 : ℝ)*(base1) + (271861567139/500000000000 : ℝ)*(base7) + (25985245893/200000000000 : ℝ)*(base50) + (617398602791/1000000000000 : ℝ)*(base54) + (924432486017/1000000000000 : ℝ)*(base60) + (3200833740351/1000000000000 : ℝ)*(major_s0_0) + (3200833740351/1000000000000 : ℝ)*(major_s0_1) + (64585878439/25000000000 : ℝ)*(major_s0_2) + (138456377/500000000000 : ℝ)*(sp_s0_6) + (4626789615373/1000000000000 : ℝ)*(sp_s0_7) + (554897543109/125000000000 : ℝ)*(sp_s0_8) + (3821734387121/1000000000000 : ℝ)*(sp_s0_9) + (279397472263/200000000000 : ℝ)*(sp_s0_13) + (591937/12500000000 : ℝ)*(sp_s0_16) + (414637253271/250000000000 : ℝ)*(f.failure) + (554897543109/125000000000 : ℝ)*(f.sum) + (1551934553948463/2500000000000000000000000000 : ℝ)*base63 + (8161216699953/50000000000000000000000000 : ℝ)*base64 + (794403630133377/2000000000000000000000000000 : ℝ)*base67 + (1342185357337/62500000000000000000000000 : ℝ)*base69 + (1687428162402633/2500000000000000000000000000 : ℝ)*base70 + (401512914333377/2000000000000000000000000000 : ℝ)*base73 + (1108751113845017/2500000000000000000000000000 : ℝ)*base74 + (1031561111345017/2500000000000000000000000000 : ℝ)*base77 + (678114558833377/1000000000000000000000000000 : ℝ)*base79 + (471/2500000000000000 : ℝ)*base86 + (471/2500000000000000 : ℝ)*base88 + (471/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7357/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-7357/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24286515870071231565321/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1041316793333/1000000000000 : ℝ)*(base1) + (3322054029/3125000000 : ℝ)*(base7) + (134072101833/200000000000 : ℝ)*(base40) + (3877243/1000000000000 : ℝ)*(base50) + (972458187349/1000000000000 : ℝ)*(base54) + (328347289711/500000000000 : ℝ)*(base60) + (1607827135759/500000000000 : ℝ)*(major_s0_0) + (1607827135759/500000000000 : ℝ)*(major_s0_1) + (280399510521/125000000000 : ℝ)*(major_s0_2) + (13361633/200000000000 : ℝ)*(sp_s0_9) + (5212155261349/1000000000000 : ℝ)*(sp_s0_14) + (4170838468017/1000000000000 : ℝ)*(sp_s0_15) + (1599156736251/500000000000 : ℝ)*(sp_s0_16) + (715510751273/1000000000000 : ℝ)*(sp_s0_20) + (66649137707/40000000000 : ℝ)*(f.failure) + (4170838468017/1000000000000 : ℝ)*(f.sum) + (799578082424981/1250000000000000000000000000 : ℝ)*base62 + (102227795515967/250000000000000000000000000 : ℝ)*base64 + (201215417499407/1000000000000000000000000000 : ℝ)*base66 + (72433898717343/312500000000000000000000000 : ℝ)*base69 + (111631801580241/625000000000000000000000000 : ℝ)*base70 + (217318571600593/1000000000000000000000000000 : ℝ)*base73 + (719979650455647/1250000000000000000000000000 : ℝ)*base75 + (1372065620330647/1250000000000000000000000000 : ℝ)*base76 + (111573645150593/500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (193/400000000000000 : ℝ)*base87 + (193/400000000000000 : ℝ)*base89 + (593/400000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36887/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36887/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58370523722893510739001/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2751326447337/1000000000000 : ℝ)*(base1) + (1247525659351/1000000000000 : ℝ)*(base7) + (1226448237681/1000000000000 : ℝ)*(base40) + (543658760093/1000000000000 : ℝ)*(base50) + (58044228407/250000000000 : ℝ)*(base60) + (1451092570367/500000000000 : ℝ)*(major_s0_0) + (1451092570367/500000000000 : ℝ)*(major_s0_1) + (1451092570367/500000000000 : ℝ)*(major_s0_2) + (4630659/125000000000 : ℝ)*(sp_s0_1) + (21515221/1000000000000 : ℝ)*(sp_s0_2) + (68415683/1000000000000 : ℝ)*(sp_s0_9) + (3177266894879/500000000000 : ℝ)*(sp_s0_21) + (3603170297149/1000000000000 : ℝ)*(sp_s0_22) + (900779352879/250000000000 : ℝ)*(sp_s0_23) + (751900393993/500000000000 : ℝ)*(f.failure) + (3603207342421/1000000000000 : ℝ)*(f.sum) + (282402540079911/625000000000000000000000000 : ℝ)*base63 + (78086176806209/1000000000000000000000000000 : ℝ)*base64 + (569794792606209/1000000000000000000000000000 : ℝ)*base67 + (3589261829911/1250000000000000000000000000 : ℝ)*base69 + (640507437149311/5000000000000000000000000000 : ℝ)*base71 + (205457106293791/1000000000000000000000000000 : ℝ)*base72 + (1217076857079911/1250000000000000000000000000 : ℝ)*base75 + (253478531204911/1250000000000000000000000000 : ℝ)*base76 + (47062425606209/500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (907/5000000000000000 : ℝ)*base87 + (907/5000000000000000 : ℝ)*base89 + (907/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (36177/100000 : ℝ) ^ (41/8 : ℝ) ≤ (545716164561313089/100000000000000000000 : ℝ) := by
    have hpowers : (36177/100000 : ℝ)^41 ≤ (545716164561313089/100000000000000000000 : ℝ)^8 := by
      have hnat : (36177 : ℕ)^41*100000000000000000000^8 ≤ 545716164561313089^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36177 100000 545716164561313089 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36177/100000 : ℝ)) (X := (545716164561313089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100545716164561313089/100000000000000000000 : ℝ) ≤ (10010624811635389/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100545716164561313089/100000000000000000000 : ℝ)^8 ≤ (10010624811635389/10000000000000000 : ℝ)^41 := by
      have hnat : (100545716164561313089 : ℕ)^8*10000000000000000^41 ≤ 10010624811635389^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100545716164561313089 100000000000000000000 10010624811635389 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010624811635389/10000000000000000 : ℝ)) (X := (100545716164561313089/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50545716164561313089/50000000000000000000 : ℝ) ≤ (1252650413698881/1250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50545716164561313089/50000000000000000000 : ℝ)^8 ≤ (1252650413698881/1250000000000000 : ℝ)^41 := by
      have hnat : (50545716164561313089 : ℕ)^8*1250000000000000^41 ≤ 1252650413698881^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50545716164561313089 50000000000000000000 1252650413698881 1250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252650413698881/1250000000000000 : ℝ)) (X := (50545716164561313089/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3541603878463/1205900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10578497955659/3617700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (36177/100000 : ℝ)) (alpha := (3541603878463/1205900000000000 : ℝ)) (beta := (10578497955659/3617700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36177/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3541603878463/1205900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10578497955659/3617700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7357/12500 : ℝ) ^ (41/8 : ℝ) ≤ (6609636228092336719/100000000000000000000 : ℝ) := by
    have hpowers : (7357/12500 : ℝ)^41 ≤ (6609636228092336719/100000000000000000000 : ℝ)^8 := by
      have hnat : (7357 : ℕ)^41*100000000000000000000^8 ≤ 6609636228092336719^8*12500^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 12500 6609636228092336719 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/12500 : ℝ)) (X := (6609636228092336719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106609636228092336719/100000000000000000000 : ℝ) ≤ (5062834188187403/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (106609636228092336719/100000000000000000000 : ℝ)^8 ≤ (5062834188187403/5000000000000000 : ℝ)^41 := by
      have hnat : (106609636228092336719 : ℕ)^8*5000000000000000^41 ≤ 5062834188187403^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106609636228092336719 100000000000000000000 5062834188187403 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5062834188187403/5000000000000000 : ℝ)) (X := (106609636228092336719/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56609636228092336719/50000000000000000000 : ℝ) ≤ (5122607135932361/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (56609636228092336719/50000000000000000000 : ℝ)^8 ≤ (5122607135932361/5000000000000000 : ℝ)^41 := by
      have hnat : (56609636228092336719 : ℕ)^8*5000000000000000^41 ≤ 5122607135932361^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56609636228092336719 50000000000000000000 5122607135932361 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5122607135932361/5000000000000000 : ℝ)) (X := (56609636228092336719/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(62834188187403/2942800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(4269496267497/210200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (7357/12500 : ℝ)) (alpha := (62834188187403/2942800000000000 : ℝ)) (beta := (4269496267497/210200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (7357/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(62834188187403/2942800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(4269496267497/210200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36887/100000 : ℝ) ^ (41/8 : ℝ) ≤ (602873015835096719/100000000000000000000 : ℝ) := by
    have hpowers : (36887/100000 : ℝ)^41 ≤ (602873015835096719/100000000000000000000 : ℝ)^8 := by
      have hnat : (36887 : ℕ)^41*100000000000000000000^8 ≤ 602873015835096719^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36887 100000 602873015835096719 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36887/100000 : ℝ)) (X := (602873015835096719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100602873015835096719/100000000000000000000 : ℝ) ≤ (10011734938740873/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100602873015835096719/100000000000000000000 : ℝ)^8 ≤ (10011734938740873/10000000000000000 : ℝ)^41 := by
      have hnat : (100602873015835096719 : ℕ)^8*10000000000000000^41 ≤ 10011734938740873^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100602873015835096719 100000000000000000000 10011734938740873 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011734938740873/10000000000000000 : ℝ)) (X := (100602873015835096719/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50602873015835096719/50000000000000000000 : ℝ) ≤ (5011706705998527/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50602873015835096719/50000000000000000000 : ℝ)^8 ≤ (5011706705998527/5000000000000000 : ℝ)^41 := by
      have hnat : (50602873015835096719 : ℕ)^8*5000000000000000^41 ≤ 5011706705998527^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50602873015835096719 50000000000000000000 5011706705998527 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011706705998527/5000000000000000 : ℝ)) (X := (50602873015835096719/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11734938740873/3688700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(11678473256181/3688700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (36887/100000 : ℝ)) (alpha := (11734938740873/3688700000000000 : ℝ)) (beta := (11678473256181/3688700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (36887/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11734938740873/3688700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(11678473256181/3688700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4109216093/10000000000 : ℝ)*X 0 0+(-4109216169/10000000000 : ℝ)*X 0 1+(4109216129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4109216093/10000000000 : ℝ)*X 1 0+(4109216169/10000000000 : ℝ)*X 1 1+(4109216129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4109216093/10000000000 : ℝ)*X 2 0+(-4109216169/10000000000 : ℝ)*X 2 1+(-4109216129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322009_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-19618972064799495482199629820297849/2337530849915000000000000000000000 : ℝ) := by norm_num
    linear_combination (24459110391/125000000000 : ℝ)*(base1) + (82931222059/500000000000 : ℝ)*(base3) + (127692934551/200000000000 : ℝ)*(base6) + (9393/250000000000 : ℝ)*(base13) + (71387/1000000000000 : ℝ)*(base15) + (28422646921/500000000000 : ℝ)*(base39) + (687152961643/1000000000000 : ℝ)*(base40) + (65161398999/100000000000 : ℝ)*(base50) + (38657797863/62500000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (1603085928159/500000000000 : ℝ)*(sp_s1_0) + (3176361383493/1000000000000 : ℝ)*(sp_s1_1) + (3010499010763/1000000000000 : ℝ)*(sp_s1_2) + (3010499010763/1000000000000 : ℝ)*(f.sum) + (77832033525246519/193841185000000000000000000000 : ℝ)*base63 + (65771966697423/184435000000000000000000000 : ℝ)*base64 + (3494629086939/5255000000000000000000000 : ℝ)*base67 + (159953431858937/368870000000000000000000000 : ℝ)*base69 + (1819108164272279561/4448203330000000000000000000000 : ℝ)*base70 + (92324759278777/120590000000000000000000000 : ℝ)*base73 + (3142123284091/10510000000000000000000000 : ℝ)*base75 + (40796453646127/120590000000000000000000000 : ℝ)*base76 + (128723553148565843/126740090000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c322010_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-410921613/1000000000 : ℝ)*x 0 + (-410921613/1000000000 : ℝ)*x 1 + (-410921613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ)] ![(1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322010_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (410921613/1000000000 : ℝ)*x 0 + (410921613/1000000000 : ℝ)*x 1 + (-410921613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410921613/1000000000 : ℝ), (410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ)] ![(1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322010_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (410921613/1000000000 : ℝ)*x 0 + (-410921613/1000000000 : ℝ)*x 1 + (410921613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ), (410921613/1000000000 : ℝ)] ![(1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322010_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (410921613/1000000000 : ℝ)*x 0 + (-410921613/1000000000 : ℝ)*x 1 + (-410921613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410921613/1000000000 : ℝ)^21 ≤ (1666666666273/5000000000000 : ℝ)^17 := by
    have hnat : (410921613 : ℕ)^21*5000000000000^17 ≤ 1666666666273^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410921613 1000000000 1666666666273 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ), (-410921613/1000000000 : ℝ)] ![(1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ), (1666666666273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410921613/1000000000 : ℝ)|^21 ≤ (1666666666273/5000000000000 : ℝ)^17
        have hw : |(-410921613/1000000000 : ℝ)|=(410921613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322010 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-410921613/1000000000 : ℝ)*X 0 0+(-410921613/1000000000 : ℝ)*X 0 1+(-410921613/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322010_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((410921613/1000000000 : ℝ)*X 1 0+(410921613/1000000000 : ℝ)*X 1 1+(-410921613/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322010_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((410921613/1000000000 : ℝ)*X 2 0+(-410921613/1000000000 : ℝ)*X 2 1+(410921613/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322010_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((410921613/1000000000 : ℝ)*X 0 0+(-410921613/1000000000 : ℝ)*X 0 1+(-410921613/1000000000 : ℝ)*X 0 2+(410921613/1000000000 : ℝ)*X 1 0+(-410921613/1000000000 : ℝ)*X 1 1+(-410921613/1000000000 : ℝ)*X 1 2+(410921613/1000000000 : ℝ)*X 2 0+(-410921613/1000000000 : ℝ)*X 2 1+(-410921613/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322010_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-4196516169865236794187/500000000000000000000 : ℝ) := by norm_num
    linear_combination (277317882417/1000000000000 : ℝ)*(base39) + (89862348307/1000000000000 : ℝ)*(base40) + (277317882417/1000000000000 : ℝ)*(base49) + (89862348307/1000000000000 : ℝ)*(base50) + (277317882417/1000000000000 : ℝ)*(base59) + (89862348307/1000000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s0_0) + (19299/10000 : ℝ)*(major_s0_1) + (19299/10000 : ℝ)*(major_s0_2) + (1398838723287/500000000000 : ℝ)*(sp_s0_0) + (1398838723287/500000000000 : ℝ)*(sp_s0_1) + (1398838723287/500000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (1398838723287/500000000000 : ℝ)*(f.sum) + (396359389/500000000000000000000 : ℝ)*base62 + (241687/976562500000000000 : ℝ)*base64 + (241687/976562500000000000 : ℝ)*base66 + (130232591/500000000000000000000 : ℝ)*base68 + (71191527/250000000000000000000 : ℝ)*base71 + (241687/976562500000000000 : ℝ)*base72 + (130232591/500000000000000000000 : ℝ)*base74 + (130232591/500000000000000000000 : ℝ)*base77 + (111593281/500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b003 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 9 ≤ c.val) (hhi : c.val < 11)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=9 ∨ c=10 := by omega
  rcases hc with rfl|rfl
  · exact collision_c322009 p hpa (by linarith only [hpb]) X hX
  · exact collision_c322010 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 9 ≤ c.val) (hhi : c.val < 11)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b003 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

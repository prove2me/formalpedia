-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:50.220998+00:00
-- url     : https://prove2.me/submissions/4e732a68-6b9d-4fda-93f3-2d9d9b8ab8b2

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
theorem collision_support_c326038_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-691793523/10000000000 : ℝ)*x 0 + (-4468948123/10000000000 : ℝ)*x 1 + (-322954953/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691793523/10000000000 : ℝ)^89 ≤ (963085340533/25000000000000 : ℝ)^73 := by
    have hnat : (691793523 : ℕ)^89*25000000000000^73 ≤ 963085340533^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691793523 10000000000 963085340533 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4468948123/10000000000 : ℝ)^89 ≤ (37457430696083/100000000000000 : ℝ)^73 := by
    have hnat : (4468948123 : ℕ)^89*100000000000000^73 ≤ 37457430696083^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468948123 10000000000 37457430696083 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322954953/500000000 : ℝ)^89 ≤ (3668139245611/6250000000000 : ℝ)^73 := by
    have hnat : (322954953 : ℕ)^89*6250000000000^73 ≤ 3668139245611^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322954953 500000000 3668139245611 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-691793523/10000000000 : ℝ), (-4468948123/10000000000 : ℝ), (-322954953/500000000 : ℝ)] ![(963085340533/25000000000000 : ℝ), (37457430696083/100000000000000 : ℝ), (3668139245611/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-691793523/10000000000 : ℝ)|^89 ≤ (963085340533/25000000000000 : ℝ)^73
        have hw : |(-691793523/10000000000 : ℝ)|=(691793523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4468948123/10000000000 : ℝ)|^89 ≤ (37457430696083/100000000000000 : ℝ)^73
        have hw : |(-4468948123/10000000000 : ℝ)|=(4468948123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322954953/500000000 : ℝ)|^89 ≤ (3668139245611/6250000000000 : ℝ)^73
        have hw : |(-322954953/500000000 : ℝ)|=(322954953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5007238111/10000000000 : ℝ)*x 0 + (-2056674493/5000000000 : ℝ)*x 1 + (1503927393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5007238111/10000000000 : ℝ)^89 ≤ (43028555158357/100000000000000 : ℝ)^73 := by
    have hnat : (5007238111 : ℕ)^89*100000000000000^73 ≤ 43028555158357^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007238111 10000000000 43028555158357 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056674493/5000000000 : ℝ)^89 ≤ (677120052721/2000000000000 : ℝ)^73 := by
    have hnat : (2056674493 : ℕ)^89*2000000000000^73 ≤ 677120052721^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056674493 5000000000 677120052721 2000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503927393/5000000000 : ℝ)^89 ≤ (361178784273/1562500000000 : ℝ)^73 := by
    have hnat : (1503927393 : ℕ)^89*1562500000000^73 ≤ 361178784273^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503927393 5000000000 361178784273 1562500000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5007238111/10000000000 : ℝ), (-2056674493/5000000000 : ℝ), (1503927393/5000000000 : ℝ)] ![(43028555158357/100000000000000 : ℝ), (677120052721/2000000000000 : ℝ), (361178784273/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5007238111/10000000000 : ℝ)|^89 ≤ (43028555158357/100000000000000 : ℝ)^73
        have hw : |(5007238111/10000000000 : ℝ)|=(5007238111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056674493/5000000000 : ℝ)|^89 ≤ (677120052721/2000000000000 : ℝ)^73
        have hw : |(-2056674493/5000000000 : ℝ)|=(2056674493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503927393/5000000000 : ℝ)|^89 ≤ (361178784273/1562500000000 : ℝ)^73
        have hw : |(1503927393/5000000000 : ℝ)|=(1503927393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7772026113/10000000000 : ℝ)*x 0 + (-193848297/1250000000 : ℝ)*x 1 + (-560349021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7772026113/10000000000 : ℝ)^89 ≤ (14708614101183/20000000000000 : ℝ)^73 := by
    have hnat : (7772026113 : ℕ)^89*20000000000000^73 ≤ 14708614101183^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7772026113 10000000000 14708614101183 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193848297/1250000000 : ℝ)^89 ≤ (5153576367953/50000000000000 : ℝ)^73 := by
    have hnat : (193848297 : ℕ)^89*50000000000000^73 ≤ 5153576367953^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193848297 1250000000 5153576367953 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560349021/2500000000 : ℝ)^89 ≤ (8074888374119/50000000000000 : ℝ)^73 := by
    have hnat : (560349021 : ℕ)^89*50000000000000^73 ≤ 8074888374119^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560349021 2500000000 8074888374119 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7772026113/10000000000 : ℝ), (-193848297/1250000000 : ℝ), (-560349021/2500000000 : ℝ)] ![(14708614101183/20000000000000 : ℝ), (5153576367953/50000000000000 : ℝ), (8074888374119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7772026113/10000000000 : ℝ)|^89 ≤ (14708614101183/20000000000000 : ℝ)^73
        have hw : |(7772026113/10000000000 : ℝ)|=(7772026113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193848297/1250000000 : ℝ)|^89 ≤ (5153576367953/50000000000000 : ℝ)^73
        have hw : |(-193848297/1250000000 : ℝ)|=(193848297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560349021/2500000000 : ℝ)|^89 ≤ (8074888374119/50000000000000 : ℝ)^73
        have hw : |(-560349021/2500000000 : ℝ)|=(560349021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-341553493/5000000000 : ℝ)*x 0 + (-70342407/156250000 : ℝ)*x 1 + (-6433970861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341553493/5000000000 : ℝ)^89 ≤ (3793448576227/100000000000000 : ℝ)^73 := by
    have hnat : (341553493 : ℕ)^89*100000000000000^73 ≤ 3793448576227^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341553493 5000000000 3793448576227 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70342407/156250000 : ℝ)^89 ≤ (37794574634103/100000000000000 : ℝ)^73 := by
    have hnat : (70342407 : ℕ)^89*100000000000000^73 ≤ 37794574634103^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70342407 156250000 37794574634103 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6433970861/10000000000 : ℝ)^89 ≤ (58411976774867/100000000000000 : ℝ)^73 := by
    have hnat : (6433970861 : ℕ)^89*100000000000000^73 ≤ 58411976774867^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6433970861 10000000000 58411976774867 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341553493/5000000000 : ℝ), (-70342407/156250000 : ℝ), (-6433970861/10000000000 : ℝ)] ![(3793448576227/100000000000000 : ℝ), (37794574634103/100000000000000 : ℝ), (58411976774867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341553493/5000000000 : ℝ)|^89 ≤ (3793448576227/100000000000000 : ℝ)^73
        have hw : |(-341553493/5000000000 : ℝ)|=(341553493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70342407/156250000 : ℝ)|^89 ≤ (37794574634103/100000000000000 : ℝ)^73
        have hw : |(-70342407/156250000 : ℝ)|=(70342407/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6433970861/10000000000 : ℝ)|^89 ≤ (58411976774867/100000000000000 : ℝ)^73
        have hw : |(-6433970861/10000000000 : ℝ)|=(6433970861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5008245119/10000000000 : ℝ)*x 0 + (2092524857/5000000000 : ℝ)*x 1 + (-732391361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5008245119/10000000000 : ℝ)^89 ≤ (21519552769851/50000000000000 : ℝ)^73 := by
    have hnat : (5008245119 : ℕ)^89*50000000000000^73 ≤ 21519552769851^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008245119 10000000000 21519552769851 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092524857/5000000000 : ℝ)^89 ≤ (34576870947987/100000000000000 : ℝ)^73 := by
    have hnat : (2092524857 : ℕ)^89*100000000000000^73 ≤ 34576870947987^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092524857 5000000000 34576870947987 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732391361/2500000000 : ℝ)^89 ≤ (5596005874961/25000000000000 : ℝ)^73 := by
    have hnat : (732391361 : ℕ)^89*25000000000000^73 ≤ 5596005874961^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732391361 2500000000 5596005874961 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5008245119/10000000000 : ℝ), (2092524857/5000000000 : ℝ), (-732391361/2500000000 : ℝ)] ![(21519552769851/50000000000000 : ℝ), (34576870947987/100000000000000 : ℝ), (5596005874961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5008245119/10000000000 : ℝ)|^89 ≤ (21519552769851/50000000000000 : ℝ)^73
        have hw : |(5008245119/10000000000 : ℝ)|=(5008245119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2092524857/5000000000 : ℝ)|^89 ≤ (34576870947987/100000000000000 : ℝ)^73
        have hw : |(2092524857/5000000000 : ℝ)|=(2092524857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732391361/2500000000 : ℝ)|^89 ≤ (5596005874961/25000000000000 : ℝ)^73
        have hw : |(-732391361/2500000000 : ℝ)|=(732391361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5008245037/10000000000 : ℝ)*x 0 + (-807067867/2000000000 : ℝ)*x 1 + (3089860381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5008245037/10000000000 : ℝ)^89 ≤ (43039104680573/100000000000000 : ℝ)^73 := by
    have hnat : (5008245037 : ℕ)^89*100000000000000^73 ≤ 43039104680573^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008245037 10000000000 43039104680573 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807067867/2000000000 : ℝ)^89 ≤ (16537414531169/50000000000000 : ℝ)^73 := by
    have hnat : (807067867 : ℕ)^89*50000000000000^73 ≤ 16537414531169^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807067867 2000000000 16537414531169 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3089860381/10000000000 : ℝ)^89 ≤ (5971516560311/25000000000000 : ℝ)^73 := by
    have hnat : (3089860381 : ℕ)^89*25000000000000^73 ≤ 5971516560311^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089860381 10000000000 5971516560311 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5008245037/10000000000 : ℝ), (-807067867/2000000000 : ℝ), (3089860381/10000000000 : ℝ)] ![(43039104680573/100000000000000 : ℝ), (16537414531169/50000000000000 : ℝ), (5971516560311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5008245037/10000000000 : ℝ)|^89 ≤ (43039104680573/100000000000000 : ℝ)^73
        have hw : |(5008245037/10000000000 : ℝ)|=(5008245037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-807067867/2000000000 : ℝ)|^89 ≤ (16537414531169/50000000000000 : ℝ)^73
        have hw : |(-807067867/2000000000 : ℝ)|=(807067867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3089860381/10000000000 : ℝ)|^89 ≤ (5971516560311/25000000000000 : ℝ)^73
        have hw : |(3089860381/10000000000 : ℝ)|=(3089860381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1935885661/2500000000 : ℝ)*x 0 + (-745993109/5000000000 : ℝ)*x 1 + (-583099841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935885661/2500000000 : ℝ)^89 ≤ (73214602626113/100000000000000 : ℝ)^73 := by
    have hnat : (1935885661 : ℕ)^89*100000000000000^73 ≤ 73214602626113^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935885661 2500000000 73214602626113 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745993109/5000000000 : ℝ)^89 ≤ (1229085741121/12500000000000 : ℝ)^73 := by
    have hnat : (745993109 : ℕ)^89*12500000000000^73 ≤ 1229085741121^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745993109 5000000000 1229085741121 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583099841/2500000000 : ℝ)^89 ≤ (2119088928869/12500000000000 : ℝ)^73 := by
    have hnat : (583099841 : ℕ)^89*12500000000000^73 ≤ 2119088928869^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583099841 2500000000 2119088928869 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1935885661/2500000000 : ℝ), (-745993109/5000000000 : ℝ), (-583099841/2500000000 : ℝ)] ![(73214602626113/100000000000000 : ℝ), (1229085741121/12500000000000 : ℝ), (2119088928869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1935885661/2500000000 : ℝ)|^89 ≤ (73214602626113/100000000000000 : ℝ)^73
        have hw : |(1935885661/2500000000 : ℝ)|=(1935885661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-745993109/5000000000 : ℝ)|^89 ≤ (1229085741121/12500000000000 : ℝ)^73
        have hw : |(-745993109/5000000000 : ℝ)|=(745993109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-583099841/2500000000 : ℝ)|^89 ≤ (2119088928869/12500000000000 : ℝ)^73
        have hw : |(-583099841/2500000000 : ℝ)|=(583099841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-410721129/10000000000 : ℝ)*x 0 + (-2251653921/5000000000 : ℝ)*x 1 + (-411916763/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410721129/10000000000 : ℝ)^89 ≤ (2040172763663/100000000000000 : ℝ)^73 := by
    have hnat : (410721129 : ℕ)^89*100000000000000^73 ≤ 2040172763663^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410721129 10000000000 2040172763663 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251653921/5000000000 : ℝ)^89 ≤ (37808840979477/100000000000000 : ℝ)^73 := by
    have hnat : (2251653921 : ℕ)^89*100000000000000^73 ≤ 37808840979477^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251653921 5000000000 37808840979477 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411916763/625000000 : ℝ)^89 ≤ (30075493119159/50000000000000 : ℝ)^73 := by
    have hnat : (411916763 : ℕ)^89*50000000000000^73 ≤ 30075493119159^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411916763 625000000 30075493119159 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410721129/10000000000 : ℝ), (-2251653921/5000000000 : ℝ), (-411916763/625000000 : ℝ)] ![(2040172763663/100000000000000 : ℝ), (37808840979477/100000000000000 : ℝ), (30075493119159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410721129/10000000000 : ℝ)|^89 ≤ (2040172763663/100000000000000 : ℝ)^73
        have hw : |(-410721129/10000000000 : ℝ)|=(410721129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251653921/5000000000 : ℝ)|^89 ≤ (37808840979477/100000000000000 : ℝ)^73
        have hw : |(-2251653921/5000000000 : ℝ)|=(2251653921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411916763/625000000 : ℝ)|^89 ≤ (30075493119159/50000000000000 : ℝ)^73
        have hw : |(-411916763/625000000 : ℝ)|=(411916763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (151628863/312500000 : ℝ)*x 0 + (4177926089/10000000000 : ℝ)*x 1 + (-3111041697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151628863/312500000 : ℝ)^89 ≤ (20704512428131/50000000000000 : ℝ)^73 := by
    have hnat : (151628863 : ℕ)^89*50000000000000^73 ≤ 20704512428131^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151628863 312500000 20704512428131 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4177926089/10000000000 : ℝ)^89 ≤ (34505129158109/100000000000000 : ℝ)^73 := by
    have hnat : (4177926089 : ℕ)^89*100000000000000^73 ≤ 34505129158109^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177926089 10000000000 34505129158109 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3111041697/10000000000 : ℝ)^89 ≤ (24085845971047/100000000000000 : ℝ)^73 := by
    have hnat : (3111041697 : ℕ)^89*100000000000000^73 ≤ 24085845971047^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111041697 10000000000 24085845971047 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151628863/312500000 : ℝ), (4177926089/10000000000 : ℝ), (-3111041697/10000000000 : ℝ)] ![(20704512428131/50000000000000 : ℝ), (34505129158109/100000000000000 : ℝ), (24085845971047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151628863/312500000 : ℝ)|^89 ≤ (20704512428131/50000000000000 : ℝ)^73
        have hw : |(151628863/312500000 : ℝ)|=(151628863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4177926089/10000000000 : ℝ)|^89 ≤ (34505129158109/100000000000000 : ℝ)^73
        have hw : |(4177926089/10000000000 : ℝ)|=(4177926089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3111041697/10000000000 : ℝ)|^89 ≤ (24085845971047/100000000000000 : ℝ)^73
        have hw : |(-3111041697/10000000000 : ℝ)|=(3111041697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1322957723/2500000000 : ℝ)*x 0 + (-488221277/1250000000 : ℝ)*x 1 + (2908384147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322957723/2500000000 : ℝ)^89 ≤ (46028459609247/100000000000000 : ℝ)^73 := by
    have hnat : (1322957723 : ℕ)^89*100000000000000^73 ≤ 46028459609247^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322957723 2500000000 46028459609247 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488221277/1250000000 : ℝ)^89 ≤ (31784672761179/100000000000000 : ℝ)^73 := by
    have hnat : (488221277 : ℕ)^89*100000000000000^73 ≤ 31784672761179^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488221277 1250000000 31784672761179 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2908384147/10000000000 : ℝ)^89 ≤ (22186867614459/100000000000000 : ℝ)^73 := by
    have hnat : (2908384147 : ℕ)^89*100000000000000^73 ≤ 22186867614459^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908384147 10000000000 22186867614459 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322957723/2500000000 : ℝ), (-488221277/1250000000 : ℝ), (2908384147/10000000000 : ℝ)] ![(46028459609247/100000000000000 : ℝ), (31784672761179/100000000000000 : ℝ), (22186867614459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322957723/2500000000 : ℝ)|^89 ≤ (46028459609247/100000000000000 : ℝ)^73
        have hw : |(1322957723/2500000000 : ℝ)|=(1322957723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488221277/1250000000 : ℝ)|^89 ≤ (31784672761179/100000000000000 : ℝ)^73
        have hw : |(-488221277/1250000000 : ℝ)|=(488221277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2908384147/10000000000 : ℝ)|^89 ≤ (22186867614459/100000000000000 : ℝ)^73
        have hw : |(2908384147/10000000000 : ℝ)|=(2908384147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_19 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2066618057/2500000000 : ℝ)*x 0 + (-1259071743/10000000000 : ℝ)*x 1 + (-73706923/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066618057/2500000000 : ℝ)^89 ≤ (7928638435337/10000000000000 : ℝ)^73 := by
    have hnat : (2066618057 : ℕ)^89*10000000000000^73 ≤ 7928638435337^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066618057 2500000000 7928638435337 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259071743/10000000000 : ℝ)^89 ≤ (799468334557/10000000000000 : ℝ)^73 := by
    have hnat : (1259071743 : ℕ)^89*10000000000000^73 ≤ 799468334557^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259071743 10000000000 799468334557 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73706923/400000000 : ℝ)^89 ≤ (1589866534821/12500000000000 : ℝ)^73 := by
    have hnat : (73706923 : ℕ)^89*12500000000000^73 ≤ 1589866534821^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73706923 400000000 1589866534821 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066618057/2500000000 : ℝ), (-1259071743/10000000000 : ℝ), (-73706923/400000000 : ℝ)] ![(7928638435337/10000000000000 : ℝ), (799468334557/10000000000000 : ℝ), (1589866534821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066618057/2500000000 : ℝ)|^89 ≤ (7928638435337/10000000000000 : ℝ)^73
        have hw : |(2066618057/2500000000 : ℝ)|=(2066618057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1259071743/10000000000 : ℝ)|^89 ≤ (799468334557/10000000000000 : ℝ)^73
        have hw : |(-1259071743/10000000000 : ℝ)|=(1259071743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73706923/400000000 : ℝ)|^89 ≤ (1589866534821/12500000000000 : ℝ)^73
        have hw : |(-73706923/400000000 : ℝ)|=(73706923/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-414825611/10000000000 : ℝ)*x 0 + (-4601099699/10000000000 : ℝ)*x 1 + (-649811567/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414825611/10000000000 : ℝ)^89 ≤ (1032528362979/50000000000000 : ℝ)^73 := by
    have hnat : (414825611 : ℕ)^89*50000000000000^73 ≤ 1032528362979^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414825611 10000000000 1032528362979 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601099699/10000000000 : ℝ)^89 ≤ (3881220401393/10000000000000 : ℝ)^73 := by
    have hnat : (4601099699 : ℕ)^89*10000000000000^73 ≤ 3881220401393^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601099699 10000000000 3881220401393 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649811567/1000000000 : ℝ)^89 ≤ (59122739249783/100000000000000 : ℝ)^73 := by
    have hnat : (649811567 : ℕ)^89*100000000000000^73 ≤ 59122739249783^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649811567 1000000000 59122739249783 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414825611/10000000000 : ℝ), (-4601099699/10000000000 : ℝ), (-649811567/1000000000 : ℝ)] ![(1032528362979/50000000000000 : ℝ), (3881220401393/10000000000000 : ℝ), (59122739249783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414825611/10000000000 : ℝ)|^89 ≤ (1032528362979/50000000000000 : ℝ)^73
        have hw : |(-414825611/10000000000 : ℝ)|=(414825611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4601099699/10000000000 : ℝ)|^89 ≤ (3881220401393/10000000000000 : ℝ)^73
        have hw : |(-4601099699/10000000000 : ℝ)|=(4601099699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649811567/1000000000 : ℝ)|^89 ≤ (59122739249783/100000000000000 : ℝ)^73
        have hw : |(-649811567/1000000000 : ℝ)|=(649811567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (330482851/625000000 : ℝ)*x 0 + (3956947023/10000000000 : ℝ)*x 1 + (-285829807/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330482851/625000000 : ℝ)^89 ≤ (2874058073063/6250000000000 : ℝ)^73 := by
    have hnat : (330482851 : ℕ)^89*6250000000000^73 ≤ 2874058073063^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330482851 625000000 2874058073063 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3956947023/10000000000 : ℝ)^89 ≤ (2018321942973/6250000000000 : ℝ)^73 := by
    have hnat : (3956947023 : ℕ)^89*6250000000000^73 ≤ 2018321942973^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3956947023 10000000000 2018321942973 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285829807/1000000000 : ℝ)^89 ≤ (21721919730841/100000000000000 : ℝ)^73 := by
    have hnat : (285829807 : ℕ)^89*100000000000000^73 ≤ 21721919730841^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285829807 1000000000 21721919730841 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330482851/625000000 : ℝ), (3956947023/10000000000 : ℝ), (-285829807/1000000000 : ℝ)] ![(2874058073063/6250000000000 : ℝ), (2018321942973/6250000000000 : ℝ), (21721919730841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330482851/625000000 : ℝ)|^89 ≤ (2874058073063/6250000000000 : ℝ)^73
        have hw : |(330482851/625000000 : ℝ)|=(330482851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3956947023/10000000000 : ℝ)|^89 ≤ (2018321942973/6250000000000 : ℝ)^73
        have hw : |(3956947023/10000000000 : ℝ)|=(3956947023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285829807/1000000000 : ℝ)|^89 ≤ (21721919730841/100000000000000 : ℝ)^73
        have hw : |(-285829807/1000000000 : ℝ)|=(285829807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4848261097/10000000000 : ℝ)*x 0 + (-16929001/40000000 : ℝ)*x 1 + (1528581587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4848261097/10000000000 : ℝ)^89 ≤ (20684419971953/50000000000000 : ℝ)^73 := by
    have hnat : (4848261097 : ℕ)^89*50000000000000^73 ≤ 20684419971953^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848261097 10000000000 20684419971953 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16929001/40000000 : ℝ)^89 ≤ (35052900625373/100000000000000 : ℝ)^73 := by
    have hnat : (16929001 : ℕ)^89*100000000000000^73 ≤ 35052900625373^73*40000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16929001 40000000 35052900625373 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528581587/5000000000 : ℝ)^89 ≤ (2357825941373/10000000000000 : ℝ)^73 := by
    have hnat : (1528581587 : ℕ)^89*10000000000000^73 ≤ 2357825941373^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528581587 5000000000 2357825941373 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4848261097/10000000000 : ℝ), (-16929001/40000000 : ℝ), (1528581587/5000000000 : ℝ)] ![(20684419971953/50000000000000 : ℝ), (35052900625373/100000000000000 : ℝ), (2357825941373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4848261097/10000000000 : ℝ)|^89 ≤ (20684419971953/50000000000000 : ℝ)^73
        have hw : |(4848261097/10000000000 : ℝ)|=(4848261097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16929001/40000000 : ℝ)|^89 ≤ (35052900625373/100000000000000 : ℝ)^73
        have hw : |(-16929001/40000000 : ℝ)|=(16929001/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1528581587/5000000000 : ℝ)|^89 ≤ (2357825941373/10000000000000 : ℝ)^73
        have hw : |(1528581587/5000000000 : ℝ)|=(1528581587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s0_25 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (827854243/1000000000 : ℝ)*x 0 + (-1279484407/10000000000 : ℝ)*x 1 + (-90350549/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827854243/1000000000 : ℝ)^89 ≤ (39713775085679/50000000000000 : ℝ)^73 := by
    have hnat : (827854243 : ℕ)^89*50000000000000^73 ≤ 39713775085679^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827854243 1000000000 39713775085679 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279484407/10000000000 : ℝ)^89 ≤ (4076492476791/50000000000000 : ℝ)^73 := by
    have hnat : (1279484407 : ℕ)^89*50000000000000^73 ≤ 4076492476791^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279484407 10000000000 4076492476791 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90350549/500000000 : ℝ)^89 ≤ (12419464853181/100000000000000 : ℝ)^73 := by
    have hnat : (90350549 : ℕ)^89*100000000000000^73 ≤ 12419464853181^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90350549 500000000 12419464853181 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827854243/1000000000 : ℝ), (-1279484407/10000000000 : ℝ), (-90350549/500000000 : ℝ)] ![(39713775085679/50000000000000 : ℝ), (4076492476791/50000000000000 : ℝ), (12419464853181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827854243/1000000000 : ℝ)|^89 ≤ (39713775085679/50000000000000 : ℝ)^73
        have hw : |(827854243/1000000000 : ℝ)|=(827854243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1279484407/10000000000 : ℝ)|^89 ≤ (4076492476791/50000000000000 : ℝ)^73
        have hw : |(-1279484407/10000000000 : ℝ)|=(1279484407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90350549/500000000 : ℝ)|^89 ≤ (12419464853181/100000000000000 : ℝ)^73
        have hw : |(-90350549/500000000 : ℝ)|=(90350549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000686377/10000000000 : ℝ)*x 0 + (-4349605399/10000000000 : ℝ)*x 1 + (-2817714519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000686377/10000000000 : ℝ)^89 ≤ (3515222183967/25000000000000 : ℝ)^73 := by
    have hnat : (2000686377 : ℕ)^89*25000000000000^73 ≤ 3515222183967^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000686377 10000000000 3515222183967 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4349605399/10000000000 : ℝ)^89 ≤ (3624148566041/10000000000000 : ℝ)^73 := by
    have hnat : (4349605399 : ℕ)^89*10000000000000^73 ≤ 3624148566041^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349605399 10000000000 3624148566041 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2817714519/5000000000 : ℝ)^89 ≤ (24848812790957/50000000000000 : ℝ)^73 := by
    have hnat : (2817714519 : ℕ)^89*50000000000000^73 ≤ 24848812790957^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817714519 5000000000 24848812790957 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000686377/10000000000 : ℝ), (-4349605399/10000000000 : ℝ), (-2817714519/5000000000 : ℝ)] ![(3515222183967/25000000000000 : ℝ), (3624148566041/10000000000000 : ℝ), (24848812790957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000686377/10000000000 : ℝ)|^89 ≤ (3515222183967/25000000000000 : ℝ)^73
        have hw : |(-2000686377/10000000000 : ℝ)|=(2000686377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4349605399/10000000000 : ℝ)|^89 ≤ (3624148566041/10000000000000 : ℝ)^73
        have hw : |(-4349605399/10000000000 : ℝ)|=(4349605399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2817714519/5000000000 : ℝ)|^89 ≤ (24848812790957/50000000000000 : ℝ)^73
        have hw : |(-2817714519/5000000000 : ℝ)|=(2817714519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (469668013/1000000000 : ℝ)*x 0 + (2056627681/5000000000 : ℝ)*x 1 + (-1674351269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469668013/1000000000 : ℝ)^89 ≤ (39797405529431/100000000000000 : ℝ)^73 := by
    have hnat : (469668013 : ℕ)^89*100000000000000^73 ≤ 39797405529431^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469668013 1000000000 39797405529431 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056627681/5000000000 : ℝ)^89 ≤ (1692753157171/5000000000000 : ℝ)^73 := by
    have hnat : (2056627681 : ℕ)^89*5000000000000^73 ≤ 1692753157171^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056627681 5000000000 1692753157171 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674351269/5000000000 : ℝ)^89 ≤ (13173765658371/50000000000000 : ℝ)^73 := by
    have hnat : (1674351269 : ℕ)^89*50000000000000^73 ≤ 13173765658371^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674351269 5000000000 13173765658371 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(469668013/1000000000 : ℝ), (2056627681/5000000000 : ℝ), (-1674351269/5000000000 : ℝ)] ![(39797405529431/100000000000000 : ℝ), (1692753157171/5000000000000 : ℝ), (13173765658371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(469668013/1000000000 : ℝ)|^89 ≤ (39797405529431/100000000000000 : ℝ)^73
        have hw : |(469668013/1000000000 : ℝ)|=(469668013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2056627681/5000000000 : ℝ)|^89 ≤ (1692753157171/5000000000000 : ℝ)^73
        have hw : |(2056627681/5000000000 : ℝ)|=(2056627681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674351269/5000000000 : ℝ)|^89 ≤ (13173765658371/50000000000000 : ℝ)^73
        have hw : |(-1674351269/5000000000 : ℝ)|=(1674351269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (93935179/200000000 : ℝ)*x 0 + (-411320973/1000000000 : ℝ)*x 1 + (3348665387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93935179/200000000 : ℝ)^89 ≤ (39798219798903/100000000000000 : ℝ)^73 := by
    have hnat : (93935179 : ℕ)^89*100000000000000^73 ≤ 39798219798903^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93935179 200000000 39798219798903 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411320973/1000000000 : ℝ)^89 ≤ (33854605239799/100000000000000 : ℝ)^73 := by
    have hnat : (411320973 : ℕ)^89*100000000000000^73 ≤ 33854605239799^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411320973 1000000000 33854605239799 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3348665387/10000000000 : ℝ)^89 ≤ (26347174947277/100000000000000 : ℝ)^73 := by
    have hnat : (3348665387 : ℕ)^89*100000000000000^73 ≤ 26347174947277^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3348665387 10000000000 26347174947277 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(93935179/200000000 : ℝ), (-411320973/1000000000 : ℝ), (3348665387/10000000000 : ℝ)] ![(39798219798903/100000000000000 : ℝ), (33854605239799/100000000000000 : ℝ), (26347174947277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(93935179/200000000 : ℝ)|^89 ≤ (39798219798903/100000000000000 : ℝ)^73
        have hw : |(93935179/200000000 : ℝ)|=(93935179/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411320973/1000000000 : ℝ)|^89 ≤ (33854605239799/100000000000000 : ℝ)^73
        have hw : |(-411320973/1000000000 : ℝ)|=(411320973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3348665387/10000000000 : ℝ)|^89 ≤ (26347174947277/100000000000000 : ℝ)^73
        have hw : |(3348665387/10000000000 : ℝ)|=(3348665387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326038_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1543156689/2500000000 : ℝ)*x 0 + (-2533644653/10000000000 : ℝ)*x 1 + (-3282636777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1543156689/2500000000 : ℝ)^89 ≤ (27766148466317/50000000000000 : ℝ)^73 := by
    have hnat : (1543156689 : ℕ)^89*50000000000000^73 ≤ 27766148466317^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543156689 2500000000 27766148466317 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533644653/10000000000 : ℝ)^89 ≤ (18752528382261/100000000000000 : ℝ)^73 := by
    have hnat : (2533644653 : ℕ)^89*100000000000000^73 ≤ 18752528382261^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533644653 10000000000 18752528382261 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3282636777/10000000000 : ℝ)^89 ≤ (25715174672623/100000000000000 : ℝ)^73 := by
    have hnat : (3282636777 : ℕ)^89*100000000000000^73 ≤ 25715174672623^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282636777 10000000000 25715174672623 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1543156689/2500000000 : ℝ), (-2533644653/10000000000 : ℝ), (-3282636777/10000000000 : ℝ)] ![(27766148466317/50000000000000 : ℝ), (18752528382261/100000000000000 : ℝ), (25715174672623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1543156689/2500000000 : ℝ)|^89 ≤ (27766148466317/50000000000000 : ℝ)^73
        have hw : |(1543156689/2500000000 : ℝ)|=(1543156689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2533644653/10000000000 : ℝ)|^89 ≤ (18752528382261/100000000000000 : ℝ)^73
        have hw : |(-2533644653/10000000000 : ℝ)|=(2533644653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3282636777/10000000000 : ℝ)|^89 ≤ (25715174672623/100000000000000 : ℝ)^73
        have hw : |(-3282636777/10000000000 : ℝ)|=(3282636777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326038 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-691793523/10000000000 : ℝ)*X 0 0+(-4468948123/10000000000 : ℝ)*X 0 1+(-322954953/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5007238111/10000000000 : ℝ)*X 2 0+(-2056674493/5000000000 : ℝ)*X 2 1+(1503927393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7772026113/10000000000 : ℝ)*X 0 0+(-193848297/1250000000 : ℝ)*X 0 1+(-560349021/2500000000 : ℝ)*X 0 2+(7772026113/10000000000 : ℝ)*X 1 0+(-193848297/1250000000 : ℝ)*X 1 1+(-560349021/2500000000 : ℝ)*X 1 2+(7772026113/10000000000 : ℝ)*X 2 0+(-193848297/1250000000 : ℝ)*X 2 1+(-560349021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-341553493/5000000000 : ℝ)*X 0 0+(-70342407/156250000 : ℝ)*X 0 1+(-6433970861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5008245119/10000000000 : ℝ)*X 1 0+(2092524857/5000000000 : ℝ)*X 1 1+(-732391361/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5008245037/10000000000 : ℝ)*X 2 0+(-807067867/2000000000 : ℝ)*X 2 1+(3089860381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1935885661/2500000000 : ℝ)*X 0 0+(-745993109/5000000000 : ℝ)*X 0 1+(-583099841/2500000000 : ℝ)*X 0 2+(1935885661/2500000000 : ℝ)*X 1 0+(-745993109/5000000000 : ℝ)*X 1 1+(-583099841/2500000000 : ℝ)*X 1 2+(1935885661/2500000000 : ℝ)*X 2 0+(-745993109/5000000000 : ℝ)*X 2 1+(-583099841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-410721129/10000000000 : ℝ)*X 0 0+(-2251653921/5000000000 : ℝ)*X 0 1+(-411916763/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((151628863/312500000 : ℝ)*X 1 0+(4177926089/10000000000 : ℝ)*X 1 1+(-3111041697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1322957723/2500000000 : ℝ)*X 2 0+(-488221277/1250000000 : ℝ)*X 2 1+(2908384147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2066618057/2500000000 : ℝ)*X 0 0+(-1259071743/10000000000 : ℝ)*X 0 1+(-73706923/400000000 : ℝ)*X 0 2+(2066618057/2500000000 : ℝ)*X 1 0+(-1259071743/10000000000 : ℝ)*X 1 1+(-73706923/400000000 : ℝ)*X 1 2+(2066618057/2500000000 : ℝ)*X 2 0+(-1259071743/10000000000 : ℝ)*X 2 1+(-73706923/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-414825611/10000000000 : ℝ)*X 0 0+(-4601099699/10000000000 : ℝ)*X 0 1+(-649811567/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((330482851/625000000 : ℝ)*X 1 0+(3956947023/10000000000 : ℝ)*X 1 1+(-285829807/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4848261097/10000000000 : ℝ)*X 2 0+(-16929001/40000000 : ℝ)*X 2 1+(1528581587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((827854243/1000000000 : ℝ)*X 0 0+(-1279484407/10000000000 : ℝ)*X 0 1+(-90350549/500000000 : ℝ)*X 0 2+(827854243/1000000000 : ℝ)*X 1 0+(-1279484407/10000000000 : ℝ)*X 1 1+(-90350549/500000000 : ℝ)*X 1 2+(827854243/1000000000 : ℝ)*X 2 0+(-1279484407/10000000000 : ℝ)*X 2 1+(-90350549/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((471/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(471/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29453341033238974729773/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (984841567009/500000000000 : ℝ)*(base39) + (109274075549/125000000000 : ℝ)*(base59) + (2773475517247/500000000000 : ℝ)*(major_s0_0) + (2773475517247/500000000000 : ℝ)*(major_s0_1) + (2773475517247/500000000000 : ℝ)*(major_s0_2) + (443467509/500000000000 : ℝ)*(sp_s0_0) + (4439831/15625000000 : ℝ)*(sp_s0_2) + (8403758205179/1000000000000 : ℝ)*(sp_s0_7) + (4202174795841/500000000000 : ℝ)*(sp_s0_8) + (8404079103261/1000000000000 : ℝ)*(sp_s0_9) + (2689235223859/1000000000000 : ℝ)*(sp_s0_13) + (17777809/1000000000000 : ℝ)*(sp_s0_14) + (78331581/250000000000 : ℝ)*(sp_s0_15) + (299665561/1000000000000 : ℝ)*(sp_s0_22) + (2689235223859/1000000000000 : ℝ)*(f.failure) + (4202331459003/500000000000 : ℝ)*(f.sum) + (20391454882979/50000000000000000000000000 : ℝ)*base63 + (3770934937024459/5000000000000000000000000000 : ℝ)*base64 + (2688978366475541/5000000000000000000000000000 : ℝ)*base66 + (77213085137979/100000000000000000000000000 : ℝ)*base69 + (1469100095125509/5000000000000000000000000000 : ℝ)*base70 + (2780227404024459/5000000000000000000000000000 : ℝ)*base72 + (77805787577979/100000000000000000000000000 : ℝ)*base75 + (42609661772021/100000000000000000000000000 : ℝ)*base76 + (1680222003/10000000000000000000000 : ℝ)*base78 + (24673/20000000000000000 : ℝ)*base86 + (24673/20000000000000000 : ℝ)*base88 + (24673/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1193/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1193/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1312374574897527504087/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256409813197/31250000000 : ℝ)*(base39) + (2931550775111/1000000000000 : ℝ)*(base40) + (1146624282171/500000000000 : ℝ)*(base59) + (600395626357/40000000000 : ℝ)*(major_s0_0) + (600395626357/40000000000 : ℝ)*(major_s0_1) + (600395626357/40000000000 : ℝ)*(major_s0_2) + (367538863/1000000000000 : ℝ)*(sp_s0_0) + (7999881/25000000000 : ℝ)*(sp_s0_9) + (32038067/250000000000 : ℝ)*(sp_s0_13) + (22742418083863/1000000000000 : ℝ)*(sp_s0_14) + (11371303775159/500000000000 : ℝ)*(sp_s0_15) + (11371232813743/500000000000 : ℝ)*(sp_s0_16) + (3638432677781/500000000000 : ℝ)*(sp_s0_19) + (22259051/125000000000 : ℝ)*(sp_s0_21) + (727699350783/100000000000 : ℝ)*(f.failure) + (11371392811363/500000000000 : ℝ)*(f.sum) + (914935046551/4000000000000000000000000 : ℝ)*base62 + (119896508596871/400000000000000000000000000 : ℝ)*base65 + (26680762243129/400000000000000000000000000 : ℝ)*base67 + (1804895380951/8000000000000000000000000 : ℝ)*base68 + (49680398069321/400000000000000000000000000 : ℝ)*base71 + (239457633516871/400000000000000000000000000 : ℝ)*base73 + (1814661921751/8000000000000000000000000 : ℝ)*base74 + (1052726332951/8000000000000000000000000 : ℝ)*base76 + (295139991/500000000000000000000 : ℝ)*base79 + (1099/2000000000000000 : ℝ)*base87 + (1099/2000000000000000 : ℝ)*base89 + (1099/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11829/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1346278416442608099537/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100691218087/12500000000 : ℝ)*(base39) + (482837842207/200000000000 : ℝ)*(base40) + (2295916705739/1000000000000 : ℝ)*(base59) + (15018518303051/1000000000000 : ℝ)*(major_s0_0) + (15018518303051/1000000000000 : ℝ)*(major_s0_1) + (15018518303051/1000000000000 : ℝ)*(major_s0_2) + (193118141/250000000000 : ℝ)*(sp_s0_2) + (90257011/500000000000 : ℝ)*(sp_s0_6) + (145448681/125000000000 : ℝ)*(sp_s0_7) + (960441457/1000000000000 : ℝ)*(sp_s0_8) + (4550938445049/200000000000 : ℝ)*(sp_s0_20) + (5688723843309/250000000000 : ℝ)*(sp_s0_21) + (22755083342129/1000000000000 : ℝ)*(sp_s0_22) + (3640497894893/500000000000 : ℝ)*(sp_s0_25) + (7281176303809/1000000000000 : ℝ)*(f.failure) + (22755855814693/1000000000000 : ℝ)*(f.sum) + (60307227125607/100000000000000000000000000 : ℝ)*base63 + (5522395066954553/10000000000000000000000000000 : ℝ)*base65 + (2169406872045447/10000000000000000000000000000 : ℝ)*base67 + (55839893055607/200000000000000000000000000 : ℝ)*base69 + (2745041459734903/10000000000000000000000000000 : ℝ)*base71 + (3882096310045447/10000000000000000000000000000 : ℝ)*base72 + (56819285895607/200000000000000000000000000 : ℝ)*base75 + (65064328115607/200000000000000000000000000 : ℝ)*base77 + (3605454311/5000000000000000000000 : ℝ)*base78 + (12677/20000000000000000 : ℝ)*base87 + (12677/20000000000000000 : ℝ)*base89 + (12677/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (471/50000 : ℝ) ^ (87/16 : ℝ) ≤ (481805539/50000000000000000000 : ℝ) := by
    have hpowers : (471/50000 : ℝ)^87 ≤ (481805539/50000000000000000000 : ℝ)^16 := by
      have hnat : (471 : ℕ)^87*50000000000000000000^16 ≤ 481805539^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471 50000 481805539 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (471/50000 : ℝ)) (X := (481805539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000000000481805539/50000000000000000000 : ℝ) ≤ (5000000000008861/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50000000000481805539/50000000000000000000 : ℝ)^16 ≤ (5000000000008861/5000000000000000 : ℝ)^87 := by
      have hnat : (50000000000481805539 : ℕ)^16*5000000000000000^87 ≤ 5000000000008861^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000481805539 50000000000000000000 5000000000008861 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000008861/5000000000000000 : ℝ)) (X := (50000000000481805539/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000000000481805539/25000000000000000000 : ℝ) ≤ (2500000000008861/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25000000000481805539/25000000000000000000 : ℝ)^16 ≤ (2500000000008861/2500000000000000 : ℝ)^87 := by
      have hnat : (25000000000481805539 : ℕ)^16*2500000000000000^87 ≤ 2500000000008861^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000481805539 25000000000000000000 2500000000008861 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000008861/2500000000000000 : ℝ)) (X := (25000000000481805539/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8861/47100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8861/47100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (471/50000 : ℝ)) (alpha := (8861/47100000000000 : ℝ)) (beta := (8861/47100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (471/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8861/47100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8861/47100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1193/5000 : ℝ) ^ (87/16 : ℝ) ≤ (20656323106521799/50000000000000000000 : ℝ) := by
    have hpowers : (1193/5000 : ℝ)^87 ≤ (20656323106521799/50000000000000000000 : ℝ)^16 := by
      have hnat : (1193 : ℕ)^87*50000000000000000000^16 ≤ 20656323106521799^16*5000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1193 5000 20656323106521799 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1193/5000 : ℝ)) (X := (20656323106521799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50020656323106521799/50000000000000000000 : ℝ) ≤ (10000759644757551/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50020656323106521799/50000000000000000000 : ℝ)^16 ≤ (10000759644757551/10000000000000000 : ℝ)^87 := by
      have hnat : (50020656323106521799 : ℕ)^16*10000000000000000^87 ≤ 10000759644757551^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020656323106521799 50000000000000000000 10000759644757551 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000759644757551/10000000000000000 : ℝ)) (X := (50020656323106521799/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25020656323106521799/25000000000000000000 : ℝ) ≤ (500075951677519/500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25020656323106521799/25000000000000000000 : ℝ)^16 ≤ (500075951677519/500000000000000 : ℝ)^87 := by
      have hnat : (25020656323106521799 : ℕ)^16*500000000000000^87 ≤ 500075951677519^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020656323106521799 25000000000000000000 500075951677519 500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500075951677519/500000000000000 : ℝ)) (X := (25020656323106521799/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(759644757551/2386000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(759388792829/2386000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1193/5000 : ℝ)) (alpha := (759644757551/2386000000000000 : ℝ)) (beta := (759388792829/2386000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1193/5000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(759644757551/2386000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(759388792829/2386000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11829/50000 : ℝ) ^ (87/16 : ℝ) ≤ (39446231966847267/100000000000000000000 : ℝ) := by
    have hpowers : (11829/50000 : ℝ)^87 ≤ (39446231966847267/100000000000000000000 : ℝ)^16 := by
      have hnat : (11829 : ℕ)^87*100000000000000000000^16 ≤ 39446231966847267^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11829 50000 39446231966847267 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11829/50000 : ℝ)) (X := (39446231966847267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100039446231966847267/100000000000000000000 : ℝ) ≤ (1000072533120489/1000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100039446231966847267/100000000000000000000 : ℝ)^16 ≤ (1000072533120489/1000000000000000 : ℝ)^87 := by
      have hnat : (100039446231966847267 : ℕ)^16*1000000000000000^87 ≤ 1000072533120489^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039446231966847267 100000000000000000000 1000072533120489 1000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000072533120489/1000000000000000 : ℝ)) (X := (100039446231966847267/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50039446231966847267/50000000000000000000 : ℝ) ≤ (2500362607260641/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50039446231966847267/50000000000000000000 : ℝ)^16 ≤ (2500362607260641/2500000000000000 : ℝ)^87 := by
      have hnat : (50039446231966847267 : ℕ)^16*2500000000000000^87 ≤ 2500362607260641^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039446231966847267 50000000000000000000 2500362607260641 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500362607260641/2500000000000000 : ℝ)) (X := (50039446231966847267/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(72533120489/236580000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(362548918837/1182900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (11829/50000 : ℝ)) (alpha := (72533120489/236580000000000 : ℝ)) (beta := (362548918837/1182900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11829/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(72533120489/236580000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(362548918837/1182900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2000686377/10000000000 : ℝ)*X 0 0+(-4349605399/10000000000 : ℝ)*X 0 1+(-2817714519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((469668013/1000000000 : ℝ)*X 1 0+(2056627681/5000000000 : ℝ)*X 1 1+(-1674351269/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((93935179/200000000 : ℝ)*X 2 0+(-411320973/1000000000 : ℝ)*X 2 1+(3348665387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1543156689/2500000000 : ℝ)*X 0 0+(-2533644653/10000000000 : ℝ)*X 0 1+(-3282636777/10000000000 : ℝ)*X 0 2+(1543156689/2500000000 : ℝ)*X 1 0+(-2533644653/10000000000 : ℝ)*X 1 1+(-3282636777/10000000000 : ℝ)*X 1 2+(1543156689/2500000000 : ℝ)*X 2 0+(-2533644653/10000000000 : ℝ)*X 2 1+(-3282636777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-341068268829466326538388625240877/36926392150000000000000000000000 : ℝ) := by norm_num
    linear_combination (86389/500000000000 : ℝ)*(base15) + (49341/1000000000000 : ℝ)*(base27) + (39413/500000000000 : ℝ)*(base33) + (623144741489/500000000000 : ℝ)*(base39) + (135726412219/250000000000 : ℝ)*(base40) + (52603/500000000000 : ℝ)*(base50) + (469491646983/1000000000000 : ℝ)*(base59) + (239197/1000000000000 : ℝ)*(ratio_s0_1) + (1031324960587/500000000000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (3078812097969/1000000000000 : ℝ)*(sp_s1_0) + (615762369273/200000000000 : ℝ)*(sp_s1_1) + (3078812019143/1000000000000 : ℝ)*(sp_s1_2) + (999999950659/1000000000000 : ℝ)*(sp_s1_6) + (3078812097969/1000000000000 : ℝ)*(f.sum) + (10918133194549891/47039990000000000000000000000 : ℝ)*base63 + (7684508853697/19715000000000000000000000 : ℝ)*base65 + (916322423789/2386000000000000000000000 : ℝ)*base67 + (1060285207861/19715000000000000000000000 : ℝ)*base68 + (18042246138152514253/46428825000000000000000000000 : ℝ)*base71 + (4567354562267011/11775000000000000000000000 : ℝ)*base73 + (892882515211/5965000000000000000000000 : ℝ)*base74 + (4573207534792471/11775000000000000000000000 : ℝ)*base77 + (10902009704025118081/28095150000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b017 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c326038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:14.027019+00:00
-- url     : https://prove2.me/submissions/94abd632-00dd-4511-841f-519bd6840adf

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
theorem collision_support_c314038_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-784047259/10000000000 : ℝ)*x 0 + (-36148611/80000000 : ℝ)*x 1 + (-3317024927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784047259/10000000000 : ℝ)^19 ≤ (1988246268799/50000000000000 : ℝ)^15 := by
    have hnat : (784047259 : ℕ)^19*50000000000000^15 ≤ 1988246268799^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784047259 10000000000 1988246268799 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36148611/80000000 : ℝ)^19 ≤ (36559652682137/100000000000000 : ℝ)^15 := by
    have hnat : (36148611 : ℕ)^19*100000000000000^15 ≤ 36559652682137^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36148611 80000000 36559652682137 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3317024927/5000000000 : ℝ)^19 ≤ (59463854767543/100000000000000 : ℝ)^15 := by
    have hnat : (3317024927 : ℕ)^19*100000000000000^15 ≤ 59463854767543^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3317024927 5000000000 59463854767543 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784047259/10000000000 : ℝ), (-36148611/80000000 : ℝ), (-3317024927/5000000000 : ℝ)] ![(1988246268799/50000000000000 : ℝ), (36559652682137/100000000000000 : ℝ), (59463854767543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784047259/10000000000 : ℝ)|^19 ≤ (1988246268799/50000000000000 : ℝ)^15
        have hw : |(-784047259/10000000000 : ℝ)|=(784047259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36148611/80000000 : ℝ)|^19 ≤ (36559652682137/100000000000000 : ℝ)^15
        have hw : |(-36148611/80000000 : ℝ)|=(36148611/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3317024927/5000000000 : ℝ)|^19 ≤ (59463854767543/100000000000000 : ℝ)^15
        have hw : |(-3317024927/5000000000 : ℝ)|=(3317024927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5068777171/10000000000 : ℝ)*x 0 + (271930927/625000000 : ℝ)*x 1 + (-779813653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5068777171/10000000000 : ℝ)^19 ≤ (10571843565761/25000000000000 : ℝ)^15 := by
    have hnat : (5068777171 : ℕ)^19*25000000000000^15 ≤ 10571843565761^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068777171 10000000000 10571843565761 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271930927/625000000 : ℝ)^19 ≤ (1742486998839/5000000000000 : ℝ)^15 := by
    have hnat : (271930927 : ℕ)^19*5000000000000^15 ≤ 1742486998839^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271930927 625000000 1742486998839 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779813653/2500000000 : ℝ)^19 ≤ (22862885751061/100000000000000 : ℝ)^15 := by
    have hnat : (779813653 : ℕ)^19*100000000000000^15 ≤ 22862885751061^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779813653 2500000000 22862885751061 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5068777171/10000000000 : ℝ), (271930927/625000000 : ℝ), (-779813653/2500000000 : ℝ)] ![(10571843565761/25000000000000 : ℝ), (1742486998839/5000000000000 : ℝ), (22862885751061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5068777171/10000000000 : ℝ)|^19 ≤ (10571843565761/25000000000000 : ℝ)^15
        have hw : |(5068777171/10000000000 : ℝ)|=(5068777171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271930927/625000000 : ℝ)|^19 ≤ (1742486998839/5000000000000 : ℝ)^15
        have hw : |(271930927/625000000 : ℝ)|=(271930927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-779813653/2500000000 : ℝ)|^19 ≤ (22862885751061/100000000000000 : ℝ)^15
        have hw : |(-779813653/2500000000 : ℝ)|=(779813653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_3 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^19 ≤ (1 : ℝ)^15 := by
    have hnat : (1 : ℕ)^19*1^15 ≤ 1^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^19 ≤ (1 : ℝ)^15
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-640081537/10000000000 : ℝ)*x 0 + (-1000349507/2000000000 : ℝ)*x 1 + (-6268490891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640081537/10000000000 : ℝ)^19 ≤ (3075374768909/100000000000000 : ℝ)^15 := by
    have hnat : (640081537 : ℕ)^19*100000000000000^15 ≤ 3075374768909^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640081537 10000000000 3075374768909 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000349507/2000000000 : ℝ)^19 ≤ (20790147741931/50000000000000 : ℝ)^15 := by
    have hnat : (1000349507 : ℕ)^19*50000000000000^15 ≤ 20790147741931^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000349507 2000000000 20790147741931 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6268490891/10000000000 : ℝ)^19 ≤ (110688659483/200000000000 : ℝ)^15 := by
    have hnat : (6268490891 : ℕ)^19*200000000000^15 ≤ 110688659483^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6268490891 10000000000 110688659483 200000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-640081537/10000000000 : ℝ), (-1000349507/2000000000 : ℝ), (-6268490891/10000000000 : ℝ)] ![(3075374768909/100000000000000 : ℝ), (20790147741931/50000000000000 : ℝ), (110688659483/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-640081537/10000000000 : ℝ)|^19 ≤ (3075374768909/100000000000000 : ℝ)^15
        have hw : |(-640081537/10000000000 : ℝ)|=(640081537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1000349507/2000000000 : ℝ)|^19 ≤ (20790147741931/50000000000000 : ℝ)^15
        have hw : |(-1000349507/2000000000 : ℝ)|=(1000349507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6268490891/10000000000 : ℝ)|^19 ≤ (110688659483/200000000000 : ℝ)^15
        have hw : |(-6268490891/10000000000 : ℝ)|=(6268490891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5020077723/10000000000 : ℝ)*x 0 + (51569991/100000000 : ℝ)*x 1 + (-2236943843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5020077723/10000000000 : ℝ)^19 ≤ (10443351623459/25000000000000 : ℝ)^15 := by
    have hnat : (5020077723 : ℕ)^19*25000000000000^15 ≤ 10443351623459^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020077723 10000000000 10443351623459 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51569991/100000000 : ℝ)^19 ≤ (43221808729093/100000000000000 : ℝ)^15 := by
    have hnat : (51569991 : ℕ)^19*100000000000000^15 ≤ 43221808729093^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51569991 100000000 43221808729093 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236943843/10000000000 : ℝ)^19 ≤ (15004784760539/100000000000000 : ℝ)^15 := by
    have hnat : (2236943843 : ℕ)^19*100000000000000^15 ≤ 15004784760539^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236943843 10000000000 15004784760539 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5020077723/10000000000 : ℝ), (51569991/100000000 : ℝ), (-2236943843/10000000000 : ℝ)] ![(10443351623459/25000000000000 : ℝ), (43221808729093/100000000000000 : ℝ), (15004784760539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5020077723/10000000000 : ℝ)|^19 ≤ (10443351623459/25000000000000 : ℝ)^15
        have hw : |(5020077723/10000000000 : ℝ)|=(5020077723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51569991/100000000 : ℝ)|^19 ≤ (43221808729093/100000000000000 : ℝ)^15
        have hw : |(51569991/100000000 : ℝ)|=(51569991/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236943843/10000000000 : ℝ)|^19 ≤ (15004784760539/100000000000000 : ℝ)^15
        have hw : |(-2236943843/10000000000 : ℝ)|=(2236943843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5020078571/10000000000 : ℝ)*x 0 + (-3483165261/10000000000 : ℝ)*x 1 + (4060884913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5020078571/10000000000 : ℝ)^19 ≤ (20886707715993/50000000000000 : ℝ)^15 := by
    have hnat : (5020078571 : ℕ)^19*50000000000000^15 ≤ 20886707715993^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020078571 10000000000 20886707715993 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3483165261/10000000000 : ℝ)^19 ≤ (26292618205327/100000000000000 : ℝ)^15 := by
    have hnat : (3483165261 : ℕ)^19*100000000000000^15 ≤ 26292618205327^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3483165261 10000000000 26292618205327 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060884913/10000000000 : ℝ)^19 ≤ (31933966352359/100000000000000 : ℝ)^15 := by
    have hnat : (4060884913 : ℕ)^19*100000000000000^15 ≤ 31933966352359^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060884913 10000000000 31933966352359 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5020078571/10000000000 : ℝ), (-3483165261/10000000000 : ℝ), (4060884913/10000000000 : ℝ)] ![(20886707715993/50000000000000 : ℝ), (26292618205327/100000000000000 : ℝ), (31933966352359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5020078571/10000000000 : ℝ)|^19 ≤ (20886707715993/50000000000000 : ℝ)^15
        have hw : |(5020078571/10000000000 : ℝ)|=(5020078571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3483165261/10000000000 : ℝ)|^19 ≤ (26292618205327/100000000000000 : ℝ)^15
        have hw : |(-3483165261/10000000000 : ℝ)|=(3483165261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060884913/10000000000 : ℝ)|^19 ≤ (31933966352359/100000000000000 : ℝ)^15
        have hw : |(4060884913/10000000000 : ℝ)|=(4060884913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (890849951/1250000000 : ℝ)*x 0 + (-69294441/625000000 : ℝ)*x 1 + (-3734635199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890849951/1250000000 : ℝ)^19 ≤ (65112808297659/100000000000000 : ℝ)^15 := by
    have hnat : (890849951 : ℕ)^19*100000000000000^15 ≤ 65112808297659^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890849951 1250000000 65112808297659 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69294441/625000000 : ℝ)^19 ≤ (1541854128041/25000000000000 : ℝ)^15 := by
    have hnat : (69294441 : ℕ)^19*25000000000000^15 ≤ 1541854128041^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69294441 625000000 1541854128041 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734635199/10000000000 : ℝ)^19 ≤ (7179943792621/25000000000000 : ℝ)^15 := by
    have hnat : (3734635199 : ℕ)^19*25000000000000^15 ≤ 7179943792621^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734635199 10000000000 7179943792621 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(890849951/1250000000 : ℝ), (-69294441/625000000 : ℝ), (-3734635199/10000000000 : ℝ)] ![(65112808297659/100000000000000 : ℝ), (1541854128041/25000000000000 : ℝ), (7179943792621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(890849951/1250000000 : ℝ)|^19 ≤ (65112808297659/100000000000000 : ℝ)^15
        have hw : |(890849951/1250000000 : ℝ)|=(890849951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69294441/625000000 : ℝ)|^19 ≤ (1541854128041/25000000000000 : ℝ)^15
        have hw : |(-69294441/625000000 : ℝ)|=(69294441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3734635199/10000000000 : ℝ)|^19 ≤ (7179943792621/25000000000000 : ℝ)^15
        have hw : |(-3734635199/10000000000 : ℝ)|=(3734635199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-16618739/5000000000 : ℝ)*x 0 + (-1068938499/2500000000 : ℝ)*x 1 + (-7189415579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16618739/5000000000 : ℝ)^19 ≤ (14513056143/20000000000000 : ℝ)^15 := by
    have hnat : (16618739 : ℕ)^19*20000000000000^15 ≤ 14513056143^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16618739 5000000000 14513056143 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068938499/2500000000 : ℝ)^19 ≤ (8522286073117/25000000000000 : ℝ)^15 := by
    have hnat : (1068938499 : ℕ)^19*25000000000000^15 ≤ 8522286073117^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068938499 2500000000 8522286073117 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7189415579/10000000000 : ℝ)^19 ≤ (65838290423049/100000000000000 : ℝ)^15 := by
    have hnat : (7189415579 : ℕ)^19*100000000000000^15 ≤ 65838290423049^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7189415579 10000000000 65838290423049 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16618739/5000000000 : ℝ), (-1068938499/2500000000 : ℝ), (-7189415579/10000000000 : ℝ)] ![(14513056143/20000000000000 : ℝ), (8522286073117/25000000000000 : ℝ), (65838290423049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16618739/5000000000 : ℝ)|^19 ≤ (14513056143/20000000000000 : ℝ)^15
        have hw : |(-16618739/5000000000 : ℝ)|=(16618739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068938499/2500000000 : ℝ)|^19 ≤ (8522286073117/25000000000000 : ℝ)^15
        have hw : |(-1068938499/2500000000 : ℝ)|=(1068938499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7189415579/10000000000 : ℝ)|^19 ≤ (65838290423049/100000000000000 : ℝ)^15
        have hw : |(-7189415579/10000000000 : ℝ)|=(7189415579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (181477647/400000000 : ℝ)*x 0 + (4574627987/10000000000 : ℝ)*x 1 + (-433097913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181477647/400000000 : ℝ)^19 ≤ (7349593459569/20000000000000 : ℝ)^15 := by
    have hnat : (181477647 : ℕ)^19*20000000000000^15 ≤ 7349593459569^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181477647 400000000 7349593459569 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574627987/10000000000 : ℝ)^19 ≤ (7427009628913/20000000000000 : ℝ)^15 := by
    have hnat : (4574627987 : ℕ)^19*20000000000000^15 ≤ 7427009628913^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574627987 10000000000 7427009628913 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433097913/1250000000 : ℝ)^19 ≤ (26116984546617/100000000000000 : ℝ)^15 := by
    have hnat : (433097913 : ℕ)^19*100000000000000^15 ≤ 26116984546617^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433097913 1250000000 26116984546617 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181477647/400000000 : ℝ), (4574627987/10000000000 : ℝ), (-433097913/1250000000 : ℝ)] ![(7349593459569/20000000000000 : ℝ), (7427009628913/20000000000000 : ℝ), (26116984546617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181477647/400000000 : ℝ)|^19 ≤ (7349593459569/20000000000000 : ℝ)^15
        have hw : |(181477647/400000000 : ℝ)|=(181477647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574627987/10000000000 : ℝ)|^19 ≤ (7427009628913/20000000000000 : ℝ)^15
        have hw : |(4574627987/10000000000 : ℝ)|=(4574627987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433097913/1250000000 : ℝ)|^19 ≤ (26116984546617/100000000000000 : ℝ)^15
        have hw : |(-433097913/1250000000 : ℝ)|=(433097913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2937620657/5000000000 : ℝ)*x 0 + (-935132703/2500000000 : ℝ)*x 1 + (566609077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2937620657/5000000000 : ℝ)^19 ≤ (5098384261959/10000000000000 : ℝ)^15 := by
    have hnat : (2937620657 : ℕ)^19*10000000000000^15 ≤ 5098384261959^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2937620657 5000000000 5098384261959 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935132703/2500000000 : ℝ)^19 ≤ (179857595721/625000000000 : ℝ)^15 := by
    have hnat : (935132703 : ℕ)^19*625000000000^15 ≤ 179857595721^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935132703 2500000000 179857595721 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566609077/2000000000 : ℝ)^19 ≤ (10119471029691/50000000000000 : ℝ)^15 := by
    have hnat : (566609077 : ℕ)^19*50000000000000^15 ≤ 10119471029691^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566609077 2000000000 10119471029691 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2937620657/5000000000 : ℝ), (-935132703/2500000000 : ℝ), (566609077/2000000000 : ℝ)] ![(5098384261959/10000000000000 : ℝ), (179857595721/625000000000 : ℝ), (10119471029691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2937620657/5000000000 : ℝ)|^19 ≤ (5098384261959/10000000000000 : ℝ)^15
        have hw : |(2937620657/5000000000 : ℝ)|=(2937620657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935132703/2500000000 : ℝ)|^19 ≤ (179857595721/625000000000 : ℝ)^15
        have hw : |(-935132703/2500000000 : ℝ)|=(935132703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566609077/2000000000 : ℝ)|^19 ≤ (10119471029691/50000000000000 : ℝ)^15
        have hw : |(566609077/2000000000 : ℝ)|=(566609077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2228141197/2500000000 : ℝ)*x 0 + (-441975499/5000000000 : ℝ)*x 1 + (-743154433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228141197/2500000000 : ℝ)^19 ≤ (86431109206567/100000000000000 : ℝ)^15 := by
    have hnat : (2228141197 : ℕ)^19*100000000000000^15 ≤ 86431109206567^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228141197 2500000000 86431109206567 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441975499/5000000000 : ℝ)^19 ≤ (4628877716413/100000000000000 : ℝ)^15 := by
    have hnat : (441975499 : ℕ)^19*100000000000000^15 ≤ 4628877716413^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441975499 5000000000 4628877716413 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743154433/5000000000 : ℝ)^19 ≤ (1117501632737/12500000000000 : ℝ)^15 := by
    have hnat : (743154433 : ℕ)^19*12500000000000^15 ≤ 1117501632737^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743154433 5000000000 1117501632737 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228141197/2500000000 : ℝ), (-441975499/5000000000 : ℝ), (-743154433/5000000000 : ℝ)] ![(86431109206567/100000000000000 : ℝ), (4628877716413/100000000000000 : ℝ), (1117501632737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228141197/2500000000 : ℝ)|^19 ≤ (86431109206567/100000000000000 : ℝ)^15
        have hw : |(2228141197/2500000000 : ℝ)|=(2228141197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441975499/5000000000 : ℝ)|^19 ≤ (4628877716413/100000000000000 : ℝ)^15
        have hw : |(-441975499/5000000000 : ℝ)|=(441975499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743154433/5000000000 : ℝ)|^19 ≤ (1117501632737/12500000000000 : ℝ)^15
        have hw : |(-743154433/5000000000 : ℝ)|=(743154433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-19172573/5000000000 : ℝ)*x 0 + (-60505761/125000000 : ℝ)*x 1 + (-3341656357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19172573/5000000000 : ℝ)^19 ≤ (86969405471/100000000000000 : ℝ)^15 := by
    have hnat : (19172573 : ℕ)^19*100000000000000^15 ≤ 86969405471^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19172573 5000000000 86969405471 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60505761/125000000 : ℝ)^19 ≤ (39889308264337/100000000000000 : ℝ)^15 := by
    have hnat : (60505761 : ℕ)^19*100000000000000^15 ≤ 39889308264337^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60505761 125000000 39889308264337 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3341656357/5000000000 : ℝ)^19 ≤ (6002372231859/10000000000000 : ℝ)^15 := by
    have hnat : (3341656357 : ℕ)^19*10000000000000^15 ≤ 6002372231859^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3341656357 5000000000 6002372231859 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19172573/5000000000 : ℝ), (-60505761/125000000 : ℝ), (-3341656357/5000000000 : ℝ)] ![(86969405471/100000000000000 : ℝ), (39889308264337/100000000000000 : ℝ), (6002372231859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19172573/5000000000 : ℝ)|^19 ≤ (86969405471/100000000000000 : ℝ)^15
        have hw : |(-19172573/5000000000 : ℝ)|=(19172573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-60505761/125000000 : ℝ)|^19 ≤ (39889308264337/100000000000000 : ℝ)^15
        have hw : |(-60505761/125000000 : ℝ)|=(60505761/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3341656357/5000000000 : ℝ)|^19 ≤ (6002372231859/10000000000000 : ℝ)^15
        have hw : |(-3341656357/5000000000 : ℝ)|=(3341656357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2935067023/5000000000 : ℝ)*x 0 + (3982103779/10000000000 : ℝ)*x 1 + (-2573648701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2935067023/5000000000 : ℝ)^19 ≤ (50927711010129/100000000000000 : ℝ)^15 := by
    have hnat : (2935067023 : ℕ)^19*100000000000000^15 ≤ 50927711010129^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935067023 5000000000 50927711010129 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3982103779/10000000000 : ℝ)^19 ≤ (3893910276209/12500000000000 : ℝ)^15 := by
    have hnat : (3982103779 : ℕ)^19*12500000000000^15 ≤ 3893910276209^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982103779 10000000000 3893910276209 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573648701/10000000000 : ℝ)^19 ≤ (3584201352603/20000000000000 : ℝ)^15 := by
    have hnat : (2573648701 : ℕ)^19*20000000000000^15 ≤ 3584201352603^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573648701 10000000000 3584201352603 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2935067023/5000000000 : ℝ), (3982103779/10000000000 : ℝ), (-2573648701/10000000000 : ℝ)] ![(50927711010129/100000000000000 : ℝ), (3893910276209/12500000000000 : ℝ), (3584201352603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2935067023/5000000000 : ℝ)|^19 ≤ (50927711010129/100000000000000 : ℝ)^15
        have hw : |(2935067023/5000000000 : ℝ)|=(2935067023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3982103779/10000000000 : ℝ)|^19 ≤ (3893910276209/12500000000000 : ℝ)^15
        have hw : |(3982103779/10000000000 : ℝ)|=(3982103779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2573648701/10000000000 : ℝ)|^19 ≤ (3584201352603/20000000000000 : ℝ)^15
        have hw : |(-2573648701/10000000000 : ℝ)|=(2573648701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (903005481/2000000000 : ℝ)*x 0 + (-4879310613/10000000000 : ℝ)*x 1 + (630703373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903005481/2000000000 : ℝ)^19 ≤ (18261642332937/50000000000000 : ℝ)^15 := by
    have hnat : (903005481 : ℕ)^19*50000000000000^15 ≤ 18261642332937^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903005481 2000000000 18261642332937 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4879310613/10000000000 : ℝ)^19 ≤ (20147634378079/50000000000000 : ℝ)^15 := by
    have hnat : (4879310613 : ℕ)^19*50000000000000^15 ≤ 20147634378079^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4879310613 10000000000 20147634378079 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630703373/2000000000 : ℝ)^19 ≤ (11590723286313/50000000000000 : ℝ)^15 := by
    have hnat : (630703373 : ℕ)^19*50000000000000^15 ≤ 11590723286313^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630703373 2000000000 11590723286313 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903005481/2000000000 : ℝ), (-4879310613/10000000000 : ℝ), (630703373/2000000000 : ℝ)] ![(18261642332937/50000000000000 : ℝ), (20147634378079/50000000000000 : ℝ), (11590723286313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903005481/2000000000 : ℝ)|^19 ≤ (18261642332937/50000000000000 : ℝ)^15
        have hw : |(903005481/2000000000 : ℝ)|=(903005481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4879310613/10000000000 : ℝ)|^19 ≤ (20147634378079/50000000000000 : ℝ)^15
        have hw : |(-4879310613/10000000000 : ℝ)|=(4879310613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630703373/2000000000 : ℝ)|^19 ≤ (11590723286313/50000000000000 : ℝ)^15
        have hw : |(630703373/2000000000 : ℝ)|=(630703373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s0_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1793212339/2000000000 : ℝ)*x 0 + (-240578733/2500000000 : ℝ)*x 1 + (-1328685797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793212339/2000000000 : ℝ)^19 ≤ (43544387557669/50000000000000 : ℝ)^15 := by
    have hnat : (1793212339 : ℕ)^19*50000000000000^15 ≤ 43544387557669^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793212339 2000000000 43544387557669 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240578733/2500000000 : ℝ)^19 ≤ (5154681285021/100000000000000 : ℝ)^15 := by
    have hnat : (240578733 : ℕ)^19*100000000000000^15 ≤ 5154681285021^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240578733 2500000000 5154681285021 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328685797/10000000000 : ℝ)^19 ≤ (1939135896903/25000000000000 : ℝ)^15 := by
    have hnat : (1328685797 : ℕ)^19*25000000000000^15 ≤ 1939135896903^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328685797 10000000000 1939135896903 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1793212339/2000000000 : ℝ), (-240578733/2500000000 : ℝ), (-1328685797/10000000000 : ℝ)] ![(43544387557669/50000000000000 : ℝ), (5154681285021/100000000000000 : ℝ), (1939135896903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1793212339/2000000000 : ℝ)|^19 ≤ (43544387557669/50000000000000 : ℝ)^15
        have hw : |(1793212339/2000000000 : ℝ)|=(1793212339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240578733/2500000000 : ℝ)|^19 ≤ (5154681285021/100000000000000 : ℝ)^15
        have hw : |(-240578733/2500000000 : ℝ)|=(240578733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328685797/10000000000 : ℝ)|^19 ≤ (1939135896903/25000000000000 : ℝ)^15
        have hw : |(-1328685797/10000000000 : ℝ)|=(1328685797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1153147879/5000000000 : ℝ)*x 0 + (-4432682423/10000000000 : ℝ)*x 1 + (-1133696539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153147879/5000000000 : ℝ)^19 ≤ (779822337753/5000000000000 : ℝ)^15 := by
    have hnat : (1153147879 : ℕ)^19*5000000000000^15 ≤ 779822337753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153147879 5000000000 779822337753 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4432682423/10000000000 : ℝ)^19 ≤ (35681605092261/100000000000000 : ℝ)^15 := by
    have hnat : (4432682423 : ℕ)^19*100000000000000^15 ≤ 35681605092261^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432682423 10000000000 35681605092261 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133696539/2000000000 : ℝ)^19 ≤ (12180487035137/25000000000000 : ℝ)^15 := by
    have hnat : (1133696539 : ℕ)^19*25000000000000^15 ≤ 12180487035137^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133696539 2000000000 12180487035137 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1153147879/5000000000 : ℝ), (-4432682423/10000000000 : ℝ), (-1133696539/2000000000 : ℝ)] ![(779822337753/5000000000000 : ℝ), (35681605092261/100000000000000 : ℝ), (12180487035137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1153147879/5000000000 : ℝ)|^19 ≤ (779822337753/5000000000000 : ℝ)^15
        have hw : |(-1153147879/5000000000 : ℝ)|=(1153147879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4432682423/10000000000 : ℝ)|^19 ≤ (35681605092261/100000000000000 : ℝ)^15
        have hw : |(-4432682423/10000000000 : ℝ)|=(4432682423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133696539/2000000000 : ℝ)|^19 ≤ (12180487035137/25000000000000 : ℝ)^15
        have hw : |(-1133696539/2000000000 : ℝ)|=(1133696539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (948509043/2000000000 : ℝ)*x 0 + (269339093/625000000 : ℝ)*x 1 + (-1762875547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948509043/2000000000 : ℝ)^19 ≤ (38870000074741/100000000000000 : ℝ)^15 := by
    have hnat : (948509043 : ℕ)^19*100000000000000^15 ≤ 38870000074741^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948509043 2000000000 38870000074741 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269339093/625000000 : ℝ)^19 ≤ (34429539147331/100000000000000 : ℝ)^15 := by
    have hnat : (269339093 : ℕ)^19*100000000000000^15 ≤ 34429539147331^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269339093 625000000 34429539147331 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762875547/5000000000 : ℝ)^19 ≤ (26700460756153/100000000000000 : ℝ)^15 := by
    have hnat : (1762875547 : ℕ)^19*100000000000000^15 ≤ 26700460756153^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762875547 5000000000 26700460756153 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(948509043/2000000000 : ℝ), (269339093/625000000 : ℝ), (-1762875547/5000000000 : ℝ)] ![(38870000074741/100000000000000 : ℝ), (34429539147331/100000000000000 : ℝ), (26700460756153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(948509043/2000000000 : ℝ)|^19 ≤ (38870000074741/100000000000000 : ℝ)^15
        have hw : |(948509043/2000000000 : ℝ)|=(948509043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269339093/625000000 : ℝ)|^19 ≤ (34429539147331/100000000000000 : ℝ)^15
        have hw : |(269339093/625000000 : ℝ)|=(269339093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762875547/5000000000 : ℝ)|^19 ≤ (26700460756153/100000000000000 : ℝ)^15
        have hw : |(-1762875547/5000000000 : ℝ)|=(1762875547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4745968913/10000000000 : ℝ)*x 0 + (-134607719/312500000 : ℝ)*x 1 + (1762066201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4745968913/10000000000 : ℝ)^19 ≤ (38905547049513/100000000000000 : ℝ)^15 := by
    have hnat : (4745968913 : ℕ)^19*100000000000000^15 ≤ 38905547049513^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745968913 10000000000 38905547049513 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134607719/312500000 : ℝ)^19 ≤ (8602379611911/25000000000000 : ℝ)^15 := by
    have hnat : (134607719 : ℕ)^19*25000000000000^15 ≤ 8602379611911^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134607719 312500000 8602379611911 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762066201/5000000000 : ℝ)^19 ≤ (26684934488093/100000000000000 : ℝ)^15 := by
    have hnat : (1762066201 : ℕ)^19*100000000000000^15 ≤ 26684934488093^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762066201 5000000000 26684934488093 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4745968913/10000000000 : ℝ), (-134607719/312500000 : ℝ), (1762066201/5000000000 : ℝ)] ![(38905547049513/100000000000000 : ℝ), (8602379611911/25000000000000 : ℝ), (26684934488093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4745968913/10000000000 : ℝ)|^19 ≤ (38905547049513/100000000000000 : ℝ)^15
        have hw : |(4745968913/10000000000 : ℝ)|=(4745968913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134607719/312500000 : ℝ)|^19 ≤ (8602379611911/25000000000000 : ℝ)^15
        have hw : |(-134607719/312500000 : ℝ)|=(134607719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1762066201/5000000000 : ℝ)|^19 ≤ (26684934488093/100000000000000 : ℝ)^15
        have hw : |(1762066201/5000000000 : ℝ)|=(1762066201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314038_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5904271477/10000000000 : ℝ)*x 0 + (-1435697921/5000000000 : ℝ)*x 1 + (-1835960271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5904271477/10000000000 : ℝ)^19 ≤ (320644666341/625000000000 : ℝ)^15 := by
    have hnat : (5904271477 : ℕ)^19*625000000000^15 ≤ 320644666341^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904271477 10000000000 320644666341 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435697921/5000000000 : ℝ)^19 ≤ (20586596469407/100000000000000 : ℝ)^15 := by
    have hnat : (1435697921 : ℕ)^19*100000000000000^15 ≤ 20586596469407^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435697921 5000000000 20586596469407 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1835960271/5000000000 : ℝ)^19 ≤ (439222764133/1562500000000 : ℝ)^15 := by
    have hnat : (1835960271 : ℕ)^19*1562500000000^15 ≤ 439222764133^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835960271 5000000000 439222764133 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5904271477/10000000000 : ℝ), (-1435697921/5000000000 : ℝ), (-1835960271/5000000000 : ℝ)] ![(320644666341/625000000000 : ℝ), (20586596469407/100000000000000 : ℝ), (439222764133/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5904271477/10000000000 : ℝ)|^19 ≤ (320644666341/625000000000 : ℝ)^15
        have hw : |(5904271477/10000000000 : ℝ)|=(5904271477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1435697921/5000000000 : ℝ)|^19 ≤ (20586596469407/100000000000000 : ℝ)^15
        have hw : |(-1435697921/5000000000 : ℝ)|=(1435697921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1835960271/5000000000 : ℝ)|^19 ≤ (439222764133/1562500000000 : ℝ)^15
        have hw : |(-1835960271/5000000000 : ℝ)|=(1835960271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314038 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-784047259/10000000000 : ℝ)*X 0 0+(-36148611/80000000 : ℝ)*X 0 1+(-3317024927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5068777171/10000000000 : ℝ)*X 1 0+(271930927/625000000 : ℝ)*X 1 1+(-779813653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-640081537/10000000000 : ℝ)*X 0 0+(-1000349507/2000000000 : ℝ)*X 0 1+(-6268490891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5020077723/10000000000 : ℝ)*X 1 0+(51569991/100000000 : ℝ)*X 1 1+(-2236943843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5020078571/10000000000 : ℝ)*X 2 0+(-3483165261/10000000000 : ℝ)*X 2 1+(4060884913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((890849951/1250000000 : ℝ)*X 0 0+(-69294441/625000000 : ℝ)*X 0 1+(-3734635199/10000000000 : ℝ)*X 0 2+(890849951/1250000000 : ℝ)*X 1 0+(-69294441/625000000 : ℝ)*X 1 1+(-3734635199/10000000000 : ℝ)*X 1 2+(890849951/1250000000 : ℝ)*X 2 0+(-69294441/625000000 : ℝ)*X 2 1+(-3734635199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-16618739/5000000000 : ℝ)*X 0 0+(-1068938499/2500000000 : ℝ)*X 0 1+(-7189415579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((181477647/400000000 : ℝ)*X 1 0+(4574627987/10000000000 : ℝ)*X 1 1+(-433097913/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2937620657/5000000000 : ℝ)*X 2 0+(-935132703/2500000000 : ℝ)*X 2 1+(566609077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2228141197/2500000000 : ℝ)*X 0 0+(-441975499/5000000000 : ℝ)*X 0 1+(-743154433/5000000000 : ℝ)*X 0 2+(2228141197/2500000000 : ℝ)*X 1 0+(-441975499/5000000000 : ℝ)*X 1 1+(-743154433/5000000000 : ℝ)*X 1 2+(2228141197/2500000000 : ℝ)*X 2 0+(-441975499/5000000000 : ℝ)*X 2 1+(-743154433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-19172573/5000000000 : ℝ)*X 0 0+(-60505761/125000000 : ℝ)*X 0 1+(-3341656357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2935067023/5000000000 : ℝ)*X 1 0+(3982103779/10000000000 : ℝ)*X 1 1+(-2573648701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((903005481/2000000000 : ℝ)*X 2 0+(-4879310613/10000000000 : ℝ)*X 2 1+(630703373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1793212339/2000000000 : ℝ)*X 0 0+(-240578733/2500000000 : ℝ)*X 0 1+(-1328685797/10000000000 : ℝ)*X 0 2+(1793212339/2000000000 : ℝ)*X 1 0+(-240578733/2500000000 : ℝ)*X 1 1+(-1328685797/10000000000 : ℝ)*X 1 2+(1793212339/2000000000 : ℝ)*X 2 0+(-240578733/2500000000 : ℝ)*X 2 1+(-1328685797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6299/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6299/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (724714342907417365053/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256817231611/200000000000 : ℝ)*(base39) + (399659/500000000000 : ℝ)*(base50) + (106783432059/250000000000 : ℝ)*(base59) + (3575555890577/1000000000000 : ℝ)*(major_s0_0) + (3575555890577/1000000000000 : ℝ)*(major_s0_1) + (3575555890577/1000000000000 : ℝ)*(major_s0_2) + (315381/250000000000 : ℝ)*(sp_s0_1) + (5073110742511/1000000000000 : ℝ)*(sp_s0_7) + (5073072143937/1000000000000 : ℝ)*(sp_s0_8) + (1268270838103/250000000000 : ℝ)*(sp_s0_9) + (2077977956853/1000000000000 : ℝ)*(sp_s0_13) + (725039/12500000000 : ℝ)*(sp_s0_15) + (20666069/1000000000000 : ℝ)*(sp_s0_20) + (48056169/1000000000000 : ℝ)*(sp_s0_22) + (2077977956853/1000000000000 : ℝ)*(f.failure) + (253656570429/50000000000 : ℝ)*(f.sum) + (89207171141649/200000000000000000000000000 : ℝ)*base62 + (267673808127427/10000000000000000000000000000 : ℝ)*base64 + (2105281004872573/10000000000000000000000000000 : ℝ)*base66 + (260598855441649/400000000000000000000000000 : ℝ)*base68 + (1052110682042163/2500000000000000000000000000 : ℝ)*base70 + (7878474124872573/10000000000000000000000000000 : ℝ)*base73 + (376403841121649/400000000000000000000000000 : ℝ)*base74 + (202429607598351/400000000000000000000000000 : ℝ)*base77 + (722340797/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (38857/100000000000000000 : ℝ)*base87 + (38857/100000000000000000 : ℝ)*base89 + (38857/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21353/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-21353/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20880153585337738085187/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142567/20000000000 : ℝ)*(base12) + (527403627973/500000000000 : ℝ)*(base39) + (203332143823/250000000000 : ℝ)*(base59) + (10970932106779/1000000000000 : ℝ)*(major_s0_0) + (263320299687/50000000000 : ℝ)*(major_s0_1) + (263320299687/50000000000 : ℝ)*(major_s0_2) + (18983499/1000000000000 : ℝ)*(sp_s0_0) + (5704526113039/1000000000000 : ℝ)*(sp_s0_3) + (7084643/500000000000 : ℝ)*(sp_s0_9) + (48673/500000000000 : ℝ)*(sp_s0_13) + (74721483471/10000000000 : ℝ)*(sp_s0_14) + (149443489179/20000000000 : ℝ)*(sp_s0_15) + (58376252263/7812500000 : ℝ)*(sp_s0_16) + (3060636039169/1000000000000 : ℝ)*(sp_s0_19) + (612127227303/200000000000 : ℝ)*(f.failure) + (149443489179/20000000000 : ℝ)*(f.sum) + (816099846719/10000000000000000000000000 : ℝ)*base62 + (339619626282037/500000000000000000000000000 : ℝ)*base64 + (614268872867963/500000000000000000000000000 : ℝ)*base66 + (5296753072281/20000000000000000000000000 : ℝ)*base69 + (238198902127237/2000000000000000000000000000 : ℝ)*base71 + (2297311256638271/10000000000000000000000000000 : ℝ)*base73 + (6191387968281/20000000000000000000000000 : ℝ)*base75 + (98045309468923/400000000000000000000000000 : ℝ)*base76 + (5799895987279011/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (93/20000000000000000 : ℝ)*base86 + (93/20000000000000000 : ℝ)*base88 + (93/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42113/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42113/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1690174774774437/156250000000000000000 : ℝ) := by norm_num
    linear_combination (101064555487/62500000000 : ℝ)*(base39) + (49037293473/62500000000 : ℝ)*(base59) + (506215020289/62500000000 : ℝ)*(major_s0_0) + (1040225881777/200000000000 : ℝ)*(major_s0_1) + (1040225881777/200000000000 : ℝ)*(major_s0_2) + (2898310915739/1000000000000 : ℝ)*(sp_s0_3) + (4431799/40000000000 : ℝ)*(sp_s0_7) + (64188921/1000000000000 : ℝ)*(sp_s0_8) + (2199023/100000000000 : ℝ)*(sp_s0_16) + (104449527/500000000000 : ℝ)*(sp_s0_19) + (230607642649/31250000000 : ℝ)*(sp_s0_20) + (3689745585411/500000000000 : ℝ)*(sp_s0_21) + (7379533369513/1000000000000 : ℝ)*(sp_s0_22) + (188905684579/62500000000 : ℝ)*(sp_s0_25) + (1511349926159/500000000000 : ℝ)*(f.failure) + (7379555359743/1000000000000 : ℝ)*(f.sum) + (5565072952049/40000000000000000000000000 : ℝ)*base62 + (583293574478627/2000000000000000000000000000 : ℝ)*base64 + (1015397694721373/2000000000000000000000000000 : ℝ)*base66 + (25887522547951/80000000000000000000000000 : ℝ)*base69 + (643754089897933/2000000000000000000000000000 : ℝ)*base71 + (74320813678239/625000000000000000000000000 : ℝ)*base72 + (25988696227951/80000000000000000000000000 : ℝ)*base75 + (9886849015293/25000000000000000000000000 : ℝ)*base76 + (3312050338541311/10000000000000000000000000000 : ℝ)*base79 + (2971/50000000000000000 : ℝ)*base87 + (2971/50000000000000000 : ℝ)*base89 + (2971/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (6299/50000 : ℝ) ^ (37/8 : ℝ) ≤ (55205825147729/800000000000000000 : ℝ) := by
    have hpowers : (6299/50000 : ℝ)^37 ≤ (55205825147729/800000000000000000 : ℝ)^8 := by
      have hnat : (6299 : ℕ)^37*800000000000000000^8 ≤ 55205825147729^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6299 50000 55205825147729 800000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6299/50000 : ℝ)) (X := (55205825147729/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (800055205825147729/800000000000000000 : ℝ) ≤ (1000014920089799/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (800055205825147729/800000000000000000 : ℝ)^8 ≤ (1000014920089799/1000000000000000 : ℝ)^37 := by
      have hnat : (800055205825147729 : ℕ)^8*1000000000000000^37 ≤ 1000014920089799^37*800000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800055205825147729 800000000000000000 1000014920089799 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000014920089799/1000000000000000 : ℝ)) (X := (800055205825147729/800000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (400055205825147729/400000000000000000 : ℝ) ≤ (10000298393726957/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (400055205825147729/400000000000000000 : ℝ)^8 ≤ (10000298393726957/10000000000000000 : ℝ)^37 := by
      have hnat : (400055205825147729 : ℕ)^8*10000000000000000^37 ≤ 10000298393726957^37*400000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400055205825147729 400000000000000000 10000298393726957 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000298393726957/10000000000000000 : ℝ)) (X := (400055205825147729/400000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14920089799/125980000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(149192828967/1259800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (6299/50000 : ℝ)) (alpha := (14920089799/125980000000000 : ℝ)) (beta := (149192828967/1259800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6299/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14920089799/125980000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(149192828967/1259800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (21353/50000 : ℝ) ^ (37/8 : ℝ) ≤ (977194799517399201/50000000000000000000 : ℝ) := by
    have hpowers : (21353/50000 : ℝ)^37 ≤ (977194799517399201/50000000000000000000 : ℝ)^8 := by
      have hnat : (21353 : ℕ)^37*50000000000000000000^8 ≤ 977194799517399201^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21353 50000 977194799517399201 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21353/50000 : ℝ)) (X := (977194799517399201/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50977194799517399201/50000000000000000000 : ℝ) ≤ (1255242141517939/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50977194799517399201/50000000000000000000 : ℝ)^8 ≤ (1255242141517939/1250000000000000 : ℝ)^37 := by
      have hnat : (50977194799517399201 : ℕ)^8*1250000000000000^37 ≤ 1255242141517939^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50977194799517399201 50000000000000000000 1255242141517939 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255242141517939/1250000000000000 : ℝ)) (X := (50977194799517399201/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25977194799517399201/25000000000000000000 : ℝ) ≤ (1008324883457417/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (25977194799517399201/25000000000000000000 : ℝ)^8 ≤ (1008324883457417/1000000000000000 : ℝ)^37 := by
      have hnat : (25977194799517399201 : ℕ)^8*1000000000000000^37 ≤ 1008324883457417^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25977194799517399201 25000000000000000000 1008324883457417 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1008324883457417/1000000000000000 : ℝ)) (X := (25977194799517399201/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5242141517939/533825000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(20655851215329/2135300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (21353/50000 : ℝ)) (alpha := (5242141517939/533825000000000 : ℝ)) (beta := (20655851215329/2135300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21353/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5242141517939/533825000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(20655851215329/2135300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (42113/100000 : ℝ) ^ (37/8 : ℝ) ≤ (915998659930330831/50000000000000000000 : ℝ) := by
    have hpowers : (42113/100000 : ℝ)^37 ≤ (915998659930330831/50000000000000000000 : ℝ)^8 := by
      have hnat : (42113 : ℕ)^37*50000000000000000000^8 ≤ 915998659930330831^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42113 100000 915998659930330831 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42113/100000 : ℝ)) (X := (915998659930330831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50915998659930330831/50000000000000000000 : ℝ) ≤ (10039329428303419/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50915998659930330831/50000000000000000000 : ℝ)^8 ≤ (10039329428303419/10000000000000000 : ℝ)^37 := by
      have hnat : (50915998659930330831 : ℕ)^8*10000000000000000^37 ≤ 10039329428303419^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50915998659930330831 50000000000000000000 10039329428303419 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10039329428303419/10000000000000000 : ℝ)) (X := (50915998659930330831/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25915998659930330831/25000000000000000000 : ℝ) ≤ (1007810813951103/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (25915998659930330831/25000000000000000000 : ℝ)^8 ≤ (1007810813951103/1000000000000000 : ℝ)^37 := by
      have hnat : (25915998659930330831 : ℕ)^8*1000000000000000^37 ≤ 1007810813951103^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25915998659930330831 25000000000000000000 1007810813951103 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007810813951103/1000000000000000 : ℝ)) (X := (25915998659930330831/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(39329428303419/4211300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(38778711207611/4211300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (42113/100000 : ℝ)) (alpha := (39329428303419/4211300000000000 : ℝ)) (beta := (38778711207611/4211300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42113/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(39329428303419/4211300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(38778711207611/4211300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1153147879/5000000000 : ℝ)*X 0 0+(-4432682423/10000000000 : ℝ)*X 0 1+(-1133696539/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((948509043/2000000000 : ℝ)*X 1 0+(269339093/625000000 : ℝ)*X 1 1+(-1762875547/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4745968913/10000000000 : ℝ)*X 2 0+(-134607719/312500000 : ℝ)*X 2 1+(1762066201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5904271477/10000000000 : ℝ)*X 0 0+(-1435697921/5000000000 : ℝ)*X 0 1+(-1835960271/5000000000 : ℝ)*X 0 2+(5904271477/10000000000 : ℝ)*X 1 0+(-1435697921/5000000000 : ℝ)*X 1 1+(-1835960271/5000000000 : ℝ)*X 1 2+(5904271477/10000000000 : ℝ)*X 2 0+(-1435697921/5000000000 : ℝ)*X 2 1+(-1835960271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-82148007183981338605538392282665171/11328611523622000000000000000000000 : ℝ) := by norm_num
    linear_combination (13417/1000000000000 : ℝ)*(base10) + (3329/200000000000 : ℝ)*(base12) + (14547/1000000000000 : ℝ)*(base17) + (446629498629/500000000000 : ℝ)*(base39) + (196091445567/500000000000 : ℝ)*(base40) + (86567791301/250000000000 : ℝ)*(base59) + (5529/500000000000 : ℝ)*(ratio_s0_2) + (172069/100000 : ℝ)*(major_s1_0) + (860345001283/500000000000 : ℝ)*(major_s1_1) + (172069/100000 : ℝ)*(major_s1_2) + (483424974111/200000000000 : ℝ)*(sp_s1_0) + (151070305219/62500000000 : ℝ)*(sp_s1_1) + (2417124900617/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2417124898051/1000000000000 : ℝ)*(f.sum) + (690166902487839413/22480972225000000000000000000000 : ℝ)*base62 + (30717276316311/84226000000000000000000000 : ℝ)*base64 + (52536674531259/533825000000000000000000000 : ℝ)*base67 + (1417258908621/5264125000000000000000000 : ℝ)*base68 + (4227596668657227/5181050527343750000000000000 : ℝ)*base70 + (49220830529/246054687500000000000000 : ℝ)*base73 + (78414795243617/1067650000000000000000000000 : ℝ)*base74 + (600691068973/1968437500000000000000000 : ℝ)*base76 + (479344420882940017/6725127350000000000000000000000 : ℝ)*base79 + (1283/500000000000 : ℝ)*base81 + (1283/500000000000 : ℝ)*base85 + (1283/500000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p014_b019 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c314038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

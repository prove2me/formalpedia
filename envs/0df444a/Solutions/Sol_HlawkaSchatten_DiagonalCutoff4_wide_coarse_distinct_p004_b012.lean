-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:05.065632+00:00
-- url     : https://prove2.me/submissions/24b9584a-b847-4d9f-ba35-4ff9f2ed0459

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
theorem collision_support_c304025_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-172178883/312500000 : ℝ)*x 0 + (1602235049/5000000000 : ℝ)*x 1 + (4139636289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172178883/312500000 : ℝ)^17 ≤ (2866536870873/6250000000000 : ℝ)^13 := by
    have hnat : (172178883 : ℕ)^17*6250000000000^13 ≤ 2866536870873^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172178883 312500000 2866536870873 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1602235049/5000000000 : ℝ)^17 ≤ (903111154841/4000000000000 : ℝ)^13 := by
    have hnat : (1602235049 : ℕ)^17*4000000000000^13 ≤ 903111154841^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602235049 5000000000 903111154841 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139636289/10000000000 : ℝ)^17 ≤ (31557631189443/100000000000000 : ℝ)^13 := by
    have hnat : (4139636289 : ℕ)^17*100000000000000^13 ≤ 31557631189443^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139636289 10000000000 31557631189443 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172178883/312500000 : ℝ), (1602235049/5000000000 : ℝ), (4139636289/10000000000 : ℝ)] ![(2866536870873/6250000000000 : ℝ), (903111154841/4000000000000 : ℝ), (31557631189443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172178883/312500000 : ℝ)|^17 ≤ (2866536870873/6250000000000 : ℝ)^13
        have hw : |(-172178883/312500000 : ℝ)|=(172178883/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1602235049/5000000000 : ℝ)|^17 ≤ (903111154841/4000000000000 : ℝ)^13
        have hw : |(1602235049/5000000000 : ℝ)|=(1602235049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139636289/10000000000 : ℝ)|^17 ≤ (31557631189443/100000000000000 : ℝ)^13
        have hw : |(4139636289/10000000000 : ℝ)|=(4139636289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2337377417/5000000000 : ℝ)*x 0 + (-2718849689/10000000000 : ℝ)*x 1 + (5411015523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2337377417/5000000000 : ℝ)^17 ≤ (18497633863371/50000000000000 : ℝ)^13 := by
    have hnat : (2337377417 : ℕ)^17*50000000000000^13 ≤ 18497633863371^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337377417 5000000000 18497633863371 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718849689/10000000000 : ℝ)^17 ≤ (2276459287897/12500000000000 : ℝ)^13 := by
    have hnat : (2718849689 : ℕ)^17*12500000000000^13 ≤ 2276459287897^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718849689 10000000000 2276459287897 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411015523/10000000000 : ℝ)^17 ≤ (44793057954259/100000000000000 : ℝ)^13 := by
    have hnat : (5411015523 : ℕ)^17*100000000000000^13 ≤ 44793057954259^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411015523 10000000000 44793057954259 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2337377417/5000000000 : ℝ), (-2718849689/10000000000 : ℝ), (5411015523/10000000000 : ℝ)] ![(18497633863371/50000000000000 : ℝ), (2276459287897/12500000000000 : ℝ), (44793057954259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2337377417/5000000000 : ℝ)|^17 ≤ (18497633863371/50000000000000 : ℝ)^13
        have hw : |(2337377417/5000000000 : ℝ)|=(2337377417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2718849689/10000000000 : ℝ)|^17 ≤ (2276459287897/12500000000000 : ℝ)^13
        have hw : |(-2718849689/10000000000 : ℝ)|=(2718849689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411015523/10000000000 : ℝ)|^17 ≤ (44793057954259/100000000000000 : ℝ)^13
        have hw : |(5411015523/10000000000 : ℝ)|=(5411015523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3467010981/10000000000 : ℝ)*x 0 + (3321390773/5000000000 : ℝ)*x 1 + (-501935553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3467010981/10000000000 : ℝ)^17 ≤ (25026664770637/100000000000000 : ℝ)^13 := by
    have hnat : (3467010981 : ℕ)^17*100000000000000^13 ≤ 25026664770637^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3467010981 10000000000 25026664770637 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3321390773/5000000000 : ℝ)^17 ≤ (58571780067319/100000000000000 : ℝ)^13 := by
    have hnat : (3321390773 : ℕ)^17*100000000000000^13 ≤ 58571780067319^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3321390773 5000000000 58571780067319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501935553/2000000000 : ℝ)^17 ≤ (16401555146159/100000000000000 : ℝ)^13 := by
    have hnat : (501935553 : ℕ)^17*100000000000000^13 ≤ 16401555146159^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501935553 2000000000 16401555146159 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3467010981/10000000000 : ℝ), (3321390773/5000000000 : ℝ), (-501935553/2000000000 : ℝ)] ![(25026664770637/100000000000000 : ℝ), (58571780067319/100000000000000 : ℝ), (16401555146159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3467010981/10000000000 : ℝ)|^17 ≤ (25026664770637/100000000000000 : ℝ)^13
        have hw : |(3467010981/10000000000 : ℝ)|=(3467010981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3321390773/5000000000 : ℝ)|^17 ≤ (58571780067319/100000000000000 : ℝ)^13
        have hw : |(3321390773/5000000000 : ℝ)|=(3321390773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501935553/2000000000 : ℝ)|^17 ≤ (16401555146159/100000000000000 : ℝ)^13
        have hw : |(-501935553/2000000000 : ℝ)|=(501935553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5764196273/10000000000 : ℝ)*x 0 + (321985283/1250000000 : ℝ)*x 1 + (4419506621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5764196273/10000000000 : ℝ)^17 ≤ (6081769135977/12500000000000 : ℝ)^13 := by
    have hnat : (5764196273 : ℕ)^17*12500000000000^13 ≤ 6081769135977^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764196273 10000000000 6081769135977 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321985283/1250000000 : ℝ)^17 ≤ (16969633901829/100000000000000 : ℝ)^13 := by
    have hnat : (321985283 : ℕ)^17*100000000000000^13 ≤ 16969633901829^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321985283 1250000000 16969633901829 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419506621/10000000000 : ℝ)^17 ≤ (34376212996653/100000000000000 : ℝ)^13 := by
    have hnat : (4419506621 : ℕ)^17*100000000000000^13 ≤ 34376212996653^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419506621 10000000000 34376212996653 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5764196273/10000000000 : ℝ), (321985283/1250000000 : ℝ), (4419506621/10000000000 : ℝ)] ![(6081769135977/12500000000000 : ℝ), (16969633901829/100000000000000 : ℝ), (34376212996653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5764196273/10000000000 : ℝ)|^17 ≤ (6081769135977/12500000000000 : ℝ)^13
        have hw : |(-5764196273/10000000000 : ℝ)|=(5764196273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321985283/1250000000 : ℝ)|^17 ≤ (16969633901829/100000000000000 : ℝ)^13
        have hw : |(321985283/1250000000 : ℝ)|=(321985283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419506621/10000000000 : ℝ)|^17 ≤ (34376212996653/100000000000000 : ℝ)^13
        have hw : |(4419506621/10000000000 : ℝ)|=(4419506621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2219183373/5000000000 : ℝ)*x 0 + (-495850143/2500000000 : ℝ)*x 1 + (3093601369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219183373/5000000000 : ℝ)^17 ≤ (34568176706387/100000000000000 : ℝ)^13 := by
    have hnat : (2219183373 : ℕ)^17*100000000000000^13 ≤ 34568176706387^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219183373 5000000000 34568176706387 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495850143/2500000000 : ℝ)^17 ≤ (1507089493709/12500000000000 : ℝ)^13 := by
    have hnat : (495850143 : ℕ)^17*12500000000000^13 ≤ 1507089493709^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495850143 2500000000 1507089493709 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3093601369/5000000000 : ℝ)^17 ≤ (53375107331347/100000000000000 : ℝ)^13 := by
    have hnat : (3093601369 : ℕ)^17*100000000000000^13 ≤ 53375107331347^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093601369 5000000000 53375107331347 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2219183373/5000000000 : ℝ), (-495850143/2500000000 : ℝ), (3093601369/5000000000 : ℝ)] ![(34568176706387/100000000000000 : ℝ), (1507089493709/12500000000000 : ℝ), (53375107331347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2219183373/5000000000 : ℝ)|^17 ≤ (34568176706387/100000000000000 : ℝ)^13
        have hw : |(2219183373/5000000000 : ℝ)|=(2219183373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495850143/2500000000 : ℝ)|^17 ≤ (1507089493709/12500000000000 : ℝ)^13
        have hw : |(-495850143/2500000000 : ℝ)|=(495850143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3093601369/5000000000 : ℝ)|^17 ≤ (53375107331347/100000000000000 : ℝ)^13
        have hw : |(3093601369/5000000000 : ℝ)|=(3093601369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (352514593/1250000000 : ℝ)*x 0 + (7418896193/10000000000 : ℝ)*x 1 + (-2128000223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352514593/1250000000 : ℝ)^17 ≤ (596992012133/3125000000000 : ℝ)^13 := by
    have hnat : (352514593 : ℕ)^17*3125000000000^13 ≤ 596992012133^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352514593 1250000000 596992012133 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7418896193/10000000000 : ℝ)^17 ≤ (67677404178841/100000000000000 : ℝ)^13 := by
    have hnat : (7418896193 : ℕ)^17*100000000000000^13 ≤ 67677404178841^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7418896193 10000000000 67677404178841 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128000223/10000000000 : ℝ)^17 ≤ (13218851421123/100000000000000 : ℝ)^13 := by
    have hnat : (2128000223 : ℕ)^17*100000000000000^13 ≤ 13218851421123^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128000223 10000000000 13218851421123 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(352514593/1250000000 : ℝ), (7418896193/10000000000 : ℝ), (-2128000223/10000000000 : ℝ)] ![(596992012133/3125000000000 : ℝ), (67677404178841/100000000000000 : ℝ), (13218851421123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(352514593/1250000000 : ℝ)|^17 ≤ (596992012133/3125000000000 : ℝ)^13
        have hw : |(352514593/1250000000 : ℝ)|=(352514593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7418896193/10000000000 : ℝ)|^17 ≤ (67677404178841/100000000000000 : ℝ)^13
        have hw : |(7418896193/10000000000 : ℝ)|=(7418896193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128000223/10000000000 : ℝ)|^17 ≤ (13218851421123/100000000000000 : ℝ)^13
        have hw : |(-2128000223/10000000000 : ℝ)|=(2128000223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (454440207/2000000000 : ℝ)*x 0 + (5977491407/10000000000 : ℝ)*x 1 + (4439132309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454440207/2000000000 : ℝ)^17 ≤ (14402250810141/100000000000000 : ℝ)^13 := by
    have hnat : (454440207 : ℕ)^17*100000000000000^13 ≤ 14402250810141^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454440207 2000000000 14402250810141 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5977491407/10000000000 : ℝ)^17 ≤ (51021775052507/100000000000000 : ℝ)^13 := by
    have hnat : (5977491407 : ℕ)^17*100000000000000^13 ≤ 51021775052507^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977491407 10000000000 51021775052507 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439132309/10000000000 : ℝ)^17 ≤ (3457597413337/10000000000000 : ℝ)^13 := by
    have hnat : (4439132309 : ℕ)^17*10000000000000^13 ≤ 3457597413337^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439132309 10000000000 3457597413337 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(454440207/2000000000 : ℝ), (5977491407/10000000000 : ℝ), (4439132309/10000000000 : ℝ)] ![(14402250810141/100000000000000 : ℝ), (51021775052507/100000000000000 : ℝ), (3457597413337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(454440207/2000000000 : ℝ)|^17 ≤ (14402250810141/100000000000000 : ℝ)^13
        have hw : |(454440207/2000000000 : ℝ)|=(454440207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5977491407/10000000000 : ℝ)|^17 ≤ (51021775052507/100000000000000 : ℝ)^13
        have hw : |(5977491407/10000000000 : ℝ)|=(5977491407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439132309/10000000000 : ℝ)|^17 ≤ (3457597413337/10000000000000 : ℝ)^13
        have hw : |(4439132309/10000000000 : ℝ)|=(4439132309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5699163277/10000000000 : ℝ)*x 0 + (2370201219/10000000000 : ℝ)*x 1 + (2329994797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5699163277/10000000000 : ℝ)^17 ≤ (23968787073693/50000000000000 : ℝ)^13 := by
    have hnat : (5699163277 : ℕ)^17*50000000000000^13 ≤ 23968787073693^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699163277 10000000000 23968787073693 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370201219/10000000000 : ℝ)^17 ≤ (237810739729/1562500000000 : ℝ)^13 := by
    have hnat : (2370201219 : ℕ)^17*1562500000000^13 ≤ 237810739729^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370201219 10000000000 237810739729 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2329994797/5000000000 : ℝ)^17 ≤ (36842538492133/100000000000000 : ℝ)^13 := by
    have hnat : (2329994797 : ℕ)^17*100000000000000^13 ≤ 36842538492133^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329994797 5000000000 36842538492133 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5699163277/10000000000 : ℝ), (2370201219/10000000000 : ℝ), (2329994797/5000000000 : ℝ)] ![(23968787073693/50000000000000 : ℝ), (237810739729/1562500000000 : ℝ), (36842538492133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5699163277/10000000000 : ℝ)|^17 ≤ (23968787073693/50000000000000 : ℝ)^13
        have hw : |(-5699163277/10000000000 : ℝ)|=(5699163277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2370201219/10000000000 : ℝ)|^17 ≤ (237810739729/1562500000000 : ℝ)^13
        have hw : |(2370201219/10000000000 : ℝ)|=(2370201219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2329994797/5000000000 : ℝ)|^17 ≤ (36842538492133/100000000000000 : ℝ)^13
        have hw : |(2329994797/5000000000 : ℝ)|=(2329994797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (273416533/500000000 : ℝ)*x 0 + (-2923187559/10000000000 : ℝ)*x 1 + (4437917539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273416533/500000000 : ℝ)^17 ≤ (11353629159471/25000000000000 : ℝ)^13 := by
    have hnat : (273416533 : ℕ)^17*25000000000000^13 ≤ 11353629159471^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273416533 500000000 11353629159471 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2923187559/10000000000 : ℝ)^17 ≤ (20021881718913/100000000000000 : ℝ)^13 := by
    have hnat : (2923187559 : ℕ)^17*100000000000000^13 ≤ 20021881718913^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2923187559 10000000000 20021881718913 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4437917539/10000000000 : ℝ)^17 ≤ (1728180081363/5000000000000 : ℝ)^13 := by
    have hnat : (4437917539 : ℕ)^17*5000000000000^13 ≤ 1728180081363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437917539 10000000000 1728180081363 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273416533/500000000 : ℝ), (-2923187559/10000000000 : ℝ), (4437917539/10000000000 : ℝ)] ![(11353629159471/25000000000000 : ℝ), (20021881718913/100000000000000 : ℝ), (1728180081363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273416533/500000000 : ℝ)|^17 ≤ (11353629159471/25000000000000 : ℝ)^13
        have hw : |(273416533/500000000 : ℝ)|=(273416533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2923187559/10000000000 : ℝ)|^17 ≤ (20021881718913/100000000000000 : ℝ)^13
        have hw : |(-2923187559/10000000000 : ℝ)|=(2923187559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4437917539/10000000000 : ℝ)|^17 ≤ (1728180081363/5000000000000 : ℝ)^13
        have hw : |(4437917539/10000000000 : ℝ)|=(4437917539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3124546969/10000000000 : ℝ)*x 0 + (43845531/62500000 : ℝ)*x 1 + (-474811683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3124546969/10000000000 : ℝ)^17 ≤ (21844239089071/100000000000000 : ℝ)^13 := by
    have hnat : (3124546969 : ℕ)^17*100000000000000^13 ≤ 21844239089071^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124546969 10000000000 21844239089071 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43845531/62500000 : ℝ)^17 ≤ (62903476003717/100000000000000 : ℝ)^13 := by
    have hnat : (43845531 : ℕ)^17*100000000000000^13 ≤ 62903476003717^13*62500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43845531 62500000 62903476003717 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474811683/2000000000 : ℝ)^17 ≤ (3813071223281/25000000000000 : ℝ)^13 := by
    have hnat : (474811683 : ℕ)^17*25000000000000^13 ≤ 3813071223281^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474811683 2000000000 3813071223281 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3124546969/10000000000 : ℝ), (43845531/62500000 : ℝ), (-474811683/2000000000 : ℝ)] ![(21844239089071/100000000000000 : ℝ), (62903476003717/100000000000000 : ℝ), (3813071223281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3124546969/10000000000 : ℝ)|^17 ≤ (21844239089071/100000000000000 : ℝ)^13
        have hw : |(3124546969/10000000000 : ℝ)|=(3124546969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43845531/62500000 : ℝ)|^17 ≤ (62903476003717/100000000000000 : ℝ)^13
        have hw : |(43845531/62500000 : ℝ)|=(43845531/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474811683/2000000000 : ℝ)|^17 ≤ (3813071223281/25000000000000 : ℝ)^13
        have hw : |(-474811683/2000000000 : ℝ)|=(474811683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (127239579/1000000000 : ℝ)*x 0 + (805579741/2000000000 : ℝ)*x 1 + (7006838161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127239579/1000000000 : ℝ)^17 ≤ (3373582797763/50000000000000 : ℝ)^13 := by
    have hnat : (127239579 : ℕ)^17*50000000000000^13 ≤ 3373582797763^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127239579 1000000000 3373582797763 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805579741/2000000000 : ℝ)^17 ≤ (30448383777811/100000000000000 : ℝ)^13 := by
    have hnat : (805579741 : ℕ)^17*100000000000000^13 ≤ 30448383777811^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805579741 2000000000 30448383777811 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7006838161/10000000000 : ℝ)^17 ≤ (15701112652441/25000000000000 : ℝ)^13 := by
    have hnat : (7006838161 : ℕ)^17*25000000000000^13 ≤ 15701112652441^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7006838161 10000000000 15701112652441 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127239579/1000000000 : ℝ), (805579741/2000000000 : ℝ), (7006838161/10000000000 : ℝ)] ![(3373582797763/50000000000000 : ℝ), (30448383777811/100000000000000 : ℝ), (15701112652441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127239579/1000000000 : ℝ)|^17 ≤ (3373582797763/50000000000000 : ℝ)^13
        have hw : |(127239579/1000000000 : ℝ)|=(127239579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805579741/2000000000 : ℝ)|^17 ≤ (30448383777811/100000000000000 : ℝ)^13
        have hw : |(805579741/2000000000 : ℝ)|=(805579741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7006838161/10000000000 : ℝ)|^17 ≤ (15701112652441/25000000000000 : ℝ)^13
        have hw : |(7006838161/10000000000 : ℝ)|=(7006838161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-154868981/250000000 : ℝ)*x 0 + (126858237/500000000 : ℝ)*x 1 + (49657343/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154868981/250000000 : ℝ)^17 ≤ (26730184355497/50000000000000 : ℝ)^13 := by
    have hnat : (154868981 : ℕ)^17*50000000000000^13 ≤ 26730184355497^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154868981 250000000 26730184355497 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126858237/500000000 : ℝ)^17 ≤ (16636858927993/100000000000000 : ℝ)^13 := by
    have hnat : (126858237 : ℕ)^17*100000000000000^13 ≤ 16636858927993^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126858237 500000000 16636858927993 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49657343/125000000 : ℝ)^17 ≤ (7475693085687/25000000000000 : ℝ)^13 := by
    have hnat : (49657343 : ℕ)^17*25000000000000^13 ≤ 7475693085687^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49657343 125000000 7475693085687 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-154868981/250000000 : ℝ), (126858237/500000000 : ℝ), (49657343/125000000 : ℝ)] ![(26730184355497/50000000000000 : ℝ), (16636858927993/100000000000000 : ℝ), (7475693085687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-154868981/250000000 : ℝ)|^17 ≤ (26730184355497/50000000000000 : ℝ)^13
        have hw : |(-154868981/250000000 : ℝ)|=(154868981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126858237/500000000 : ℝ)|^17 ≤ (16636858927993/100000000000000 : ℝ)^13
        have hw : |(126858237/500000000 : ℝ)|=(126858237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49657343/125000000 : ℝ)|^17 ≤ (7475693085687/25000000000000 : ℝ)^13
        have hw : |(49657343/125000000 : ℝ)|=(49657343/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1997176549/5000000000 : ℝ)*x 0 + (-3556903799/10000000000 : ℝ)*x 1 + (667249133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997176549/5000000000 : ℝ)^17 ≤ (6023440001709/20000000000000 : ℝ)^13 := by
    have hnat : (1997176549 : ℕ)^17*20000000000000^13 ≤ 6023440001709^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997176549 5000000000 6023440001709 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3556903799/10000000000 : ℝ)^17 ≤ (6469645320183/25000000000000 : ℝ)^13 := by
    have hnat : (3556903799 : ℕ)^17*25000000000000^13 ≤ 6469645320183^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3556903799 10000000000 6469645320183 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (667249133/1250000000 : ℝ)^17 ≤ (4400421869723/10000000000000 : ℝ)^13 := by
    have hnat : (667249133 : ℕ)^17*10000000000000^13 ≤ 4400421869723^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667249133 1250000000 4400421869723 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1997176549/5000000000 : ℝ), (-3556903799/10000000000 : ℝ), (667249133/1250000000 : ℝ)] ![(6023440001709/20000000000000 : ℝ), (6469645320183/25000000000000 : ℝ), (4400421869723/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1997176549/5000000000 : ℝ)|^17 ≤ (6023440001709/20000000000000 : ℝ)^13
        have hw : |(1997176549/5000000000 : ℝ)|=(1997176549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3556903799/10000000000 : ℝ)|^17 ≤ (6469645320183/25000000000000 : ℝ)^13
        have hw : |(-3556903799/10000000000 : ℝ)|=(3556903799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(667249133/1250000000 : ℝ)|^17 ≤ (4400421869723/10000000000000 : ℝ)^13
        have hw : |(667249133/1250000000 : ℝ)|=(667249133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4058188211/10000000000 : ℝ)*x 0 + (3111725137/5000000000 : ℝ)*x 1 + (-2399628413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4058188211/10000000000 : ℝ)^17 ≤ (30748151415863/100000000000000 : ℝ)^13 := by
    have hnat : (4058188211 : ℕ)^17*100000000000000^13 ≤ 30748151415863^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058188211 10000000000 30748151415863 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3111725137/5000000000 : ℝ)^17 ≤ (53784386085261/100000000000000 : ℝ)^13 := by
    have hnat : (3111725137 : ℕ)^17*100000000000000^13 ≤ 53784386085261^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111725137 5000000000 53784386085261 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399628413/10000000000 : ℝ)^17 ≤ (1546746247839/10000000000000 : ℝ)^13 := by
    have hnat : (2399628413 : ℕ)^17*10000000000000^13 ≤ 1546746247839^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399628413 10000000000 1546746247839 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4058188211/10000000000 : ℝ), (3111725137/5000000000 : ℝ), (-2399628413/10000000000 : ℝ)] ![(30748151415863/100000000000000 : ℝ), (53784386085261/100000000000000 : ℝ), (1546746247839/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4058188211/10000000000 : ℝ)|^17 ≤ (30748151415863/100000000000000 : ℝ)^13
        have hw : |(4058188211/10000000000 : ℝ)|=(4058188211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3111725137/5000000000 : ℝ)|^17 ≤ (53784386085261/100000000000000 : ℝ)^13
        have hw : |(3111725137/5000000000 : ℝ)|=(3111725137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2399628413/10000000000 : ℝ)|^17 ≤ (1546746247839/10000000000000 : ℝ)^13
        have hw : |(-2399628413/10000000000 : ℝ)|=(2399628413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s0_26 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (681684913/5000000000 : ℝ)*x 0 + (2643731857/5000000000 : ℝ)*x 1 + (1452375989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681684913/5000000000 : ℝ)^17 ≤ (184620946101/2500000000000 : ℝ)^13 := by
    have hnat : (681684913 : ℕ)^17*2500000000000^13 ≤ 184620946101^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681684913 5000000000 184620946101 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2643731857/5000000000 : ℝ)^17 ≤ (10865075849583/25000000000000 : ℝ)^13 := by
    have hnat : (2643731857 : ℕ)^17*25000000000000^13 ≤ 10865075849583^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643731857 5000000000 10865075849583 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452375989/2500000000 : ℝ)^17 ≤ (49154858734033/100000000000000 : ℝ)^13 := by
    have hnat : (1452375989 : ℕ)^17*100000000000000^13 ≤ 49154858734033^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452375989 2500000000 49154858734033 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681684913/5000000000 : ℝ), (2643731857/5000000000 : ℝ), (1452375989/2500000000 : ℝ)] ![(184620946101/2500000000000 : ℝ), (10865075849583/25000000000000 : ℝ), (49154858734033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681684913/5000000000 : ℝ)|^17 ≤ (184620946101/2500000000000 : ℝ)^13
        have hw : |(681684913/5000000000 : ℝ)|=(681684913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2643731857/5000000000 : ℝ)|^17 ≤ (10865075849583/25000000000000 : ℝ)^13
        have hw : |(2643731857/5000000000 : ℝ)|=(2643731857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1452375989/2500000000 : ℝ)|^17 ≤ (49154858734033/100000000000000 : ℝ)^13
        have hw : |(1452375989/2500000000 : ℝ)|=(1452375989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2432883933/5000000000 : ℝ)*x 0 + (4033882909/10000000000 : ℝ)*x 1 + (4033938099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2432883933/5000000000 : ℝ)^17 ≤ (3898434788749/10000000000000 : ℝ)^13 := by
    have hnat : (2432883933 : ℕ)^17*10000000000000^13 ≤ 3898434788749^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432883933 5000000000 3898434788749 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4033882909/10000000000 : ℝ)^17 ≤ (30507553139489/100000000000000 : ℝ)^13 := by
    have hnat : (4033882909 : ℕ)^17*100000000000000^13 ≤ 30507553139489^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033882909 10000000000 30507553139489 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033938099/10000000000 : ℝ)^17 ≤ (30508098961401/100000000000000 : ℝ)^13 := by
    have hnat : (4033938099 : ℕ)^17*100000000000000^13 ≤ 30508098961401^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033938099 10000000000 30508098961401 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2432883933/5000000000 : ℝ), (4033882909/10000000000 : ℝ), (4033938099/10000000000 : ℝ)] ![(3898434788749/10000000000000 : ℝ), (30507553139489/100000000000000 : ℝ), (30508098961401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2432883933/5000000000 : ℝ)|^17 ≤ (3898434788749/10000000000000 : ℝ)^13
        have hw : |(-2432883933/5000000000 : ℝ)|=(2432883933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4033882909/10000000000 : ℝ)|^17 ≤ (30507553139489/100000000000000 : ℝ)^13
        have hw : |(4033882909/10000000000 : ℝ)|=(4033882909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033938099/10000000000 : ℝ)|^17 ≤ (30508098961401/100000000000000 : ℝ)^13
        have hw : |(4033938099/10000000000 : ℝ)|=(4033938099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2088350151/5000000000 : ℝ)*x 0 + (-3462623049/10000000000 : ℝ)*x 1 + (5252709223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088350151/5000000000 : ℝ)^17 ≤ (31927626993153/100000000000000 : ℝ)^13 := by
    have hnat : (2088350151 : ℕ)^17*100000000000000^13 ≤ 31927626993153^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088350151 5000000000 31927626993153 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3462623049/10000000000 : ℝ)^17 ≤ (24985252540211/100000000000000 : ℝ)^13 := by
    have hnat : (3462623049 : ℕ)^17*100000000000000^13 ≤ 24985252540211^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462623049 10000000000 24985252540211 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252709223/10000000000 : ℝ)^17 ≤ (43087120449097/100000000000000 : ℝ)^13 := by
    have hnat : (5252709223 : ℕ)^17*100000000000000^13 ≤ 43087120449097^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252709223 10000000000 43087120449097 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088350151/5000000000 : ℝ), (-3462623049/10000000000 : ℝ), (5252709223/10000000000 : ℝ)] ![(31927626993153/100000000000000 : ℝ), (24985252540211/100000000000000 : ℝ), (43087120449097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088350151/5000000000 : ℝ)|^17 ≤ (31927626993153/100000000000000 : ℝ)^13
        have hw : |(2088350151/5000000000 : ℝ)|=(2088350151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3462623049/10000000000 : ℝ)|^17 ≤ (24985252540211/100000000000000 : ℝ)^13
        have hw : |(-3462623049/10000000000 : ℝ)|=(3462623049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252709223/10000000000 : ℝ)|^17 ≤ (43087120449097/100000000000000 : ℝ)^13
        have hw : |(5252709223/10000000000 : ℝ)|=(5252709223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4176657539/10000000000 : ℝ)*x 0 + (2626369293/5000000000 : ℝ)*x 1 + (-3462634971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176657539/10000000000 : ℝ)^17 ≤ (7981799880607/25000000000000 : ℝ)^13 := by
    have hnat : (4176657539 : ℕ)^17*25000000000000^13 ≤ 7981799880607^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176657539 10000000000 7981799880607 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626369293/5000000000 : ℝ)^17 ≤ (43087435420031/100000000000000 : ℝ)^13 := by
    have hnat : (2626369293 : ℕ)^17*100000000000000^13 ≤ 43087435420031^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626369293 5000000000 43087435420031 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3462634971/10000000000 : ℝ)^17 ≤ (24985365035269/100000000000000 : ℝ)^13 := by
    have hnat : (3462634971 : ℕ)^17*100000000000000^13 ≤ 24985365035269^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462634971 10000000000 24985365035269 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176657539/10000000000 : ℝ), (2626369293/5000000000 : ℝ), (-3462634971/10000000000 : ℝ)] ![(7981799880607/25000000000000 : ℝ), (43087435420031/100000000000000 : ℝ), (24985365035269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176657539/10000000000 : ℝ)|^17 ≤ (7981799880607/25000000000000 : ℝ)^13
        have hw : |(4176657539/10000000000 : ℝ)|=(4176657539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626369293/5000000000 : ℝ)|^17 ≤ (43087435420031/100000000000000 : ℝ)^13
        have hw : |(2626369293/5000000000 : ℝ)|=(2626369293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3462634971/10000000000 : ℝ)|^17 ≤ (24985365035269/100000000000000 : ℝ)^13
        have hw : |(-3462634971/10000000000 : ℝ)|=(3462634971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304025_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (183884717/500000000 : ℝ)*x 0 + (578152709/1250000000 : ℝ)*x 1 + (2312574231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183884717/500000000 : ℝ)^17 ≤ (6758442193971/25000000000000 : ℝ)^13 := by
    have hnat : (183884717 : ℕ)^17*25000000000000^13 ≤ 6758442193971^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183884717 500000000 6758442193971 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578152709/1250000000 : ℝ)^17 ≤ (36483493184803/100000000000000 : ℝ)^13 := by
    have hnat : (578152709 : ℕ)^17*100000000000000^13 ≤ 36483493184803^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578152709 1250000000 36483493184803 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312574231/5000000000 : ℝ)^17 ≤ (18241369012573/50000000000000 : ℝ)^13 := by
    have hnat : (2312574231 : ℕ)^17*50000000000000^13 ≤ 18241369012573^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312574231 5000000000 18241369012573 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183884717/500000000 : ℝ), (578152709/1250000000 : ℝ), (2312574231/5000000000 : ℝ)] ![(6758442193971/25000000000000 : ℝ), (36483493184803/100000000000000 : ℝ), (18241369012573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183884717/500000000 : ℝ)|^17 ≤ (6758442193971/25000000000000 : ℝ)^13
        have hw : |(183884717/500000000 : ℝ)|=(183884717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(578152709/1250000000 : ℝ)|^17 ≤ (36483493184803/100000000000000 : ℝ)^13
        have hw : |(578152709/1250000000 : ℝ)|=(578152709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312574231/5000000000 : ℝ)|^17 ≤ (18241369012573/50000000000000 : ℝ)^13
        have hw : |(2312574231/5000000000 : ℝ)|=(2312574231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304025 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-172178883/312500000 : ℝ)*X 0 0+(1602235049/5000000000 : ℝ)*X 0 1+(4139636289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2337377417/5000000000 : ℝ)*X 1 0+(-2718849689/10000000000 : ℝ)*X 1 1+(5411015523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3467010981/10000000000 : ℝ)*X 2 0+(3321390773/5000000000 : ℝ)*X 2 1+(-501935553/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5764196273/10000000000 : ℝ)*X 0 0+(321985283/1250000000 : ℝ)*X 0 1+(4419506621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2219183373/5000000000 : ℝ)*X 1 0+(-495850143/2500000000 : ℝ)*X 1 1+(3093601369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((352514593/1250000000 : ℝ)*X 2 0+(7418896193/10000000000 : ℝ)*X 2 1+(-2128000223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((454440207/2000000000 : ℝ)*X 0 0+(5977491407/10000000000 : ℝ)*X 0 1+(4439132309/10000000000 : ℝ)*X 0 2+(454440207/2000000000 : ℝ)*X 1 0+(5977491407/10000000000 : ℝ)*X 1 1+(4439132309/10000000000 : ℝ)*X 1 2+(454440207/2000000000 : ℝ)*X 2 0+(5977491407/10000000000 : ℝ)*X 2 1+(4439132309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5699163277/10000000000 : ℝ)*X 0 0+(2370201219/10000000000 : ℝ)*X 0 1+(2329994797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((273416533/500000000 : ℝ)*X 1 0+(-2923187559/10000000000 : ℝ)*X 1 1+(4437917539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3124546969/10000000000 : ℝ)*X 2 0+(43845531/62500000 : ℝ)*X 2 1+(-474811683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((127239579/1000000000 : ℝ)*X 0 0+(805579741/2000000000 : ℝ)*X 0 1+(7006838161/10000000000 : ℝ)*X 0 2+(127239579/1000000000 : ℝ)*X 1 0+(805579741/2000000000 : ℝ)*X 1 1+(7006838161/10000000000 : ℝ)*X 1 2+(127239579/1000000000 : ℝ)*X 2 0+(805579741/2000000000 : ℝ)*X 2 1+(7006838161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-154868981/250000000 : ℝ)*X 0 0+(126858237/500000000 : ℝ)*X 0 1+(49657343/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1997176549/5000000000 : ℝ)*X 1 0+(-3556903799/10000000000 : ℝ)*X 1 1+(667249133/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4058188211/10000000000 : ℝ)*X 2 0+(3111725137/5000000000 : ℝ)*X 2 1+(-2399628413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((681684913/5000000000 : ℝ)*X 0 0+(2643731857/5000000000 : ℝ)*X 0 1+(1452375989/2500000000 : ℝ)*X 0 2+(681684913/5000000000 : ℝ)*X 1 0+(2643731857/5000000000 : ℝ)*X 1 1+(1452375989/2500000000 : ℝ)*X 1 2+(681684913/5000000000 : ℝ)*X 2 0+(2643731857/5000000000 : ℝ)*X 2 1+(1452375989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3167/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3167/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4201290467990703/312500000000000000000 : ℝ) := by norm_num
    linear_combination (1151755448979/1000000000000 : ℝ)*(base50) + (192448557051/250000000000 : ℝ)*(base59) + (97369022633/1000000000000 : ℝ)*(base60) + (4859912327517/1000000000000 : ℝ)*(major_s0_0) + (4859912327517/1000000000000 : ℝ)*(major_s0_1) + (4859912327517/1000000000000 : ℝ)*(major_s0_2) + (114871537/500000000000 : ℝ)*(sp_s0_0) + (10823729/1000000000000 : ℝ)*(sp_s0_1) + (1302995318573/200000000000 : ℝ)*(sp_s0_7) + (6515584227607/1000000000000 : ℝ)*(sp_s0_8) + (1303119010267/200000000000 : ℝ)*(sp_s0_9) + (801049754619/250000000000 : ℝ)*(sp_s0_12) + (388715397/1000000000000 : ℝ)*(sp_s0_13) + (13051919/500000000000 : ℝ)*(sp_s0_26) + (1602112561157/500000000000 : ℝ)*(f.failure) + (1303119010267/200000000000 : ℝ)*(f.sum) + (43280900605481/1000000000000000000000000000 : ℝ)*base62 + (3167696182479/100000000000000000000000000 : ℝ)*base64 + (406915817521/100000000000000000000000000 : ℝ)*base66 + (448257947194519/2000000000000000000000000000 : ℝ)*base69 + (70201794044099/2000000000000000000000000000 : ℝ)*base70 + (28912255542479/100000000000000000000000000 : ℝ)*base73 + (267369860794519/2000000000000000000000000000 : ℝ)*base75 + (1970068977805481/2000000000000000000000000000 : ℝ)*base77 + (10255552542521/50000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (5687/6250000000000000 : ℝ)*base86 + (5687/6250000000000000 : ℝ)*base88 + (5687/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3777/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(3777/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1081866845118168188133/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233992257839/1000000000000 : ℝ)*(base40) + (15899206197/125000000000 : ℝ)*(base50) + (905274453989/1000000000000 : ℝ)*(base59) + (3927051/1000000000000 : ℝ)*(base60) + (1793599857283/500000000000 : ℝ)*(major_s0_0) + (1793599857283/500000000000 : ℝ)*(major_s0_1) + (1793599857283/500000000000 : ℝ)*(major_s0_2) + (9442577/500000000000 : ℝ)*(sp_s0_1) + (89522569/1000000000000 : ℝ)*(sp_s0_2) + (1560543/500000000000 : ℝ)*(sp_s0_8) + (4809294530121/1000000000000 : ℝ)*(sp_s0_13) + (4809272523881/1000000000000 : ℝ)*(sp_s0_14) + (75143828243/15625000000 : ℝ)*(sp_s0_15) + (591275864129/250000000000 : ℝ)*(sp_s0_19) + (591275864129/250000000000 : ℝ)*(f.failure) + (4809294530121/1000000000000 : ℝ)*(f.sum) + (125421723890919/500000000000000000000000000 : ℝ)*base62 + (1017375119879/50000000000000000000000000 : ℝ)*base65 + (45712861264879/50000000000000000000000000 : ℝ)*base66 + (356486636940919/1000000000000000000000000000 : ℝ)*base68 + (617453397738499/1000000000000000000000000000 : ℝ)*base71 + (48711196239879/50000000000000000000000000 : ℝ)*base72 + (623827439440919/1000000000000000000000000000 : ℝ)*base74 + (251817469659081/1000000000000000000000000000 : ℝ)*base76 + (22909968292379/25000000000000000000000000 : ℝ)*base78 + (2961/3125000000000000 : ℝ)*base87 + (2961/3125000000000000 : ℝ)*base89 + (2961/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2453/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2453/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4980958087706272105389/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1027613/500000000000 : ℝ)*(base40) + (191067931883/200000000000 : ℝ)*(base50) + (197319972429/200000000000 : ℝ)*(base59) + (5218790367471/1000000000000 : ℝ)*(major_s0_0) + (5218790367471/1000000000000 : ℝ)*(major_s0_1) + (5218790367471/1000000000000 : ℝ)*(major_s0_2) + (894741/1000000000000 : ℝ)*(sp_s0_0) + (12949659/1000000000000 : ℝ)*(sp_s0_9) + (1091403/50000000000 : ℝ)*(sp_s0_12) + (12355071/1000000000000 : ℝ)*(sp_s0_14) + (6996738494589/1000000000000 : ℝ)*(sp_s0_20) + (6996727034259/1000000000000 : ℝ)*(sp_s0_21) + (6996726439671/1000000000000 : ℝ)*(sp_s0_22) + (3440817857229/1000000000000 : ℝ)*(sp_s0_26) + (3440839685289/1000000000000 : ℝ)*(f.failure) + (699673938933/100000000000 : ℝ)*(f.sum) + (278449956921997/1000000000000000000000000000 : ℝ)*base63 + (75799063365477/100000000000000000000000000 : ℝ)*base64 + (25329158404523/100000000000000000000000000 : ℝ)*base66 + (351152722478003/2000000000000000000000000000 : ℝ)*base68 + (1267552022431537/2000000000000000000000000000 : ℝ)*base70 + (35695673764523/100000000000000000000000000 : ℝ)*base72 + (88222249478003/2000000000000000000000000000 : ℝ)*base74 + (1028829770121997/2000000000000000000000000000 : ℝ)*base76 + (4539197405477/50000000000000000000000000 : ℝ)*base79 + (6651/12500000000000000 : ℝ)*base87 + (6651/12500000000000000 : ℝ)*base89 + (6651/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (3167/12500 : ℝ) ^ (33/8 : ℝ) ≤ (86767975891571217/25000000000000000000 : ℝ) := by
    have hpowers : (3167/12500 : ℝ)^33 ≤ (86767975891571217/25000000000000000000 : ℝ)^8 := by
      have hnat : (3167 : ℕ)^33*25000000000000000000^8 ≤ 86767975891571217^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3167 12500 86767975891571217 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3167/12500 : ℝ)) (X := (86767975891571217/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25086767975891571217/25000000000000000000 : ℝ) ≤ (10008402825343059/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25086767975891571217/25000000000000000000 : ℝ)^8 ≤ (10008402825343059/10000000000000000 : ℝ)^33 := by
      have hnat : (25086767975891571217 : ℕ)^8*10000000000000000^33 ≤ 10008402825343059^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25086767975891571217 25000000000000000000 10008402825343059 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008402825343059/10000000000000000 : ℝ)) (X := (25086767975891571217/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12586767975891571217/12500000000000000000 : ℝ) ≤ (10016783662039601/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12586767975891571217/12500000000000000000 : ℝ)^8 ≤ (10016783662039601/10000000000000000 : ℝ)^33 := by
      have hnat : (12586767975891571217 : ℕ)^8*10000000000000000^33 ≤ 10016783662039601^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12586767975891571217 12500000000000000000 10016783662039601 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016783662039601/10000000000000000 : ℝ)) (X := (12586767975891571217/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8402825343059/2533600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4190418348271/1266800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3167/12500 : ℝ)) (alpha := (8402825343059/2533600000000000 : ℝ)) (beta := (4190418348271/1266800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3167/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8402825343059/2533600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4190418348271/1266800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3777/25000 : ℝ) ^ (33/8 : ℝ) ≤ (205683181329187/500000000000000000 : ℝ) := by
    have hpowers : (3777/25000 : ℝ)^33 ≤ (205683181329187/500000000000000000 : ℝ)^8 := by
      have hnat : (3777 : ℕ)^33*500000000000000000^8 ≤ 205683181329187^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3777 25000 205683181329187 500000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3777/25000 : ℝ)) (X := (205683181329187/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (500205683181329187/500000000000000000 : ℝ) ≤ (10000997096433339/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (500205683181329187/500000000000000000 : ℝ)^8 ≤ (10000997096433339/10000000000000000 : ℝ)^33 := by
      have hnat : (500205683181329187 : ℕ)^8*10000000000000000^33 ≤ 10000997096433339^33*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500205683181329187 500000000000000000 10000997096433339 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000997096433339/10000000000000000 : ℝ)) (X := (500205683181329187/500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (250205683181329187/250000000000000000 : ℝ) ≤ (20003987764613/20000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (250205683181329187/250000000000000000 : ℝ)^8 ≤ (20003987764613/20000000000000 : ℝ)^33 := by
      have hnat : (250205683181329187 : ℕ)^8*20000000000000^33 ≤ 20003987764613^33*250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250205683181329187 250000000000000000 20003987764613 20000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20003987764613/20000000000000 : ℝ)) (X := (250205683181329187/250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(997096433339/1510800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(996785873161/1510800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3777/25000 : ℝ)) (alpha := (997096433339/1510800000000000 : ℝ)) (beta := (996785873161/1510800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (3777/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(997096433339/1510800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(996785873161/1510800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2453/20000 : ℝ) ^ (33/8 : ℝ) ≤ (3481638289633789/20000000000000000000 : ℝ) := by
    have hpowers : (2453/20000 : ℝ)^33 ≤ (3481638289633789/20000000000000000000 : ℝ)^8 := by
      have hnat : (2453 : ℕ)^33*20000000000000000000^8 ≤ 3481638289633789^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2453 20000 3481638289633789 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2453/20000 : ℝ)) (X := (3481638289633789/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20003481638289633789/20000000000000000000 : ℝ) ≤ (10000421988937383/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (20003481638289633789/20000000000000000000 : ℝ)^8 ≤ (10000421988937383/10000000000000000 : ℝ)^33 := by
      have hnat : (20003481638289633789 : ℕ)^8*10000000000000000^33 ≤ 10000421988937383^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003481638289633789 20000000000000000000 10000421988937383 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000421988937383/10000000000000000 : ℝ)) (X := (20003481638289633789/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10003481638289633789/10000000000000000000 : ℝ) ≤ (10000843922236117/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10003481638289633789/10000000000000000000 : ℝ)^8 ≤ (10000843922236117/10000000000000000 : ℝ)^33 := by
      have hnat : (10003481638289633789 : ℕ)^8*10000000000000000^33 ≤ 10000843922236117^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003481638289633789 10000000000000000000 10000843922236117 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000843922236117/10000000000000000 : ℝ)) (X := (10003481638289633789/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(421988937383/1226500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(210966649367/613250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (2453/20000 : ℝ)) (alpha := (421988937383/1226500000000000 : ℝ)) (beta := (210966649367/613250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2453/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(421988937383/1226500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(210966649367/613250000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2432883933/5000000000 : ℝ)*X 0 0+(4033882909/10000000000 : ℝ)*X 0 1+(4033938099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2088350151/5000000000 : ℝ)*X 1 0+(-3462623049/10000000000 : ℝ)*X 1 1+(5252709223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4176657539/10000000000 : ℝ)*X 2 0+(2626369293/5000000000 : ℝ)*X 2 1+(-3462634971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((183884717/500000000 : ℝ)*X 0 0+(578152709/1250000000 : ℝ)*X 0 1+(2312574231/5000000000 : ℝ)*X 0 2+(183884717/500000000 : ℝ)*X 1 0+(578152709/1250000000 : ℝ)*X 1 1+(2312574231/5000000000 : ℝ)*X 1 2+(183884717/500000000 : ℝ)*X 2 0+(578152709/1250000000 : ℝ)*X 2 1+(2312574231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304025_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-147923216702672430612808955065921/24451829022500000000000000000000 : ℝ) := by norm_num
    linear_combination (101721/250000000000 : ℝ)*(base5) + (258407/1000000000000 : ℝ)*(base8) + (265957/1000000000000 : ℝ)*(base23) + (41877/200000000000 : ℝ)*(base40) + (63963775039/1000000000000 : ℝ)*(base49) + (152857986619/500000000000 : ℝ)*(base50) + (109284022413/200000000000 : ℝ)*(base59) + (9568330327/31250000000 : ℝ)*(base60) + (18959/12500 : ℝ)*(major_s1_0) + (18959/12500 : ℝ)*(major_s1_1) + (18959/12500 : ℝ)*(major_s1_2) + (1008262664869/500000000000 : ℝ)*(sp_s1_0) + (403305117629/200000000000 : ℝ)*(sp_s1_1) + (126032858067/62500000000 : ℝ)*(sp_s1_2) + (249999898279/250000000000 : ℝ)*(sp_s1_6) + (403305117629/200000000000 : ℝ)*(f.sum) + (2676296639335577/23162452500000000000000000000 : ℝ)*base63 + (3185405115659/12265000000000000000000000 : ℝ)*base65 + (10913269627421/18885000000000000000000000 : ℝ)*base67 + (623871496319/2453000000000000000000000 : ℝ)*base68 + (16780363356947603/77686510000000000000000000000 : ℝ)*base71 + (3193028348191/31670000000000000000000000 : ℝ)*base73 + (73137769643/295078125000000000000000 : ℝ)*base75 + (120853825391/247421875000000000000000 : ℝ)*base76 + (2169754110975347/2990439750000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p004_b012 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=25 := by omega
  rcases hc with rfl
  · exact collision_c304025 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b012 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

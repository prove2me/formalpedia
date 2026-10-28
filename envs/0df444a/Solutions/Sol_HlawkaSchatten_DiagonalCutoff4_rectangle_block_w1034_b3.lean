-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1034_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:42.233021+00:00
-- url     : https://prove2.me/submissions/d59b6af6-197c-4895-b727-62d1b9f03e61

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1034_s9_0 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336259457/2500000000 : ℝ)*x 0 + (-1143051913/5000000000 : ℝ)*x 1 + (1052774667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336259457/2500000000 : ℝ)^8227 ≤ (21714577093477/50000000000000 : ℝ)^6179 := by
    have hnat : (1336259457 : ℕ)^8227*50000000000000^6179 ≤ 21714577093477^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336259457 2500000000 21714577093477 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143051913/5000000000 : ℝ)^8227 ≤ (7008762967321/50000000000000 : ℝ)^6179 := by
    have hnat : (1143051913 : ℕ)^8227*50000000000000^6179 ≤ 7008762967321^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143051913 5000000000 7008762967321 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052774667/2000000000 : ℝ)^8227 ≤ (10638329966807/25000000000000 : ℝ)^6179 := by
    have hnat : (1052774667 : ℕ)^8227*25000000000000^6179 ≤ 10638329966807^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052774667 2000000000 10638329966807 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336259457/2500000000 : ℝ), (-1143051913/5000000000 : ℝ), (1052774667/2000000000 : ℝ)] ![(21714577093477/50000000000000 : ℝ), (7008762967321/50000000000000 : ℝ), (10638329966807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336259457/2500000000 : ℝ)|^8227 ≤ (21714577093477/50000000000000 : ℝ)^6179
        have hw : |(1336259457/2500000000 : ℝ)|=(1336259457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143051913/5000000000 : ℝ)|^8227 ≤ (7008762967321/50000000000000 : ℝ)^6179
        have hw : |(-1143051913/5000000000 : ℝ)|=(1143051913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052774667/2000000000 : ℝ)|^8227 ≤ (10638329966807/25000000000000 : ℝ)^6179
        have hw : |(1052774667/2000000000 : ℝ)|=(1052774667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s9_1 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-277453519/1250000000 : ℝ)*x 0 + (2632100563/5000000000 : ℝ)*x 1 + (2697279133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277453519/1250000000 : ℝ)^8227 ≤ (13477456262329/100000000000000 : ℝ)^6179 := by
    have hnat : (277453519 : ℕ)^8227*100000000000000^6179 ≤ 13477456262329^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277453519 1250000000 13477456262329 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632100563/5000000000 : ℝ)^8227 ≤ (42556848064231/100000000000000 : ℝ)^6179 := by
    have hnat : (2632100563 : ℕ)^8227*100000000000000^6179 ≤ 42556848064231^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632100563 5000000000 42556848064231 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697279133/5000000000 : ℝ)^8227 ≤ (8793139130993/20000000000000 : ℝ)^6179 := by
    have hnat : (2697279133 : ℕ)^8227*20000000000000^6179 ≤ 8793139130993^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697279133 5000000000 8793139130993 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277453519/1250000000 : ℝ), (2632100563/5000000000 : ℝ), (2697279133/5000000000 : ℝ)] ![(13477456262329/100000000000000 : ℝ), (42556848064231/100000000000000 : ℝ), (8793139130993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277453519/1250000000 : ℝ)|^8227 ≤ (13477456262329/100000000000000 : ℝ)^6179
        have hw : |(-277453519/1250000000 : ℝ)|=(277453519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632100563/5000000000 : ℝ)|^8227 ≤ (42556848064231/100000000000000 : ℝ)^6179
        have hw : |(2632100563/5000000000 : ℝ)|=(2632100563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697279133/5000000000 : ℝ)|^8227 ≤ (8793139130993/20000000000000 : ℝ)^6179
        have hw : |(2697279133/5000000000 : ℝ)|=(2697279133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s9_2 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656061561/5000000000 : ℝ)*x 0 + (-1077709403/5000000000 : ℝ)*x 1 + (5394558269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656061561/5000000000 : ℝ)^8227 ≤ (8614688222523/20000000000000 : ℝ)^6179 := by
    have hnat : (2656061561 : ℕ)^8227*20000000000000^6179 ≤ 8614688222523^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656061561 5000000000 8614688222523 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077709403/5000000000 : ℝ)^8227 ≤ (12960863187121/100000000000000 : ℝ)^6179 := by
    have hnat : (1077709403 : ℕ)^8227*100000000000000^6179 ≤ 12960863187121^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077709403 5000000000 12960863187121 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394558269/10000000000 : ℝ)^8227 ≤ (43965695687519/100000000000000 : ℝ)^6179 := by
    have hnat : (5394558269 : ℕ)^8227*100000000000000^6179 ≤ 43965695687519^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394558269 10000000000 43965695687519 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656061561/5000000000 : ℝ), (-1077709403/5000000000 : ℝ), (5394558269/10000000000 : ℝ)] ![(8614688222523/20000000000000 : ℝ), (12960863187121/100000000000000 : ℝ), (43965695687519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656061561/5000000000 : ℝ)|^8227 ≤ (8614688222523/20000000000000 : ℝ)^6179
        have hw : |(2656061561/5000000000 : ℝ)|=(2656061561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077709403/5000000000 : ℝ)|^8227 ≤ (12960863187121/100000000000000 : ℝ)^6179
        have hw : |(-1077709403/5000000000 : ℝ)|=(1077709403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394558269/10000000000 : ℝ)|^8227 ≤ (43965695687519/100000000000000 : ℝ)^6179
        have hw : |(5394558269/10000000000 : ℝ)|=(5394558269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s9_3 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332007689/625000000 : ℝ)*x 0 + (269727913/500000000 : ℝ)*x 1 + (-43108379/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332007689/625000000 : ℝ)^8227 ≤ (21536720027301/50000000000000 : ℝ)^6179 := by
    have hnat : (332007689 : ℕ)^8227*50000000000000^6179 ≤ 21536720027301^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332007689 625000000 21536720027301 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269727913/500000000 : ℝ)^8227 ≤ (21982847794929/50000000000000 : ℝ)^6179 := by
    have hnat : (269727913 : ℕ)^8227*50000000000000^6179 ≤ 21982847794929^6179*500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269727913 500000000 21982847794929 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43108379/200000000 : ℝ)^8227 ≤ (12960864340011/100000000000000 : ℝ)^6179 := by
    have hnat : (43108379 : ℕ)^8227*100000000000000^6179 ≤ 12960864340011^6179*200000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43108379 200000000 12960864340011 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332007689/625000000 : ℝ), (269727913/500000000 : ℝ), (-43108379/200000000 : ℝ)] ![(21536720027301/50000000000000 : ℝ), (21982847794929/50000000000000 : ℝ), (12960864340011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332007689/625000000 : ℝ)|^8227 ≤ (21536720027301/50000000000000 : ℝ)^6179
        have hw : |(332007689/625000000 : ℝ)|=(332007689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269727913/500000000 : ℝ)|^8227 ≤ (21982847794929/50000000000000 : ℝ)^6179
        have hw : |(269727913/500000000 : ℝ)|=(269727913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43108379/200000000 : ℝ)|^8227 ≤ (12960864340011/100000000000000 : ℝ)^6179
        have hw : |(-43108379/200000000 : ℝ)|=(43108379/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s9_4 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4380125741/10000000000 : ℝ)*x 0 + (45089433/100000000 : ℝ)*x 1 + (1063770883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380125741/10000000000 : ℝ)^8227 ≤ (33316472973569/100000000000000 : ℝ)^6179 := by
    have hnat : (4380125741 : ℕ)^8227*100000000000000^6179 ≤ 33316472973569^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380125741 10000000000 33316472973569 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45089433/100000000 : ℝ)^8227 ≤ (6925474076361/20000000000000 : ℝ)^6179 := by
    have hnat : (45089433 : ℕ)^8227*20000000000000^6179 ≤ 6925474076361^6179*100000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45089433 100000000 6925474076361 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063770883/2500000000 : ℝ)^8227 ≤ (1282246264961/4000000000000 : ℝ)^6179 := by
    have hnat : (1063770883 : ℕ)^8227*4000000000000^6179 ≤ 1282246264961^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063770883 2500000000 1282246264961 4000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380125741/10000000000 : ℝ), (45089433/100000000 : ℝ), (1063770883/2500000000 : ℝ)] ![(33316472973569/100000000000000 : ℝ), (6925474076361/20000000000000 : ℝ), (1282246264961/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380125741/10000000000 : ℝ)|^8227 ≤ (33316472973569/100000000000000 : ℝ)^6179
        have hw : |(4380125741/10000000000 : ℝ)|=(4380125741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45089433/100000000 : ℝ)|^8227 ≤ (6925474076361/20000000000000 : ℝ)^6179
        have hw : |(45089433/100000000 : ℝ)|=(45089433/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063770883/2500000000 : ℝ)|^8227 ≤ (1282246264961/4000000000000 : ℝ)^6179
        have hw : |(1063770883/2500000000 : ℝ)|=(1063770883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1034_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6991/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11207/100000 : ℝ) ^ (4113/1024 : ℝ) ≤ (15211692095291407/100000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^4113 ≤ (15211692095291407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11207 : ℕ)^4113*100000000000000000000^1024 ≤ 15211692095291407^1024*100000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 15211692095291407 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (15211692095291407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13983/100000 : ℝ) ^ (4113/1024 : ℝ) ≤ (37001306709592199/100000000000000000000 : ℝ) := by
    have hpowers : (13983/100000 : ℝ)^4113 ≤ (37001306709592199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13983 : ℕ)^4113*100000000000000000000^1024 ≤ 37001306709592199^1024*100000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13983 100000 37001306709592199 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13983/100000 : ℝ)) (X := (37001306709592199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015211692095291407/50000000000000000000 : ℝ) ≤ (10000757354410653/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50015211692095291407/50000000000000000000 : ℝ)^1024 ≤ (10000757354410653/10000000000000000 : ℝ)^4113 := by
      have hnat : (50015211692095291407 : ℕ)^1024*10000000000000000^4113 ≤ 10000757354410653^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015211692095291407 50000000000000000000 10000757354410653 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757354410653/10000000000000000 : ℝ)) (X := (50015211692095291407/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026106499402441803/50000000000000000000 : ℝ) ≤ (10001299674956221/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50026106499402441803/50000000000000000000 : ℝ)^1024 ≤ (10001299674956221/10000000000000000 : ℝ)^4113 := by
      have hnat : (50026106499402441803 : ℕ)^1024*10000000000000000^4113 ≤ 10001299674956221^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026106499402441803 50000000000000000000 10001299674956221 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001299674956221/10000000000000000 : ℝ)) (X := (50026106499402441803/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037001306709592199/50000000000000000000 : ℝ) ≤ (10001841995501789/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50037001306709592199/50000000000000000000 : ℝ)^1024 ≤ (10001841995501789/10000000000000000 : ℝ)^4113 := by
      have hnat : (50037001306709592199 : ℕ)^1024*10000000000000000^4113 ≤ 10001841995501789^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037001306709592199 50000000000000000000 10001841995501789 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001841995501789/10000000000000000 : ℝ)) (X := (50037001306709592199/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15211692095291407/100000000000000000000 : ℝ) ≤ ((3468743355391951447/3470000000000000000 : ℝ)+2*(16947517049/8675000000000 : ℝ)*(11207/100000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (3468743355391951447/3470000000000000000 : ℝ)+2*(16947517049/8675000000000 : ℝ)*(11207/100000 : ℝ)=(10000757354410653/10000000000000000 : ℝ) by norm_num, show 1+2*(15211692095291407/100000000000000000000 : ℝ)=(50015211692095291407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37001306709592199/100000000000000000000 : ℝ)+(15211692095291407/100000000000000000000 : ℝ) ≤ ((3468743355391951447/3470000000000000000 : ℝ)+(16947517049/8675000000000 : ℝ)*((13983/100000 : ℝ)+(11207/100000 : ℝ)))^(4113/1024 : ℝ) := by
    rw [show (3468743355391951447/3470000000000000000 : ℝ)+(16947517049/8675000000000 : ℝ)*((13983/100000 : ℝ)+(11207/100000 : ℝ))=(10001299674956221/10000000000000000 : ℝ) by norm_num, show 1+(37001306709592199/100000000000000000000 : ℝ)+(15211692095291407/100000000000000000000 : ℝ)=(50026106499402441803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37001306709592199/100000000000000000000 : ℝ) ≤ ((3468743355391951447/3470000000000000000 : ℝ)+2*(16947517049/8675000000000 : ℝ)*(13983/100000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (3468743355391951447/3470000000000000000 : ℝ)+2*(16947517049/8675000000000 : ℝ)*(13983/100000 : ℝ)=(10001841995501789/10000000000000000 : ℝ) by norm_num, show 1+2*(37001306709592199/100000000000000000000 : ℝ)=(50037001306709592199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3468743355391951447/3470000000000000000 : ℝ)*(X 1 0+X 2 0)+(16947517049/8675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (3468743355391951447/3470000000000000000 : ℝ)) (alpha := (16947517049/8675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3468743355391951447/3470000000000000000 : ℝ)*(X 0 1+X 2 1)+(16947517049/8675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (3468743355391951447/3470000000000000000 : ℝ)) (alpha := (16947517049/8675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3468743355391951447/3470000000000000000 : ℝ)*(X 0 2+X 1 2)+(16947517049/8675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (3468743355391951447/3470000000000000000 : ℝ)) (alpha := (16947517049/8675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336259457/2500000000 : ℝ)*X 1 0+(-1143051913/5000000000 : ℝ)*X 1 1+(1052774667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-277453519/1250000000 : ℝ)*X 0 0+(2632100563/5000000000 : ℝ)*X 0 1+(2697279133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2656061561/5000000000 : ℝ)*X 1 0+(-1077709403/5000000000 : ℝ)*X 1 1+(5394558269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((332007689/625000000 : ℝ)*X 2 0+(269727913/500000000 : ℝ)*X 2 1+(-43108379/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4380125741/10000000000 : ℝ)*X 0 0+(45089433/100000000 : ℝ)*X 0 1+(1063770883/2500000000 : ℝ)*X 0 2+(4380125741/10000000000 : ℝ)*X 1 0+(45089433/100000000 : ℝ)*X 1 1+(1063770883/2500000000 : ℝ)*X 1 2+(4380125741/10000000000 : ℝ)*X 2 0+(45089433/100000000 : ℝ)*X 2 1+(1063770883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (436234818648846662382250911/86750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7208131/781250000000 : ℝ)*(base19) + (380964839/50000000000000 : ℝ)*(base23) + (29412499/12500000000000 : ℝ)*(lower1) + (57268101/100000000000000 : ℝ)*(upper3) + (5929893/25000000000000 : ℝ)*(lower4) + (20897787/20000000000000 : ℝ)*(upper5) + (5805192898405229/100000000000000 : ℝ)*(major0) + (5805192898405229/100000000000000 : ℝ)*(major1) + (5805192898405229/100000000000000 : ℝ)*(major2) + (5151707189/50000000000000 : ℝ)*(sp0) + (7671214494993471/100000000000000 : ℝ)*(sp1) + (306848130757533/4000000000000 : ℝ)*(sp2) + (7671213733063793/100000000000000 : ℝ)*(sp3) + (3939171134195527/100000000000000 : ℝ)*(sp4) + (3939171134195527/100000000000000 : ℝ)*(f.failure) + (7671214494993471/100000000000000 : ℝ)*(f.sum) + (1660393869359/1735000000000000000000000000 : ℝ)*base65 + (4654181544425316363/347000000000000000000000000000000 : ℝ)*base67 + (488246948637316363/347000000000000000000000000000000 : ℝ)*base69 + (3044610005260316363/347000000000000000000000000000000 : ℝ)*base71 + (1926453208607/867500000000000000000000000 : ℝ)*base73 + (7015147345794316363/347000000000000000000000000000000 : ℝ)*base75 + (2598487348845683637/347000000000000000000000000000000 : ℝ)*base78 + (5266903098027316363/347000000000000000000000000000000 : ℝ)*base79 + (4159038116297/867500000000000000000000000 : ℝ)*base81 + (22335763/2500000000000000000000 : ℝ)*base90 + (22335763/2500000000000000000000 : ℝ)*base92 + (22335763/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1034_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1034_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1034_box_0 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-130565393/625000000 : ℝ)*x 0 + (2688898031/5000000000 : ℝ)*x 1 + (16805613/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130565393/625000000 : ℝ)^8227 ≤ (12432203221483/100000000000000 : ℝ)^6179 := by
    have hnat : (130565393 : ℕ)^8227*100000000000000^6179 ≤ 12432203221483^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130565393 625000000 12432203221483 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688898031/5000000000 : ℝ)^8227 ≤ (8756779569901/20000000000000 : ℝ)^6179 := by
    have hnat : (2688898031 : ℕ)^8227*20000000000000^6179 ≤ 8756779569901^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688898031 5000000000 8756779569901 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16805613/31250000 : ℝ)^8227 ≤ (8756779782367/20000000000000 : ℝ)^6179 := by
    have hnat : (16805613 : ℕ)^8227*20000000000000^6179 ≤ 8756779782367^6179*31250000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16805613 31250000 8756779782367 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130565393/625000000 : ℝ), (2688898031/5000000000 : ℝ), (16805613/31250000 : ℝ)] ![(12432203221483/100000000000000 : ℝ), (8756779569901/20000000000000 : ℝ), (8756779782367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130565393/625000000 : ℝ)|^8227 ≤ (12432203221483/100000000000000 : ℝ)^6179
        have hw : |(-130565393/625000000 : ℝ)|=(130565393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688898031/5000000000 : ℝ)|^8227 ≤ (8756779569901/20000000000000 : ℝ)^6179
        have hw : |(2688898031/5000000000 : ℝ)|=(2688898031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16805613/31250000 : ℝ)|^8227 ≤ (8756779782367/20000000000000 : ℝ)^6179
        have hw : |(16805613/31250000 : ℝ)|=(16805613/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_1 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1058965599/2000000000 : ℝ)*x 0 + (-275159323/1250000000 : ℝ)*x 1 + (537779587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058965599/2000000000 : ℝ)^8227 ≤ (85773645879/200000000000 : ℝ)^6179 := by
    have hnat : (1058965599 : ℕ)^8227*200000000000^6179 ≤ 85773645879^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058965599 2000000000 85773645879 200000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275159323/1250000000 : ℝ)^8227 ≤ (13329281280913/100000000000000 : ℝ)^6179 := by
    have hnat : (275159323 : ℕ)^8227*100000000000000^6179 ≤ 13329281280913^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275159323 1250000000 13329281280913 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537779587/1000000000 : ℝ)^8227 ≤ (8756779153641/20000000000000 : ℝ)^6179 := by
    have hnat : (537779587 : ℕ)^8227*20000000000000^6179 ≤ 8756779153641^6179*1000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537779587 1000000000 8756779153641 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058965599/2000000000 : ℝ), (-275159323/1250000000 : ℝ), (537779587/1000000000 : ℝ)] ![(85773645879/200000000000 : ℝ), (13329281280913/100000000000000 : ℝ), (8756779153641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058965599/2000000000 : ℝ)|^8227 ≤ (85773645879/200000000000 : ℝ)^6179
        have hw : |(1058965599/2000000000 : ℝ)|=(1058965599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275159323/1250000000 : ℝ)|^8227 ≤ (13329281280913/100000000000000 : ℝ)^6179
        have hw : |(-275159323/1250000000 : ℝ)|=(275159323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537779587/1000000000 : ℝ)|^8227 ≤ (8756779153641/20000000000000 : ℝ)^6179
        have hw : |(537779587/1000000000 : ℝ)|=(537779587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_2 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294827827/10000000000 : ℝ)*x 0 + (5377796103/10000000000 : ℝ)*x 1 + (-17197457/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294827827/10000000000 : ℝ)^8227 ≤ (10721705281931/25000000000000 : ℝ)^6179 := by
    have hnat : (5294827827 : ℕ)^8227*25000000000000^6179 ≤ 10721705281931^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294827827 10000000000 10721705281931 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377796103/10000000000 : ℝ)^8227 ≤ (43783898293949/100000000000000 : ℝ)^6179 := by
    have hnat : (5377796103 : ℕ)^8227*100000000000000^6179 ≤ 43783898293949^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377796103 10000000000 43783898293949 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17197457/78125000 : ℝ)^8227 ≤ (3332320142859/25000000000000 : ℝ)^6179 := by
    have hnat : (17197457 : ℕ)^8227*25000000000000^6179 ≤ 3332320142859^6179*78125000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17197457 78125000 3332320142859 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294827827/10000000000 : ℝ), (5377796103/10000000000 : ℝ), (-17197457/78125000 : ℝ)] ![(10721705281931/25000000000000 : ℝ), (43783898293949/100000000000000 : ℝ), (3332320142859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294827827/10000000000 : ℝ)|^8227 ≤ (10721705281931/25000000000000 : ℝ)^6179
        have hw : |(5294827827/10000000000 : ℝ)|=(5294827827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377796103/10000000000 : ℝ)|^8227 ≤ (43783898293949/100000000000000 : ℝ)^6179
        have hw : |(5377796103/10000000000 : ℝ)|=(5377796103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17197457/78125000 : ℝ)|^8227 ≤ (3332320142859/25000000000000 : ℝ)^6179
        have hw : |(-17197457/78125000 : ℝ)|=(17197457/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_3 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4488875879/10000000000 : ℝ)*x 0 + (4327922051/10000000000 : ℝ)*x 1 + (135247563/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488875879/10000000000 : ℝ)^8227 ≤ (34422330262247/100000000000000 : ℝ)^6179 := by
    have hnat : (4488875879 : ℕ)^8227*100000000000000^6179 ≤ 34422330262247^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488875879 10000000000 34422330262247 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4327922051/10000000000 : ℝ)^8227 ≤ (32788835037293/100000000000000 : ℝ)^6179 := by
    have hnat : (4327922051 : ℕ)^8227*100000000000000^6179 ≤ 32788835037293^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327922051 10000000000 32788835037293 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135247563/312500000 : ℝ)^8227 ≤ (32788834684241/100000000000000 : ℝ)^6179 := by
    have hnat : (135247563 : ℕ)^8227*100000000000000^6179 ≤ 32788834684241^6179*312500000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135247563 312500000 32788834684241 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488875879/10000000000 : ℝ), (4327922051/10000000000 : ℝ), (135247563/312500000 : ℝ)] ![(34422330262247/100000000000000 : ℝ), (32788835037293/100000000000000 : ℝ), (32788834684241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488875879/10000000000 : ℝ)|^8227 ≤ (34422330262247/100000000000000 : ℝ)^6179
        have hw : |(4488875879/10000000000 : ℝ)|=(4488875879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4327922051/10000000000 : ℝ)|^8227 ≤ (32788835037293/100000000000000 : ℝ)^6179
        have hw : |(4327922051/10000000000 : ℝ)|=(4327922051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135247563/312500000 : ℝ)|^8227 ≤ (32788834684241/100000000000000 : ℝ)^6179
        have hw : |(135247563/312500000 : ℝ)|=(135247563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_4 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-235159387/1000000000 : ℝ)*x 0 + (2639798471/5000000000 : ℝ)*x 1 + (5279597759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235159387/1000000000 : ℝ)^8227 ≤ (14554703630031/100000000000000 : ℝ)^6179 := by
    have hnat : (235159387 : ℕ)^8227*100000000000000^6179 ≤ 14554703630031^6179*1000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235159387 1000000000 14554703630031 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639798471/5000000000 : ℝ)^8227 ≤ (42722643778339/100000000000000 : ℝ)^6179 := by
    have hnat : (2639798471 : ℕ)^8227*100000000000000^6179 ≤ 42722643778339^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639798471 5000000000 42722643778339 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279597759/10000000000 : ℝ)^8227 ≤ (10680663145193/25000000000000 : ℝ)^6179 := by
    have hnat : (5279597759 : ℕ)^8227*25000000000000^6179 ≤ 10680663145193^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279597759 10000000000 10680663145193 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235159387/1000000000 : ℝ), (2639798471/5000000000 : ℝ), (5279597759/10000000000 : ℝ)] ![(14554703630031/100000000000000 : ℝ), (42722643778339/100000000000000 : ℝ), (10680663145193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235159387/1000000000 : ℝ)|^8227 ≤ (14554703630031/100000000000000 : ℝ)^6179
        have hw : |(-235159387/1000000000 : ℝ)|=(235159387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639798471/5000000000 : ℝ)|^8227 ≤ (42722643778339/100000000000000 : ℝ)^6179
        have hw : |(2639798471/5000000000 : ℝ)|=(2639798471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279597759/10000000000 : ℝ)|^8227 ≤ (10680663145193/25000000000000 : ℝ)^6179
        have hw : |(5279597759/10000000000 : ℝ)|=(5279597759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_5 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268218803/500000000 : ℝ)*x 0 + (-2239564781/10000000000 : ℝ)*x 1 + (5279596923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268218803/500000000 : ℝ)^8227 ≤ (21819241922367/50000000000000 : ℝ)^6179 := by
    have hnat : (268218803 : ℕ)^8227*50000000000000^6179 ≤ 21819241922367^6179*500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268218803 500000000 21819241922367 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239564781/10000000000 : ℝ)^8227 ≤ (13638872574907/100000000000000 : ℝ)^6179 := by
    have hnat : (2239564781 : ℕ)^8227*100000000000000^6179 ≤ 13638872574907^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239564781 10000000000 13638872574907 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279596923/10000000000 : ℝ)^8227 ≤ (333770652919/781250000000 : ℝ)^6179 := by
    have hnat : (5279596923 : ℕ)^8227*781250000000^6179 ≤ 333770652919^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279596923 10000000000 333770652919 781250000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268218803/500000000 : ℝ), (-2239564781/10000000000 : ℝ), (5279596923/10000000000 : ℝ)] ![(21819241922367/50000000000000 : ℝ), (13638872574907/100000000000000 : ℝ), (333770652919/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268218803/500000000 : ℝ)|^8227 ≤ (21819241922367/50000000000000 : ℝ)^6179
        have hw : |(268218803/500000000 : ℝ)|=(268218803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239564781/10000000000 : ℝ)|^8227 ≤ (13638872574907/100000000000000 : ℝ)^6179
        have hw : |(-2239564781/10000000000 : ℝ)|=(2239564781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279596923/10000000000 : ℝ)|^8227 ≤ (333770652919/781250000000 : ℝ)^6179
        have hw : |(5279596923/10000000000 : ℝ)|=(5279596923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_6 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072875169/2000000000 : ℝ)*x 0 + (105591953/200000000 : ℝ)*x 1 + (-2239564101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072875169/2000000000 : ℝ)^8227 ≤ (43638481516041/100000000000000 : ℝ)^6179 := by
    have hnat : (1072875169 : ℕ)^8227*100000000000000^6179 ≤ 43638481516041^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072875169 2000000000 43638481516041 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105591953/200000000 : ℝ)^8227 ≤ (10680662851599/25000000000000 : ℝ)^6179 := by
    have hnat : (105591953 : ℕ)^8227*25000000000000^6179 ≤ 10680662851599^6179*200000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105591953 200000000 10680662851599 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239564101/10000000000 : ℝ)^8227 ≤ (6819433530579/50000000000000 : ℝ)^6179 := by
    have hnat : (2239564101 : ℕ)^8227*50000000000000^6179 ≤ 6819433530579^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239564101 10000000000 6819433530579 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072875169/2000000000 : ℝ), (105591953/200000000 : ℝ), (-2239564101/10000000000 : ℝ)] ![(43638481516041/100000000000000 : ℝ), (10680662851599/25000000000000 : ℝ), (6819433530579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072875169/2000000000 : ℝ)|^8227 ≤ (43638481516041/100000000000000 : ℝ)^6179
        have hw : |(1072875169/2000000000 : ℝ)|=(1072875169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105591953/200000000 : ℝ)|^8227 ≤ (10680662851599/25000000000000 : ℝ)^6179
        have hw : |(105591953/200000000 : ℝ)|=(105591953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239564101/10000000000 : ℝ)|^8227 ≤ (6819433530579/50000000000000 : ℝ)^6179
        have hw : |(-2239564101/10000000000 : ℝ)|=(2239564101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_7 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2135520429/5000000000 : ℝ)*x 0 + (277301077/625000000 : ℝ)*x 1 + (277301149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135520429/5000000000 : ℝ)^8227 ≤ (32216317480049/100000000000000 : ℝ)^6179 := by
    have hnat : (2135520429 : ℕ)^8227*100000000000000^6179 ≤ 32216317480049^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135520429 5000000000 32216317480049 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277301077/625000000 : ℝ)^8227 ≤ (6778367077789/20000000000000 : ℝ)^6179 := by
    have hnat : (277301077 : ℕ)^8227*20000000000000^6179 ≤ 6778367077789^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277301077 625000000 6778367077789 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277301149/625000000 : ℝ)^8227 ≤ (8472961776371/25000000000000 : ℝ)^6179 := by
    have hnat : (277301149 : ℕ)^8227*25000000000000^6179 ≤ 8472961776371^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277301149 625000000 8472961776371 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135520429/5000000000 : ℝ), (277301077/625000000 : ℝ), (277301149/625000000 : ℝ)] ![(32216317480049/100000000000000 : ℝ), (6778367077789/20000000000000 : ℝ), (8472961776371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135520429/5000000000 : ℝ)|^8227 ≤ (32216317480049/100000000000000 : ℝ)^6179
        have hw : |(2135520429/5000000000 : ℝ)|=(2135520429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277301077/625000000 : ℝ)|^8227 ≤ (6778367077789/20000000000000 : ℝ)^6179
        have hw : |(277301077/625000000 : ℝ)|=(277301077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277301149/625000000 : ℝ)|^8227 ≤ (8472961776371/25000000000000 : ℝ)^6179
        have hw : |(277301149/625000000 : ℝ)|=(277301149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_8 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2296826141/10000000000 : ℝ)*x 0 + (2606513631/5000000000 : ℝ)*x 1 + (269369607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2296826141/10000000000 : ℝ)^8227 ≤ (14105130021007/100000000000000 : ℝ)^6179 := by
    have hnat : (2296826141 : ℕ)^8227*100000000000000^6179 ≤ 14105130021007^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296826141 10000000000 14105130021007 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606513631/5000000000 : ℝ)^8227 ≤ (42006918897949/100000000000000 : ℝ)^6179 := by
    have hnat : (2606513631 : ℕ)^8227*100000000000000^6179 ≤ 42006918897949^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606513631 5000000000 42006918897949 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269369607/500000000 : ℝ)^8227 ≤ (43887951068799/100000000000000 : ℝ)^6179 := by
    have hnat : (269369607 : ℕ)^8227*100000000000000^6179 ≤ 43887951068799^6179*500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269369607 500000000 43887951068799 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2296826141/10000000000 : ℝ), (2606513631/5000000000 : ℝ), (269369607/500000000 : ℝ)] ![(14105130021007/100000000000000 : ℝ), (42006918897949/100000000000000 : ℝ), (43887951068799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2296826141/10000000000 : ℝ)|^8227 ≤ (14105130021007/100000000000000 : ℝ)^6179
        have hw : |(-2296826141/10000000000 : ℝ)|=(2296826141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606513631/5000000000 : ℝ)|^8227 ≤ (42006918897949/100000000000000 : ℝ)^6179
        have hw : |(2606513631/5000000000 : ℝ)|=(2606513631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269369607/500000000 : ℝ)|^8227 ≤ (43887951068799/100000000000000 : ℝ)^6179
        have hw : |(269369607/500000000 : ℝ)|=(269369607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_9 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288027979/10000000000 : ℝ)*x 0 + (-2197461209/10000000000 : ℝ)*x 1 + (538739201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288027979/10000000000 : ℝ)^8227 ≤ (8562700914401/20000000000000 : ℝ)^6179 := by
    have hnat : (5288027979 : ℕ)^8227*20000000000000^6179 ≤ 8562700914401^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288027979 10000000000 8562700914401 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197461209/10000000000 : ℝ)^8227 ≤ (1329854575963/10000000000000 : ℝ)^6179 := by
    have hnat : (2197461209 : ℕ)^8227*10000000000000^6179 ≤ 1329854575963^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197461209 10000000000 1329854575963 10000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538739201/1000000000 : ℝ)^8227 ≤ (43887949658753/100000000000000 : ℝ)^6179 := by
    have hnat : (538739201 : ℕ)^8227*100000000000000^6179 ≤ 43887949658753^6179*1000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538739201 1000000000 43887949658753 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288027979/10000000000 : ℝ), (-2197461209/10000000000 : ℝ), (538739201/1000000000 : ℝ)] ![(8562700914401/20000000000000 : ℝ), (1329854575963/10000000000000 : ℝ), (43887949658753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288027979/10000000000 : ℝ)|^8227 ≤ (8562700914401/20000000000000 : ℝ)^6179
        have hw : |(5288027979/10000000000 : ℝ)|=(5288027979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197461209/10000000000 : ℝ)|^8227 ≤ (1329854575963/10000000000000 : ℝ)^6179
        have hw : |(-2197461209/10000000000 : ℝ)|=(2197461209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538739201/1000000000 : ℝ)|^8227 ≤ (43887949658753/100000000000000 : ℝ)^6179
        have hw : |(538739201/1000000000 : ℝ)|=(538739201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_10 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661003481/1250000000 : ℝ)*x 0 + (1077478363/2000000000 : ℝ)*x 1 + (-2197461647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661003481/1250000000 : ℝ)^8227 ≤ (42813503159853/100000000000000 : ℝ)^6179 := by
    have hnat : (661003481 : ℕ)^8227*100000000000000^6179 ≤ 42813503159853^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661003481 1250000000 42813503159853 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077478363/2000000000 : ℝ)^8227 ≤ (43887947543683/100000000000000 : ℝ)^6179 := by
    have hnat : (1077478363 : ℕ)^8227*100000000000000^6179 ≤ 43887947543683^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077478363 2000000000 43887947543683 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197461647/10000000000 : ℝ)^8227 ≤ (415579665277/3125000000000 : ℝ)^6179 := by
    have hnat : (2197461647 : ℕ)^8227*3125000000000^6179 ≤ 415579665277^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197461647 10000000000 415579665277 3125000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661003481/1250000000 : ℝ), (1077478363/2000000000 : ℝ), (-2197461647/10000000000 : ℝ)] ![(42813503159853/100000000000000 : ℝ), (43887947543683/100000000000000 : ℝ), (415579665277/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661003481/1250000000 : ℝ)|^8227 ≤ (42813503159853/100000000000000 : ℝ)^6179
        have hw : |(661003481/1250000000 : ℝ)|=(661003481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077478363/2000000000 : ℝ)|^8227 ≤ (43887947543683/100000000000000 : ℝ)^6179
        have hw : |(1077478363/2000000000 : ℝ)|=(1077478363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197461647/10000000000 : ℝ)|^8227 ≤ (415579665277/3125000000000 : ℝ)^6179
        have hw : |(-2197461647/10000000000 : ℝ)|=(2197461647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_11 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2254944523/5000000000 : ℝ)*x 0 + (431727457/1000000000 : ℝ)*x 1 + (4317275301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254944523/5000000000 : ℝ)^8227 ≤ (17318520537981/50000000000000 : ℝ)^6179 := by
    have hnat : (2254944523 : ℕ)^8227*50000000000000^6179 ≤ 17318520537981^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254944523 5000000000 17318520537981 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431727457/1000000000 : ℝ)^8227 ≤ (32681475771253/100000000000000 : ℝ)^6179 := by
    have hnat : (431727457 : ℕ)^8227*100000000000000^6179 ≤ 32681475771253^6179*1000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431727457 1000000000 32681475771253 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317275301/10000000000 : ℝ)^8227 ≤ (6536296627793/20000000000000 : ℝ)^6179 := by
    have hnat : (4317275301 : ℕ)^8227*20000000000000^6179 ≤ 6536296627793^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317275301 10000000000 6536296627793 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254944523/5000000000 : ℝ), (431727457/1000000000 : ℝ), (4317275301/10000000000 : ℝ)] ![(17318520537981/50000000000000 : ℝ), (32681475771253/100000000000000 : ℝ), (6536296627793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254944523/5000000000 : ℝ)|^8227 ≤ (17318520537981/50000000000000 : ℝ)^6179
        have hw : |(2254944523/5000000000 : ℝ)|=(2254944523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431727457/1000000000 : ℝ)|^8227 ≤ (32681475771253/100000000000000 : ℝ)^6179
        have hw : |(431727457/1000000000 : ℝ)|=(431727457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317275301/10000000000 : ℝ)|^8227 ≤ (6536296627793/20000000000000 : ℝ)^6179
        have hw : |(4317275301/10000000000 : ℝ)|=(4317275301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_12 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144204491/10000000000 : ℝ)*x 0 + (2721502461/5000000000 : ℝ)*x 1 + (1054322829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144204491/10000000000 : ℝ)^8227 ≤ (3217789205837/25000000000000 : ℝ)^6179 := by
    have hnat : (2144204491 : ℕ)^8227*25000000000000^6179 ≤ 3217789205837^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144204491 10000000000 3217789205837 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721502461/5000000000 : ℝ)^8227 ≤ (11123046302761/25000000000000 : ℝ)^6179 := by
    have hnat : (2721502461 : ℕ)^8227*25000000000000^6179 ≤ 11123046302761^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721502461 5000000000 11123046302761 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054322829/2000000000 : ℝ)^8227 ≤ (10659164488179/25000000000000 : ℝ)^6179 := by
    have hnat : (1054322829 : ℕ)^8227*25000000000000^6179 ≤ 10659164488179^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054322829 2000000000 10659164488179 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144204491/10000000000 : ℝ), (2721502461/5000000000 : ℝ), (1054322829/2000000000 : ℝ)] ![(3217789205837/25000000000000 : ℝ), (11123046302761/25000000000000 : ℝ), (10659164488179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144204491/10000000000 : ℝ)|^8227 ≤ (3217789205837/25000000000000 : ℝ)^6179
        have hw : |(-2144204491/10000000000 : ℝ)|=(2144204491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721502461/5000000000 : ℝ)|^8227 ≤ (11123046302761/25000000000000 : ℝ)^6179
        have hw : |(2721502461/5000000000 : ℝ)|=(2721502461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054322829/2000000000 : ℝ)|^8227 ≤ (10659164488179/25000000000000 : ℝ)^6179
        have hw : |(1054322829/2000000000 : ℝ)|=(1054322829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_13 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370027563/10000000000 : ℝ)*x 0 + (-560654489/2500000000 : ℝ)*x 1 + (1054322841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370027563/10000000000 : ℝ)^8227 ≤ (21849853344531/50000000000000 : ℝ)^6179 := by
    have hnat : (5370027563 : ℕ)^8227*50000000000000^6179 ≤ 21849853344531^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370027563 10000000000 21849853344531 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560654489/2500000000 : ℝ)^8227 ≤ (3415908675107/25000000000000 : ℝ)^6179 := by
    have hnat : (560654489 : ℕ)^8227*25000000000000^6179 ≤ 3415908675107^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560654489 2500000000 3415908675107 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054322841/2000000000 : ℝ)^8227 ≤ (42636658598837/100000000000000 : ℝ)^6179 := by
    have hnat : (1054322841 : ℕ)^8227*100000000000000^6179 ≤ 42636658598837^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054322841 2000000000 42636658598837 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370027563/10000000000 : ℝ), (-560654489/2500000000 : ℝ), (1054322841/2000000000 : ℝ)] ![(21849853344531/50000000000000 : ℝ), (3415908675107/25000000000000 : ℝ), (42636658598837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370027563/10000000000 : ℝ)|^8227 ≤ (21849853344531/50000000000000 : ℝ)^6179
        have hw : |(5370027563/10000000000 : ℝ)|=(5370027563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560654489/2500000000 : ℝ)|^8227 ≤ (3415908675107/25000000000000 : ℝ)^6179
        have hw : |(-560654489/2500000000 : ℝ)|=(560654489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054322841/2000000000 : ℝ)|^8227 ≤ (42636658598837/100000000000000 : ℝ)^6179
        have hw : |(1054322841/2000000000 : ℝ)|=(1054322841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_14 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342506903/2500000000 : ℝ)*x 0 + (1317903549/2500000000 : ℝ)*x 1 + (-2242617903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342506903/2500000000 : ℝ)^8227 ≤ (10924926804993/25000000000000 : ℝ)^6179 := by
    have hnat : (1342506903 : ℕ)^8227*25000000000000^6179 ≤ 10924926804993^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342506903 2500000000 10924926804993 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317903549/2500000000 : ℝ)^8227 ≤ (42636658501919/100000000000000 : ℝ)^6179 := by
    have hnat : (1317903549 : ℕ)^8227*100000000000000^6179 ≤ 42636658501919^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317903549 2500000000 42636658501919 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242617903/10000000000 : ℝ)^8227 ≤ (6831817135243/50000000000000 : ℝ)^6179 := by
    have hnat : (2242617903 : ℕ)^8227*50000000000000^6179 ≤ 6831817135243^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242617903 10000000000 6831817135243 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342506903/2500000000 : ℝ), (1317903549/2500000000 : ℝ), (-2242617903/10000000000 : ℝ)] ![(10924926804993/25000000000000 : ℝ), (42636658501919/100000000000000 : ℝ), (6831817135243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342506903/2500000000 : ℝ)|^8227 ≤ (10924926804993/25000000000000 : ℝ)^6179
        have hw : |(1342506903/2500000000 : ℝ)|=(1342506903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1317903549/2500000000 : ℝ)|^8227 ≤ (42636658501919/100000000000000 : ℝ)^6179
        have hw : |(1317903549/2500000000 : ℝ)|=(1317903549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242617903/10000000000 : ℝ)|^8227 ≤ (6831817135243/50000000000000 : ℝ)^6179
        have hw : |(-2242617903/10000000000 : ℝ)|=(2242617903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_box_15 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2126550863/5000000000 : ℝ)*x 0 + (4445665767/10000000000 : ℝ)*x 1 + (4445665801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126550863/5000000000 : ℝ)^8227 ≤ (4004534933331/12500000000000 : ℝ)^6179 := by
    have hnat : (2126550863 : ℕ)^8227*12500000000000^6179 ≤ 4004534933331^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126550863 5000000000 4004534933331 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4445665767/10000000000 : ℝ)^8227 ≤ (33981860087289/100000000000000 : ℝ)^6179 := by
    have hnat : (4445665767 : ℕ)^8227*100000000000000^6179 ≤ 33981860087289^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445665767 10000000000 33981860087289 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4445665801/10000000000 : ℝ)^8227 ≤ (16990930216659/50000000000000 : ℝ)^6179 := by
    have hnat : (4445665801 : ℕ)^8227*50000000000000^6179 ≤ 16990930216659^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445665801 10000000000 16990930216659 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126550863/5000000000 : ℝ), (4445665767/10000000000 : ℝ), (4445665801/10000000000 : ℝ)] ![(4004534933331/12500000000000 : ℝ), (33981860087289/100000000000000 : ℝ), (16990930216659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126550863/5000000000 : ℝ)|^8227 ≤ (4004534933331/12500000000000 : ℝ)^6179
        have hw : |(2126550863/5000000000 : ℝ)|=(2126550863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4445665767/10000000000 : ℝ)|^8227 ≤ (33981860087289/100000000000000 : ℝ)^6179
        have hw : |(4445665767/10000000000 : ℝ)|=(4445665767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4445665801/10000000000 : ℝ)|^8227 ≤ (16990930216659/50000000000000 : ℝ)^6179
        have hw : |(4445665801/10000000000 : ℝ)|=(4445665801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1034_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59217/100000 : ℝ) ∧ (79471/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82879/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11207/100000 : ℝ) ^ (4113/1024 : ℝ) ≤ (15211692095291407/100000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^4113 ≤ (15211692095291407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11207 : ℕ)^4113*100000000000000000000^1024 ≤ 15211692095291407^1024*100000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 15211692095291407 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (15211692095291407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6991/50000 : ℝ) ^ (4113/1024 : ℝ) ≤ (36990679270844317/100000000000000000000 : ℝ) := by
    have hpowers : (6991/50000 : ℝ)^4113 ≤ (36990679270844317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6991 : ℕ)^4113*100000000000000000000^1024 ≤ 36990679270844317^1024*50000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6991 50000 36990679270844317 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6991/50000 : ℝ)) (X := (36990679270844317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015211692095291407/50000000000000000000 : ℝ) ≤ (10000757354410653/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50015211692095291407/50000000000000000000 : ℝ)^1024 ≤ (10000757354410653/10000000000000000 : ℝ)^4113 := by
      have hnat : (50015211692095291407 : ℕ)^1024*10000000000000000^4113 ≤ 10000757354410653^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015211692095291407 50000000000000000000 10000757354410653 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757354410653/10000000000000000 : ℝ)) (X := (50015211692095291407/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013050592841533931/25000000000000000000 : ℝ) ≤ (2500324852618023/2500000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (25013050592841533931/25000000000000000000 : ℝ)^1024 ≤ (2500324852618023/2500000000000000 : ℝ)^4113 := by
      have hnat : (25013050592841533931 : ℕ)^1024*2500000000000000^4113 ≤ 2500324852618023^4113*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013050592841533931 25000000000000000000 2500324852618023 2500000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500324852618023/2500000000000000 : ℝ)) (X := (25013050592841533931/25000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036990679270844317/50000000000000000000 : ℝ) ≤ (10001841466533531/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50036990679270844317/50000000000000000000 : ℝ)^1024 ≤ (10001841466533531/10000000000000000 : ℝ)^4113 := by
      have hnat : (50036990679270844317 : ℕ)^1024*10000000000000000^4113 ≤ 10001841466533531^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036990679270844317 50000000000000000000 10001841466533531 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001841466533531/10000000000000000 : ℝ)) (X := (50036990679270844317/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15211692095291407/100000000000000000000 : ℝ) ≤ ((9246650671309489443/9250000000000000000 : ℝ)+2*(180685353813/92500000000000 : ℝ)*(11207/100000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (9246650671309489443/9250000000000000000 : ℝ)+2*(180685353813/92500000000000 : ℝ)*(11207/100000 : ℝ)=(10000757354410653/10000000000000000 : ℝ) by norm_num, show 1+2*(15211692095291407/100000000000000000000 : ℝ)=(50015211692095291407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36990679270844317/100000000000000000000 : ℝ)+(15211692095291407/100000000000000000000 : ℝ) ≤ ((9246650671309489443/9250000000000000000 : ℝ)+(180685353813/92500000000000 : ℝ)*((6991/50000 : ℝ)+(11207/100000 : ℝ)))^(4113/1024 : ℝ) := by
    rw [show (9246650671309489443/9250000000000000000 : ℝ)+(180685353813/92500000000000 : ℝ)*((6991/50000 : ℝ)+(11207/100000 : ℝ))=(2500324852618023/2500000000000000 : ℝ) by norm_num, show 1+(36990679270844317/100000000000000000000 : ℝ)+(15211692095291407/100000000000000000000 : ℝ)=(25013050592841533931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36990679270844317/100000000000000000000 : ℝ) ≤ ((9246650671309489443/9250000000000000000 : ℝ)+2*(180685353813/92500000000000 : ℝ)*(6991/50000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (9246650671309489443/9250000000000000000 : ℝ)+2*(180685353813/92500000000000 : ℝ)*(6991/50000 : ℝ)=(10001841466533531/10000000000000000 : ℝ) by norm_num, show 1+2*(36990679270844317/100000000000000000000 : ℝ)=(50036990679270844317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9246650671309489443/9250000000000000000 : ℝ)*(X 1 0+X 2 0)+(180685353813/92500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (9246650671309489443/9250000000000000000 : ℝ)) (alpha := (180685353813/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9246650671309489443/9250000000000000000 : ℝ)*(X 0 1+X 2 1)+(180685353813/92500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (9246650671309489443/9250000000000000000 : ℝ)) (alpha := (180685353813/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9246650671309489443/9250000000000000000 : ℝ)*(X 0 2+X 1 2)+(180685353813/92500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (9246650671309489443/9250000000000000000 : ℝ)) (alpha := (180685353813/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130565393/625000000 : ℝ)*X 0 0+(2688898031/5000000000 : ℝ)*X 0 1+(16805613/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1058965599/2000000000 : ℝ)*X 1 0+(-275159323/1250000000 : ℝ)*X 1 1+(537779587/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294827827/10000000000 : ℝ)*X 2 0+(5377796103/10000000000 : ℝ)*X 2 1+(-17197457/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4488875879/10000000000 : ℝ)*X 0 0+(4327922051/10000000000 : ℝ)*X 0 1+(135247563/312500000 : ℝ)*X 0 2+(4488875879/10000000000 : ℝ)*X 1 0+(4327922051/10000000000 : ℝ)*X 1 1+(135247563/312500000 : ℝ)*X 1 2+(4488875879/10000000000 : ℝ)*X 2 0+(4327922051/10000000000 : ℝ)*X 2 1+(135247563/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235159387/1000000000 : ℝ)*X 0 0+(2639798471/5000000000 : ℝ)*X 0 1+(5279597759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268218803/500000000 : ℝ)*X 1 0+(-2239564781/10000000000 : ℝ)*X 1 1+(5279596923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072875169/2000000000 : ℝ)*X 2 0+(105591953/200000000 : ℝ)*X 2 1+(-2239564101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135520429/5000000000 : ℝ)*X 0 0+(277301077/625000000 : ℝ)*X 0 1+(277301149/625000000 : ℝ)*X 0 2+(2135520429/5000000000 : ℝ)*X 1 0+(277301077/625000000 : ℝ)*X 1 1+(277301149/625000000 : ℝ)*X 1 2+(2135520429/5000000000 : ℝ)*X 2 0+(277301077/625000000 : ℝ)*X 2 1+(277301149/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2296826141/10000000000 : ℝ)*X 0 0+(2606513631/5000000000 : ℝ)*X 0 1+(269369607/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288027979/10000000000 : ℝ)*X 1 0+(-2197461209/10000000000 : ℝ)*X 1 1+(538739201/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((661003481/1250000000 : ℝ)*X 2 0+(1077478363/2000000000 : ℝ)*X 2 1+(-2197461647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2254944523/5000000000 : ℝ)*X 0 0+(431727457/1000000000 : ℝ)*X 0 1+(4317275301/10000000000 : ℝ)*X 0 2+(2254944523/5000000000 : ℝ)*X 1 0+(431727457/1000000000 : ℝ)*X 1 1+(4317275301/10000000000 : ℝ)*X 1 2+(2254944523/5000000000 : ℝ)*X 2 0+(431727457/1000000000 : ℝ)*X 2 1+(4317275301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2144204491/10000000000 : ℝ)*X 0 0+(2721502461/5000000000 : ℝ)*X 0 1+(1054322829/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370027563/10000000000 : ℝ)*X 1 0+(-560654489/2500000000 : ℝ)*X 1 1+(1054322841/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342506903/2500000000 : ℝ)*X 2 0+(1317903549/2500000000 : ℝ)*X 2 1+(-2242617903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2126550863/5000000000 : ℝ)*X 0 0+(4445665767/10000000000 : ℝ)*X 0 1+(4445665801/10000000000 : ℝ)*X 0 2+(2126550863/5000000000 : ℝ)*X 1 0+(4445665767/10000000000 : ℝ)*X 1 1+(4445665801/10000000000 : ℝ)*X 1 2+(2126550863/5000000000 : ℝ)*X 2 0+(4445665767/10000000000 : ℝ)*X 2 1+(4445665801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-143885502959763794644106824016817/231250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14347929/12500000000000 : ℝ)*(lower3) + (1021787/25000000000000 : ℝ)*(lower4) + (368891/78125000000 : ℝ)*(upper5) + (1914713995552727/50000000000000 : ℝ)*(major0) + (1914713995552727/50000000000000 : ℝ)*(major1) + (1914713995552727/50000000000000 : ℝ)*(major2) + (1566769807/5000000000000 : ℝ)*(sp1) + (8107715983/50000000000000 : ℝ)*(sp2) + (3464214859/20000000000000 : ℝ)*(sp3) + (1270274270575269/25000000000000 : ℝ)*(sp4) + (1270267152640301/25000000000000 : ℝ)*(sp5) + (2540541865262689/50000000000000 : ℝ)*(sp6) + (51969579357163/2000000000000 : ℝ)*(sp7) + (715914067/25000000000000 : ℝ)*(sp12) + (519699257786489/20000000000000 : ℝ)*(f.failure) + (158784373311167/3125000000000 : ℝ)*(f.sum) + (16872194747477/4625000000000000000000000000 : ℝ)*base65 + (4392884688248961061/462500000000000000000000000000000 : ℝ)*base67 + (2788226702338538939/462500000000000000000000000000000 : ℝ)*base70 + (941200892301038939/462500000000000000000000000000000 : ℝ)*base72 + (14719079351477/4625000000000000000000000000 : ℝ)*base73 + (1043638568288538939/462500000000000000000000000000000 : ℝ)*base76 + (3214618140101038939/462500000000000000000000000000000 : ℝ)*base78 + (65027289873961061/462500000000000000000000000000000 : ℝ)*base79 + (458929326147/289062500000000000000000000 : ℝ)*base81 + (338541/500000000000000000000 : ℝ)*base90 + (338541/500000000000000000000 : ℝ)*base92 + (338541/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59217/100000 : ℝ) ≤ (68472660127230345150766358555163/115625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17200187/50000000000000 : ℝ)*(lower0) + (27913737/100000000000000 : ℝ)*(lower1) + (12777531/50000000000000 : ℝ)*(lower3) + (3149383/10000000000000 : ℝ)*(lower5) + (972950367330347/25000000000000 : ℝ)*(major0) + (972950367330347/25000000000000 : ℝ)*(major1) + (972950367330347/25000000000000 : ℝ)*(major2) + (5123039866975797/100000000000000 : ℝ)*(sp0) + (5122916073364443/100000000000000 : ℝ)*(sp1) + (5123042642355043/100000000000000 : ℝ)*(sp2) + (82525588079869/3125000000000 : ℝ)*(sp3) + (805874641/50000000000000 : ℝ)*(sp7) + (126568990601/100000000000000 : ℝ)*(sp9) + (2775379247/100000000000000 : ℝ)*(sp12) + (264082043030509/10000000000000 : ℝ)*(f.failure) + (5123042642355043/100000000000000 : ℝ)*(f.sum) + (14023552393069/4625000000000000000000000000 : ℝ)*base65 + (10127103535073873279/231250000000000000000000000000000 : ℝ)*base68 + (121827800867623279/231250000000000000000000000000000 : ℝ)*base70 + (1083589336098873279/231250000000000000000000000000000 : ℝ)*base72 + (122246554685931/4625000000000000000000000000 : ℝ)*base74 + (336380179476126721/231250000000000000000000000000000 : ℝ)*base75 + (770995334594876721/231250000000000000000000000000000 : ℝ)*base77 + (6934519750055123279/231250000000000000000000000000000 : ℝ)*base80 + (5449217869889/1156250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2119921/250000000000000000000 : ℝ)*base90 + (2119921/250000000000000000000 : ℝ)*base92 + (2119921/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79471/100000 : ℝ) ≤ (1837821685605236865331524597/2312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (302896061/100000000000000 : ℝ)*(upper0) + (5251271/25000000000000 : ℝ)*(lower1) + (29073069/25000000000000 : ℝ)*(upper2) + (153649791/100000000000000 : ℝ)*(lower3) + (489393637/100000000000000 : ℝ)*(lower5) + (4360058638183807/100000000000000 : ℝ)*(major0) + (4360058638183807/100000000000000 : ℝ)*(major1) + (4360058638183807/100000000000000 : ℝ)*(major2) + (60533567369/100000000000000 : ℝ)*(sp1) + (17930266359/100000000000000 : ℝ)*(sp3) + (229402607329949/4000000000000 : ℝ)*(sp8) + (1433751162420339/25000000000000 : ℝ)*(sp9) + (229402607329949/4000000000000 : ℝ)*(sp10) + (2958543039456411/100000000000000 : ℝ)*(sp11) + (295856096972277/10000000000000 : ℝ)*(f.failure) + (229402607329949/4000000000000 : ℝ)*(f.sum) + (14884503313159/4625000000000000000000000000 : ℝ)*base66 + (139293408244149501/925000000000000000000000000000000 : ℝ)*base67 + (5340573564194149501/925000000000000000000000000000000 : ℝ)*base69 + (3152773837480850499/925000000000000000000000000000000 : ℝ)*base72 + (18940466989821/1156250000000000000000000000 : ℝ)*base74 + (2989338269055850499/925000000000000000000000000000000 : ℝ)*base76 + (2075197475594149501/925000000000000000000000000000000 : ℝ)*base77 + (6356468147380850499/925000000000000000000000000000000 : ℝ)*base80 + (13260231701409/4625000000000000000000000000 : ℝ)*base82 + (1531513/250000000000000000000 : ℝ)*base90 + (1531513/250000000000000000000 : ℝ)*base92 + (1531513/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82879/100000 : ℝ) ≤ (-191652048355419296126798790490431/231250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9290719/100000000000000 : ℝ)*(lower0) + (1678571/10000000000000 : ℝ)*(lower1) + (7147409/25000000000000 : ℝ)*(lower2) + (6714029/20000000000000 : ℝ)*(upper5) + (2197221905563561/50000000000000 : ℝ)*(major0) + (2197221905563561/50000000000000 : ℝ)*(major1) + (2197221905563561/50000000000000 : ℝ)*(major2) + (735908557/50000000000000 : ℝ)*(sp0) + (28740196743/100000000000000 : ℝ)*(sp7) + (224045909/100000000000000 : ℝ)*(sp8) + (5834618077510429/100000000000000 : ℝ)*(sp12) + (1458654943343363/25000000000000 : ℝ)*(sp13) + (1458654943343363/25000000000000 : ℝ)*(sp14) + (1490932314583853/50000000000000 : ℝ)*(sp15) + (2981893369364449/100000000000000 : ℝ)*(f.failure) + (1458654943343363/25000000000000 : ℝ)*(f.sum) + (4588624138133/578125000000000000000000000 : ℝ)*base66 + (3100383717520713477/462500000000000000000000000000000 : ℝ)*base68 + (1930026487483213477/462500000000000000000000000000000 : ℝ)*base70 + (669435336129286523/462500000000000000000000000000000 : ℝ)*base71 + (5753964750391/1156250000000000000000000000 : ℝ)*base74 + (1125049658329286523/462500000000000000000000000000000 : ℝ)*base75 + (3444640519820713477/462500000000000000000000000000000 : ℝ)*base78 + (2457239000470713477/462500000000000000000000000000000 : ℝ)*base80 + (1082776276109/1156250000000000000000000000 : ℝ)*base81 + (14529781/2500000000000000000000 : ℝ)*base90 + (14529781/2500000000000000000000 : ℝ)*base92 + (14529781/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1034_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59217/100000 : ℝ) else (79471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82879/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1034_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1034_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59217/100000 : ℝ) else (79471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82879/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1034_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1034_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59217/100000 : ℝ) else (79471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82879/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1034_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

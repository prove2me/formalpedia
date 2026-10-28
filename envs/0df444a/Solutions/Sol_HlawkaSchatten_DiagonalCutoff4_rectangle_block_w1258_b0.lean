-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:56.684201+00:00
-- url     : https://prove2.me/submissions/d2018ec6-e202-4d64-867c-dd3e46c5b1ba

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
theorem support_rectangle_w1258_s0_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-927816597/5000000000 : ℝ)*x 0 + (301395323/500000000 : ℝ)*x 1 + (4794965477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927816597/5000000000 : ℝ)^8451 ≤ (10827278051967/100000000000000 : ℝ)^6403 := by
    have hnat : (927816597 : ℕ)^8451*100000000000000^6403 ≤ 10827278051967^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927816597 5000000000 10827278051967 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301395323/500000000 : ℝ)^8451 ≤ (51268751944637/100000000000000 : ℝ)^6403 := by
    have hnat : (301395323 : ℕ)^8451*100000000000000^6403 ≤ 51268751944637^6403*500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301395323 500000000 51268751944637 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794965477/10000000000 : ℝ)^8451 ≤ (18951984993703/50000000000000 : ℝ)^6403 := by
    have hnat : (4794965477 : ℕ)^8451*50000000000000^6403 ≤ 18951984993703^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794965477 10000000000 18951984993703 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927816597/5000000000 : ℝ), (301395323/500000000 : ℝ), (4794965477/10000000000 : ℝ)] ![(10827278051967/100000000000000 : ℝ), (51268751944637/100000000000000 : ℝ), (18951984993703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927816597/5000000000 : ℝ)|^8451 ≤ (10827278051967/100000000000000 : ℝ)^6403
        have hw : |(-927816597/5000000000 : ℝ)|=(927816597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301395323/500000000 : ℝ)|^8451 ≤ (51268751944637/100000000000000 : ℝ)^6403
        have hw : |(301395323/500000000 : ℝ)|=(301395323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794965477/10000000000 : ℝ)|^8451 ≤ (18951984993703/50000000000000 : ℝ)^6403
        have hw : |(4794965477/10000000000 : ℝ)|=(4794965477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510258039/10000000000 : ℝ)*x 0 + (-1280023929/5000000000 : ℝ)*x 1 + (2397482723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510258039/10000000000 : ℝ)^8451 ≤ (5692404792921/12500000000000 : ℝ)^6403 := by
    have hnat : (5510258039 : ℕ)^8451*12500000000000^6403 ≤ 5692404792921^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510258039 10000000000 5692404792921 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280023929/5000000000 : ℝ)^8451 ≤ (16556791978841/100000000000000 : ℝ)^6403 := by
    have hnat : (1280023929 : ℕ)^8451*100000000000000^6403 ≤ 16556791978841^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280023929 5000000000 16556791978841 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397482723/5000000000 : ℝ)^8451 ≤ (9475992415993/25000000000000 : ℝ)^6403 := by
    have hnat : (2397482723 : ℕ)^8451*25000000000000^6403 ≤ 9475992415993^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397482723 5000000000 9475992415993 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510258039/10000000000 : ℝ), (-1280023929/5000000000 : ℝ), (2397482723/5000000000 : ℝ)] ![(5692404792921/12500000000000 : ℝ), (16556791978841/100000000000000 : ℝ), (9475992415993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510258039/10000000000 : ℝ)|^8451 ≤ (5692404792921/12500000000000 : ℝ)^6403
        have hw : |(5510258039/10000000000 : ℝ)|=(5510258039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1280023929/5000000000 : ℝ)|^8451 ≤ (16556791978841/100000000000000 : ℝ)^6403
        have hw : |(-1280023929/5000000000 : ℝ)|=(1280023929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397482723/5000000000 : ℝ)|^8451 ≤ (9475992415993/25000000000000 : ℝ)^6403
        have hw : |(2397482723/5000000000 : ℝ)|=(2397482723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510258077/10000000000 : ℝ)*x 0 + (4794965449/10000000000 : ℝ)*x 1 + (-512009561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510258077/10000000000 : ℝ)^8451 ≤ (22769619378933/50000000000000 : ℝ)^6403 := by
    have hnat : (5510258077 : ℕ)^8451*50000000000000^6403 ≤ 22769619378933^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510258077 10000000000 22769619378933 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794965449/10000000000 : ℝ)^8451 ≤ (4737996211909/12500000000000 : ℝ)^6403 := by
    have hnat : (4794965449 : ℕ)^8451*12500000000000^6403 ≤ 4737996211909^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794965449 10000000000 4737996211909 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512009561/2000000000 : ℝ)^8451 ≤ (3311358305287/20000000000000 : ℝ)^6403 := by
    have hnat : (512009561 : ℕ)^8451*20000000000000^6403 ≤ 3311358305287^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512009561 2000000000 3311358305287 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510258077/10000000000 : ℝ), (4794965449/10000000000 : ℝ), (-512009561/2000000000 : ℝ)] ![(22769619378933/50000000000000 : ℝ), (4737996211909/12500000000000 : ℝ), (3311358305287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510258077/10000000000 : ℝ)|^8451 ≤ (22769619378933/50000000000000 : ℝ)^6403
        have hw : |(5510258077/10000000000 : ℝ)|=(5510258077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794965449/10000000000 : ℝ)|^8451 ≤ (4737996211909/12500000000000 : ℝ)^6403
        have hw : |(4794965449/10000000000 : ℝ)|=(4794965449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512009561/2000000000 : ℝ)|^8451 ≤ (3311358305287/20000000000000 : ℝ)^6403
        have hw : |(-512009561/2000000000 : ℝ)|=(512009561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2095883893/5000000000 : ℝ)*x 0 + (3116301429/10000000000 : ℝ)*x 1 + (2812569117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095883893/5000000000 : ℝ)^8451 ≤ (15870512190811/50000000000000 : ℝ)^6403 := by
    have hnat : (2095883893 : ℕ)^8451*50000000000000^6403 ≤ 15870512190811^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095883893 5000000000 15870512190811 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116301429/10000000000 : ℝ)^8451 ≤ (268281062193/1250000000000 : ℝ)^6403 := by
    have hnat : (3116301429 : ℕ)^8451*1250000000000^6403 ≤ 268281062193^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116301429 10000000000 268281062193 1250000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812569117/5000000000 : ℝ)^8451 ≤ (46796490637311/100000000000000 : ℝ)^6403 := by
    have hnat : (2812569117 : ℕ)^8451*100000000000000^6403 ≤ 46796490637311^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812569117 5000000000 46796490637311 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095883893/5000000000 : ℝ), (3116301429/10000000000 : ℝ), (2812569117/5000000000 : ℝ)] ![(15870512190811/50000000000000 : ℝ), (268281062193/1250000000000 : ℝ), (46796490637311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095883893/5000000000 : ℝ)|^8451 ≤ (15870512190811/50000000000000 : ℝ)^6403
        have hw : |(2095883893/5000000000 : ℝ)|=(2095883893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116301429/10000000000 : ℝ)|^8451 ≤ (268281062193/1250000000000 : ℝ)^6403
        have hw : |(3116301429/10000000000 : ℝ)|=(3116301429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812569117/5000000000 : ℝ)|^8451 ≤ (46796490637311/100000000000000 : ℝ)^6403
        have hw : |(2812569117/5000000000 : ℝ)|=(2812569117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-930222667/5000000000 : ℝ)*x 0 + (2413352879/5000000000 : ℝ)*x 1 + (749380481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930222667/5000000000 : ℝ)^8451 ≤ (2716088024431/25000000000000 : ℝ)^6403 := by
    have hnat : (930222667 : ℕ)^8451*25000000000000^6403 ≤ 2716088024431^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930222667 5000000000 2716088024431 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2413352879/5000000000 : ℝ)^8451 ≤ (19117738761929/50000000000000 : ℝ)^6403 := by
    have hnat : (2413352879 : ℕ)^8451*50000000000000^6403 ≤ 19117738761929^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413352879 5000000000 19117738761929 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749380481/1250000000 : ℝ)^8451 ≤ (50900170356603/100000000000000 : ℝ)^6403 := by
    have hnat : (749380481 : ℕ)^8451*100000000000000^6403 ≤ 50900170356603^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749380481 1250000000 50900170356603 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930222667/5000000000 : ℝ), (2413352879/5000000000 : ℝ), (749380481/1250000000 : ℝ)] ![(2716088024431/25000000000000 : ℝ), (19117738761929/50000000000000 : ℝ), (50900170356603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930222667/5000000000 : ℝ)|^8451 ≤ (2716088024431/25000000000000 : ℝ)^6403
        have hw : |(-930222667/5000000000 : ℝ)|=(930222667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2413352879/5000000000 : ℝ)|^8451 ≤ (19117738761929/50000000000000 : ℝ)^6403
        have hw : |(2413352879/5000000000 : ℝ)|=(2413352879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(749380481/1250000000 : ℝ)|^8451 ≤ (50900170356603/100000000000000 : ℝ)^6403
        have hw : |(749380481/1250000000 : ℝ)|=(749380481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517472571/1000000000 : ℝ)*x 0 + (-1359967061/10000000000 : ℝ)*x 1 + (1498761561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517472571/1000000000 : ℝ)^8451 ≤ (41915454388701/100000000000000 : ℝ)^6403 := by
    have hnat : (517472571 : ℕ)^8451*100000000000000^6403 ≤ 41915454388701^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517472571 1000000000 41915454388701 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359967061/10000000000 : ℝ)^8451 ≤ (1436869677561/20000000000000 : ℝ)^6403 := by
    have hnat : (1359967061 : ℕ)^8451*20000000000000^6403 ≤ 1436869677561^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359967061 10000000000 1436869677561 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498761561/2500000000 : ℝ)^8451 ≤ (25450098603117/50000000000000 : ℝ)^6403 := by
    have hnat : (1498761561 : ℕ)^8451*50000000000000^6403 ≤ 25450098603117^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498761561 2500000000 25450098603117 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517472571/1000000000 : ℝ), (-1359967061/10000000000 : ℝ), (1498761561/2500000000 : ℝ)] ![(41915454388701/100000000000000 : ℝ), (1436869677561/20000000000000 : ℝ), (25450098603117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517472571/1000000000 : ℝ)|^8451 ≤ (41915454388701/100000000000000 : ℝ)^6403
        have hw : |(517472571/1000000000 : ℝ)|=(517472571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1359967061/10000000000 : ℝ)|^8451 ≤ (1436869677561/20000000000000 : ℝ)^6403
        have hw : |(-1359967061/10000000000 : ℝ)|=(1359967061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498761561/2500000000 : ℝ)|^8451 ≤ (25450098603117/50000000000000 : ℝ)^6403
        have hw : |(1498761561/2500000000 : ℝ)|=(1498761561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174726743/10000000000 : ℝ)*x 0 + (5995044269/10000000000 : ℝ)*x 1 + (-339992163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174726743/10000000000 : ℝ)^8451 ≤ (41915465432329/100000000000000 : ℝ)^6403 := by
    have hnat : (5174726743 : ℕ)^8451*100000000000000^6403 ≤ 41915465432329^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174726743 10000000000 41915465432329 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5995044269/10000000000 : ℝ)^8451 ≤ (50900175074339/100000000000000 : ℝ)^6403 := by
    have hnat : (5995044269 : ℕ)^8451*100000000000000^6403 ≤ 50900175074339^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995044269 10000000000 50900175074339 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339992163/2500000000 : ℝ)^8451 ≤ (7184359480929/100000000000000 : ℝ)^6403 := by
    have hnat : (339992163 : ℕ)^8451*100000000000000^6403 ≤ 7184359480929^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339992163 2500000000 7184359480929 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174726743/10000000000 : ℝ), (5995044269/10000000000 : ℝ), (-339992163/2500000000 : ℝ)] ![(41915465432329/100000000000000 : ℝ), (50900175074339/100000000000000 : ℝ), (7184359480929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174726743/10000000000 : ℝ)|^8451 ≤ (41915465432329/100000000000000 : ℝ)^6403
        have hw : |(5174726743/10000000000 : ℝ)|=(5174726743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5995044269/10000000000 : ℝ)|^8451 ≤ (50900175074339/100000000000000 : ℝ)^6403
        have hw : |(5995044269/10000000000 : ℝ)|=(5995044269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339992163/2500000000 : ℝ)|^8451 ≤ (7184359480929/100000000000000 : ℝ)^6403
        have hw : |(-339992163/2500000000 : ℝ)|=(339992163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s0_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4201561921/10000000000 : ℝ)*x 0 + (2780278823/5000000000 : ℝ)*x 1 + (3183165551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201561921/10000000000 : ℝ)^8451 ≤ (31838945547193/100000000000000 : ℝ)^6403 := by
    have hnat : (4201561921 : ℕ)^8451*100000000000000^6403 ≤ 31838945547193^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201561921 10000000000 31838945547193 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2780278823/5000000000 : ℝ)^8451 ≤ (1843547891947/4000000000000 : ℝ)^6403 := by
    have hnat : (2780278823 : ℕ)^8451*4000000000000^6403 ≤ 1843547891947^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780278823 5000000000 1843547891947 4000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183165551/10000000000 : ℝ)^8451 ≤ (2207235714323/10000000000000 : ℝ)^6403 := by
    have hnat : (3183165551 : ℕ)^8451*10000000000000^6403 ≤ 2207235714323^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183165551 10000000000 2207235714323 10000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201561921/10000000000 : ℝ), (2780278823/5000000000 : ℝ), (3183165551/10000000000 : ℝ)] ![(31838945547193/100000000000000 : ℝ), (1843547891947/4000000000000 : ℝ), (2207235714323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201561921/10000000000 : ℝ)|^8451 ≤ (31838945547193/100000000000000 : ℝ)^6403
        have hw : |(4201561921/10000000000 : ℝ)|=(4201561921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2780278823/5000000000 : ℝ)|^8451 ≤ (1843547891947/4000000000000 : ℝ)^6403
        have hw : |(2780278823/5000000000 : ℝ)|=(2780278823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183165551/10000000000 : ℝ)|^8451 ≤ (2207235714323/10000000000000 : ℝ)^6403
        have hw : |(3183165551/10000000000 : ℝ)|=(3183165551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (441/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1711/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4225/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4225 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4225*1^1024 ≤ 0^1024*1^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4225/1024 : ℝ) ≤ (1140456842628142321/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4225 ≤ (1140456842628142321/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4225*50000000000000000000^1024 ≤ 1140456842628142321^1024*5^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1140456842628142321 50000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1140456842628142321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4225 := by
      have hnat : (1 : ℕ)^1024*1^4225 ≤ 1^4225*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51140456842628142321/50000000000000000000 : ℝ) ≤ (5027405206505013/5000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (51140456842628142321/50000000000000000000 : ℝ)^1024 ≤ (5027405206505013/5000000000000000 : ℝ)^4225 := by
      have hnat : (51140456842628142321 : ℕ)^1024*5000000000000000^4225 ≤ 5027405206505013^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51140456842628142321 50000000000000000000 5027405206505013 5000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027405206505013/5000000000000000 : ℝ)) (X := (51140456842628142321/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26140456842628142321/25000000000000000000 : ℝ) ≤ (2527405206505013/2500000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (26140456842628142321/25000000000000000000 : ℝ)^1024 ≤ (2527405206505013/2500000000000000 : ℝ)^4225 := by
      have hnat : (26140456842628142321 : ℕ)^1024*2500000000000000^4225 ≤ 2527405206505013^4225*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26140456842628142321 25000000000000000000 2527405206505013 2500000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527405206505013/2500000000000000 : ℝ)) (X := (26140456842628142321/25000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27405206505013/2000000000000000 : ℝ)*(0 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27405206505013/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1140456842628142321/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27405206505013/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27405206505013/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027405206505013/5000000000000000 : ℝ) by norm_num, show 1+(1140456842628142321/50000000000000000000 : ℝ)+(0 : ℝ)=(51140456842628142321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1140456842628142321/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27405206505013/2000000000000000 : ℝ)*(2/5 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27405206505013/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527405206505013/2500000000000000 : ℝ) by norm_num, show 1+2*(1140456842628142321/50000000000000000000 : ℝ)=(26140456842628142321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27405206505013/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27405206505013/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27405206505013/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27405206505013/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27405206505013/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27405206505013/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-927816597/5000000000 : ℝ)*X 0 0+(301395323/500000000 : ℝ)*X 0 1+(4794965477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510258039/10000000000 : ℝ)*X 1 0+(-1280023929/5000000000 : ℝ)*X 1 1+(2397482723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510258077/10000000000 : ℝ)*X 2 0+(4794965449/10000000000 : ℝ)*X 2 1+(-512009561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095883893/5000000000 : ℝ)*X 0 0+(3116301429/10000000000 : ℝ)*X 0 1+(2812569117/5000000000 : ℝ)*X 0 2+(2095883893/5000000000 : ℝ)*X 1 0+(3116301429/10000000000 : ℝ)*X 1 1+(2812569117/5000000000 : ℝ)*X 1 2+(2095883893/5000000000 : ℝ)*X 2 0+(3116301429/10000000000 : ℝ)*X 2 1+(2812569117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-930222667/5000000000 : ℝ)*X 0 0+(2413352879/5000000000 : ℝ)*X 0 1+(749380481/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517472571/1000000000 : ℝ)*X 1 0+(-1359967061/10000000000 : ℝ)*X 1 1+(1498761561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174726743/10000000000 : ℝ)*X 2 0+(5995044269/10000000000 : ℝ)*X 2 1+(-339992163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201561921/10000000000 : ℝ)*X 0 0+(2780278823/5000000000 : ℝ)*X 0 1+(3183165551/10000000000 : ℝ)*X 0 2+(4201561921/10000000000 : ℝ)*X 1 0+(2780278823/5000000000 : ℝ)*X 1 1+(3183165551/10000000000 : ℝ)*X 1 2+(4201561921/10000000000 : ℝ)*X 2 0+(2780278823/5000000000 : ℝ)*X 2 1+(3183165551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22117005984424054219347/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27038393/100000000000000 : ℝ)*(base1) + (108761919/25000000000000 : ℝ)*(base19) + (405939003/100000000000000 : ℝ)*(base23) + (34702003/100000000000000 : ℝ)*(base24) + (100864573/100000000000000 : ℝ)*(upper3) + (151207930831309/25000000000000 : ℝ)*(major0) + (151207930831309/25000000000000 : ℝ)*(major1) + (151207930831309/25000000000000 : ℝ)*(major2) + (811070261141317/100000000000000 : ℝ)*(sp0) + (405535358248121/50000000000000 : ℝ)*(sp1) + (811070710902913/100000000000000 : ℝ)*(sp2) + (398591488025919/100000000000000 : ℝ)*(sp3) + (183488199/20000000000000 : ℝ)*(sp4) + (721063549/100000000000000 : ℝ)*(sp7) + (398592236127861/100000000000000 : ℝ)*(f.failure) + (405535575771959/50000000000000 : ℝ)*(f.sum) + (55702087477017/25000000000000000000000000000 : ℝ)*base65 + (179090519102017/50000000000000000000000000000 : ℝ)*base67 + (144190090152017/50000000000000000000000000000 : ℝ)*base69 + (270639945802017/50000000000000000000000000000 : ℝ)*base71 + (24781709127017/25000000000000000000000000000 : ℝ)*base73 + (645800492002017/50000000000000000000000000000 : ℝ)*base75 + (224275502652017/50000000000000000000000000000 : ℝ)*base77 + (153115723752017/50000000000000000000000000000 : ℝ)*base79 + (59799276352017/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (91590247/10000000000000000000000 : ℝ)*base90 + (91590247/10000000000000000000000 : ℝ)*base92 + (91590247/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108028339921788962544939/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182861083/100000000000000 : ℝ)*(base1) + (8634893/2000000000000 : ℝ)*(base19) + (551640519/100000000000000 : ℝ)*(base23) + (87068289/100000000000000 : ℝ)*(upper3) + (638273364534101/100000000000000 : ℝ)*(major0) + (638273364534101/100000000000000 : ℝ)*(major1) + (638273364534101/100000000000000 : ℝ)*(major2) + (188836121/12500000000000 : ℝ)*(sp1) + (362339689/50000000000000 : ℝ)*(sp2) + (63767623/10000000000000 : ℝ)*(sp3) + (427958056343141/50000000000000 : ℝ)*(sp4) + (427956993695791/50000000000000 : ℝ)*(sp5) + (855914653505303/100000000000000 : ℝ)*(sp6) + (42062990668679/10000000000000 : ℝ)*(sp7) + (210315363612051/50000000000000 : ℝ)*(f.failure) + (2139789824563/250000000000 : ℝ)*(f.sum) + (261120952251687/100000000000000000000000000000 : ℝ)*base66 + (153165112748313/200000000000000000000000000000 : ℝ)*base67 + (1194804816748313/200000000000000000000000000000 : ℝ)*base69 + (424074202451687/200000000000000000000000000000 : ℝ)*base72 + (120298530451687/100000000000000000000000000000 : ℝ)*base74 + (521520103251687/200000000000000000000000000000 : ℝ)*base76 + (508607655051687/200000000000000000000000000000 : ℝ)*base78 + (336246381851687/200000000000000000000000000000 : ℝ)*base80 + (299841039548313/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (24683377/5000000000000000000000 : ℝ)*base90 + (24683377/5000000000000000000000 : ℝ)*base92 + (24683377/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1258_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1711/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s1_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-410376539/2000000000 : ℝ)*x 0 + (1417899887/2500000000 : ℝ)*x 1 + (5025649993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410376539/2000000000 : ℝ)^8451 ≤ (12363586360509/100000000000000 : ℝ)^6403 := by
    have hnat : (410376539 : ℕ)^8451*100000000000000^6403 ≤ 12363586360509^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410376539 2000000000 12363586360509 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417899887/2500000000 : ℝ)^8451 ≤ (23653655612619/50000000000000 : ℝ)^6403 := by
    have hnat : (1417899887 : ℕ)^8451*50000000000000^6403 ≤ 23653655612619^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417899887 2500000000 23653655612619 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025649993/10000000000 : ℝ)^8451 ≤ (2016455119533/5000000000000 : ℝ)^6403 := by
    have hnat : (5025649993 : ℕ)^8451*5000000000000^6403 ≤ 2016455119533^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025649993 10000000000 2016455119533 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410376539/2000000000 : ℝ), (1417899887/2500000000 : ℝ), (5025649993/10000000000 : ℝ)] ![(12363586360509/100000000000000 : ℝ), (23653655612619/50000000000000 : ℝ), (2016455119533/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410376539/2000000000 : ℝ)|^8451 ≤ (12363586360509/100000000000000 : ℝ)^6403
        have hw : |(-410376539/2000000000 : ℝ)|=(410376539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417899887/2500000000 : ℝ)|^8451 ≤ (23653655612619/50000000000000 : ℝ)^6403
        have hw : |(1417899887/2500000000 : ℝ)|=(1417899887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025649993/10000000000 : ℝ)|^8451 ≤ (2016455119533/5000000000000 : ℝ)^6403
        have hw : |(5025649993/10000000000 : ℝ)|=(5025649993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706393993/5000000000 : ℝ)*x 0 + (-299810679/1250000000 : ℝ)*x 1 + (5025650227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706393993/5000000000 : ℝ)^8451 ≤ (44479071204937/100000000000000 : ℝ)^6403 := by
    have hnat : (2706393993 : ℕ)^8451*100000000000000^6403 ≤ 44479071204937^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706393993 5000000000 44479071204937 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299810679/1250000000 : ℝ)^8451 ≤ (3797955979461/25000000000000 : ℝ)^6403 := by
    have hnat : (299810679 : ℕ)^8451*25000000000000^6403 ≤ 3797955979461^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299810679 1250000000 3797955979461 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025650227/10000000000 : ℝ)^8451 ≤ (40329104869033/100000000000000 : ℝ)^6403 := by
    have hnat : (5025650227 : ℕ)^8451*100000000000000^6403 ≤ 40329104869033^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025650227 10000000000 40329104869033 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706393993/5000000000 : ℝ), (-299810679/1250000000 : ℝ), (5025650227/10000000000 : ℝ)] ![(44479071204937/100000000000000 : ℝ), (3797955979461/25000000000000 : ℝ), (40329104869033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706393993/5000000000 : ℝ)|^8451 ≤ (44479071204937/100000000000000 : ℝ)^6403
        have hw : |(2706393993/5000000000 : ℝ)|=(2706393993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299810679/1250000000 : ℝ)|^8451 ≤ (3797955979461/25000000000000 : ℝ)^6403
        have hw : |(-299810679/1250000000 : ℝ)|=(299810679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025650227/10000000000 : ℝ)|^8451 ≤ (40329104869033/100000000000000 : ℝ)^6403
        have hw : |(5025650227/10000000000 : ℝ)|=(5025650227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27063941/50000000 : ℝ)*x 0 + (1005130017/2000000000 : ℝ)*x 1 + (-1199242667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27063941/50000000 : ℝ)^8451 ≤ (22239536762963/50000000000000 : ℝ)^6403 := by
    have hnat : (27063941 : ℕ)^8451*50000000000000^6403 ≤ 22239536762963^6403*50000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27063941 50000000 22239536762963 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005130017/2000000000 : ℝ)^8451 ≤ (40329103365063/100000000000000 : ℝ)^6403 := by
    have hnat : (1005130017 : ℕ)^8451*100000000000000^6403 ≤ 40329103365063^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005130017 2000000000 40329103365063 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199242667/5000000000 : ℝ)^8451 ≤ (759591154929/5000000000000 : ℝ)^6403 := by
    have hnat : (1199242667 : ℕ)^8451*5000000000000^6403 ≤ 759591154929^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199242667 5000000000 759591154929 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27063941/50000000 : ℝ), (1005130017/2000000000 : ℝ), (-1199242667/5000000000 : ℝ)] ![(22239536762963/50000000000000 : ℝ), (40329103365063/100000000000000 : ℝ), (759591154929/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27063941/50000000 : ℝ)|^8451 ≤ (22239536762963/50000000000000 : ℝ)^6403
        have hw : |(27063941/50000000 : ℝ)|=(27063941/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005130017/2000000000 : ℝ)|^8451 ≤ (40329103365063/100000000000000 : ℝ)^6403
        have hw : |(1005130017/2000000000 : ℝ)|=(1005130017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199242667/5000000000 : ℝ)|^8451 ≤ (759591154929/5000000000000 : ℝ)^6403
        have hw : |(-1199242667/5000000000 : ℝ)|=(1199242667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538433299/1250000000 : ℝ)*x 0 + (924585861/2500000000 : ℝ)*x 1 + (5012747609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538433299/1250000000 : ℝ)^8451 ≤ (32902412732207/100000000000000 : ℝ)^6403 := by
    have hnat : (538433299 : ℕ)^8451*100000000000000^6403 ≤ 32902412732207^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538433299 1250000000 32902412732207 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924585861/2500000000 : ℝ)^8451 ≤ (3363135282623/12500000000000 : ℝ)^6403 := by
    have hnat : (924585861 : ℕ)^8451*12500000000000^6403 ≤ 3363135282623^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924585861 2500000000 3363135282623 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5012747609/10000000000 : ℝ)^8451 ≤ (8038500998443/20000000000000 : ℝ)^6403 := by
    have hnat : (5012747609 : ℕ)^8451*20000000000000^6403 ≤ 8038500998443^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012747609 10000000000 8038500998443 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538433299/1250000000 : ℝ), (924585861/2500000000 : ℝ), (5012747609/10000000000 : ℝ)] ![(32902412732207/100000000000000 : ℝ), (3363135282623/12500000000000 : ℝ), (8038500998443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538433299/1250000000 : ℝ)|^8451 ≤ (32902412732207/100000000000000 : ℝ)^6403
        have hw : |(538433299/1250000000 : ℝ)|=(538433299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924585861/2500000000 : ℝ)|^8451 ≤ (3363135282623/12500000000000 : ℝ)^6403
        have hw : |(924585861/2500000000 : ℝ)|=(924585861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5012747609/10000000000 : ℝ)|^8451 ≤ (8038500998443/20000000000000 : ℝ)^6403
        have hw : |(5012747609/10000000000 : ℝ)|=(5012747609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-513135033/2500000000 : ℝ)*x 0 + (2517040893/5000000000 : ℝ)*x 1 + (2831504213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513135033/2500000000 : ℝ)^8451 ≤ (12368815050961/100000000000000 : ℝ)^6403 := by
    have hnat : (513135033 : ℕ)^8451*100000000000000^6403 ≤ 12368815050961^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513135033 2500000000 12368815050961 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517040893/5000000000 : ℝ)^8451 ≤ (5052303791371/12500000000000 : ℝ)^6403 := by
    have hnat : (2517040893 : ℕ)^8451*12500000000000^6403 ≤ 5052303791371^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517040893 5000000000 5052303791371 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831504213/5000000000 : ℝ)^8451 ≤ (47212754606017/100000000000000 : ℝ)^6403 := by
    have hnat : (2831504213 : ℕ)^8451*100000000000000^6403 ≤ 47212754606017^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831504213 5000000000 47212754606017 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513135033/2500000000 : ℝ), (2517040893/5000000000 : ℝ), (2831504213/5000000000 : ℝ)] ![(12368815050961/100000000000000 : ℝ), (5052303791371/12500000000000 : ℝ), (47212754606017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513135033/2500000000 : ℝ)|^8451 ≤ (12368815050961/100000000000000 : ℝ)^6403
        have hw : |(-513135033/2500000000 : ℝ)|=(513135033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517040893/5000000000 : ℝ)|^8451 ≤ (5052303791371/12500000000000 : ℝ)^6403
        have hw : |(2517040893/5000000000 : ℝ)|=(2517040893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831504213/5000000000 : ℝ)|^8451 ≤ (47212754606017/100000000000000 : ℝ)^6403
        have hw : |(2831504213/5000000000 : ℝ)|=(2831504213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246247461/10000000000 : ℝ)*x 0 + (-1761126887/10000000000 : ℝ)*x 1 + (5663008807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246247461/10000000000 : ℝ)^8451 ≤ (42681766157063/100000000000000 : ℝ)^6403 := by
    have hnat : (5246247461 : ℕ)^8451*100000000000000^6403 ≤ 42681766157063^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246247461 10000000000 42681766157063 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761126887/10000000000 : ℝ)^8451 ≤ (5052737512261/50000000000000 : ℝ)^6403 := by
    have hnat : (1761126887 : ℕ)^8451*50000000000000^6403 ≤ 5052737512261^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761126887 10000000000 5052737512261 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663008807/10000000000 : ℝ)^8451 ≤ (47212758798407/100000000000000 : ℝ)^6403 := by
    have hnat : (5663008807 : ℕ)^8451*100000000000000^6403 ≤ 47212758798407^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663008807 10000000000 47212758798407 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246247461/10000000000 : ℝ), (-1761126887/10000000000 : ℝ), (5663008807/10000000000 : ℝ)] ![(42681766157063/100000000000000 : ℝ), (5052737512261/50000000000000 : ℝ), (47212758798407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246247461/10000000000 : ℝ)|^8451 ≤ (42681766157063/100000000000000 : ℝ)^6403
        have hw : |(5246247461/10000000000 : ℝ)|=(5246247461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761126887/10000000000 : ℝ)|^8451 ≤ (5052737512261/50000000000000 : ℝ)^6403
        have hw : |(-1761126887/10000000000 : ℝ)|=(1761126887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663008807/10000000000 : ℝ)|^8451 ≤ (47212758798407/100000000000000 : ℝ)^6403
        have hw : |(5663008807/10000000000 : ℝ)|=(5663008807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246247381/10000000000 : ℝ)*x 0 + (5663008551/10000000000 : ℝ)*x 1 + (-880563687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246247381/10000000000 : ℝ)^8451 ≤ (42681765298033/100000000000000 : ℝ)^6403 := by
    have hnat : (5246247381 : ℕ)^8451*100000000000000^6403 ≤ 42681765298033^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246247381 10000000000 42681765298033 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663008551/10000000000 : ℝ)^8451 ≤ (47212755981473/100000000000000 : ℝ)^6403 := by
    have hnat : (5663008551 : ℕ)^8451*100000000000000^6403 ≤ 47212755981473^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663008551 10000000000 47212755981473 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880563687/5000000000 : ℝ)^8451 ≤ (5052739356383/50000000000000 : ℝ)^6403 := by
    have hnat : (880563687 : ℕ)^8451*50000000000000^6403 ≤ 5052739356383^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880563687 5000000000 5052739356383 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246247381/10000000000 : ℝ), (5663008551/10000000000 : ℝ), (-880563687/5000000000 : ℝ)] ![(42681765298033/100000000000000 : ℝ), (47212755981473/100000000000000 : ℝ), (5052739356383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246247381/10000000000 : ℝ)|^8451 ≤ (42681765298033/100000000000000 : ℝ)^6403
        have hw : |(5246247381/10000000000 : ℝ)|=(5246247381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663008551/10000000000 : ℝ)|^8451 ≤ (47212755981473/100000000000000 : ℝ)^6403
        have hw : |(5663008551/10000000000 : ℝ)|=(5663008551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880563687/5000000000 : ℝ)|^8451 ≤ (5052739356383/50000000000000 : ℝ)^6403
        have hw : |(-880563687/5000000000 : ℝ)|=(880563687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s1_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538600491/1250000000 : ℝ)*x 0 + (2497795221/5000000000 : ℝ)*x 1 + (371582527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538600491/1250000000 : ℝ)^8451 ≤ (1645794896767/5000000000000 : ℝ)^6403 := by
    have hnat : (538600491 : ℕ)^8451*5000000000000^6403 ≤ 1645794896767^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538600491 1250000000 1645794896767 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497795221/5000000000 : ℝ)^8451 ≤ (20005518205929/50000000000000 : ℝ)^6403 := by
    have hnat : (2497795221 : ℕ)^8451*50000000000000^6403 ≤ 20005518205929^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497795221 5000000000 20005518205929 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371582527/1000000000 : ℝ)^8451 ≤ (1353653281953/5000000000000 : ℝ)^6403 := by
    have hnat : (371582527 : ℕ)^8451*5000000000000^6403 ≤ 1353653281953^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371582527 1000000000 1353653281953 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538600491/1250000000 : ℝ), (2497795221/5000000000 : ℝ), (371582527/1000000000 : ℝ)] ![(1645794896767/5000000000000 : ℝ), (20005518205929/50000000000000 : ℝ), (1353653281953/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538600491/1250000000 : ℝ)|^8451 ≤ (1645794896767/5000000000000 : ℝ)^6403
        have hw : |(538600491/1250000000 : ℝ)|=(538600491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497795221/5000000000 : ℝ)|^8451 ≤ (20005518205929/50000000000000 : ℝ)^6403
        have hw : |(2497795221/5000000000 : ℝ)|=(2497795221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371582527/1000000000 : ℝ)|^8451 ≤ (1353653281953/5000000000000 : ℝ)^6403
        have hw : |(371582527/1000000000 : ℝ)|=(371582527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1711/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (251/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1711/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1711/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1711/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1711/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1711/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1711/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (441/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (333465980987/100000000000000000000 : ℝ) := by
    have hpowers : (441/50000 : ℝ)^4225 ≤ (333465980987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4225*100000000000000000000^1024 ≤ 333465980987^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 50000 333465980987 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/50000 : ℝ)) (X := (333465980987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1711/6250 : ℝ) ^ (4225/1024 : ℝ) ≤ (954183209456821/200000000000000000 : ℝ) := by
    have hpowers : (1711/6250 : ℝ)^4225 ≤ (954183209456821/200000000000000000 : ℝ)^1024 := by
      have hnat : (1711 : ℕ)^4225*200000000000000000^1024 ≤ 954183209456821^1024*6250^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1711 6250 954183209456821 200000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1711/6250 : ℝ)) (X := (954183209456821/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000333465980987/50000000000000000000 : ℝ) ≤ (10000000016164221/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50000000333465980987/50000000000000000000 : ℝ)^1024 ≤ (10000000016164221/10000000000000000 : ℝ)^4225 := by
      have hnat : (50000000333465980987 : ℕ)^1024*10000000000000000^4225 ≤ 10000000016164221^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000333465980987 50000000000000000000 10000000016164221 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000016164221/10000000000000000 : ℝ)) (X := (50000000333465980987/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100477091938194391487/100000000000000000000 : ℝ) ≤ (10011542287828919/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100477091938194391487/100000000000000000000 : ℝ)^1024 ≤ (10011542287828919/10000000000000000 : ℝ)^4225 := by
      have hnat : (100477091938194391487 : ℕ)^1024*10000000000000000^4225 ≤ 10011542287828919^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100477091938194391487 100000000000000000000 10011542287828919 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011542287828919/10000000000000000 : ℝ)) (X := (100477091938194391487/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (100954183209456821/100000000000000000 : ℝ) ≤ (10023084559493617/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100954183209456821/100000000000000000 : ℝ)^1024 ≤ (10023084559493617/10000000000000000 : ℝ)^4225 := by
      have hnat : (100954183209456821 : ℕ)^1024*10000000000000000^4225 ≤ 10023084559493617^4225*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100954183209456821 100000000000000000 10023084559493617 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023084559493617/10000000000000000 : ℝ)) (X := (100954183209456821/100000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(333465980987/100000000000000000000 : ℝ) ≤ ((132459819930519171951/132470000000000000000 : ℝ)+2*(5771135832349/1324700000000000 : ℝ)*(441/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (132459819930519171951/132470000000000000000 : ℝ)+2*(5771135832349/1324700000000000 : ℝ)*(441/50000 : ℝ)=(10000000016164221/10000000000000000 : ℝ) by norm_num, show 1+2*(333465980987/100000000000000000000 : ℝ)=(50000000333465980987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(954183209456821/200000000000000000 : ℝ)+(333465980987/100000000000000000000 : ℝ) ≤ ((132459819930519171951/132470000000000000000 : ℝ)+(5771135832349/1324700000000000 : ℝ)*((1711/6250 : ℝ)+(441/50000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (132459819930519171951/132470000000000000000 : ℝ)+(5771135832349/1324700000000000 : ℝ)*((1711/6250 : ℝ)+(441/50000 : ℝ))=(10011542287828919/10000000000000000 : ℝ) by norm_num, show 1+(954183209456821/200000000000000000 : ℝ)+(333465980987/100000000000000000000 : ℝ)=(100477091938194391487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(954183209456821/200000000000000000 : ℝ) ≤ ((132459819930519171951/132470000000000000000 : ℝ)+2*(5771135832349/1324700000000000 : ℝ)*(1711/6250 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (132459819930519171951/132470000000000000000 : ℝ)+2*(5771135832349/1324700000000000 : ℝ)*(1711/6250 : ℝ)=(10023084559493617/10000000000000000 : ℝ) by norm_num, show 1+2*(954183209456821/200000000000000000 : ℝ)=(100954183209456821/100000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132459819930519171951/132470000000000000000 : ℝ)*(X 1 0+X 2 0)+(5771135832349/1324700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (441/50000 : ℝ)) (hi := (1711/6250 : ℝ)) (c := (132459819930519171951/132470000000000000000 : ℝ)) (alpha := (5771135832349/1324700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132459819930519171951/132470000000000000000 : ℝ)*(X 0 1+X 2 1)+(5771135832349/1324700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (441/50000 : ℝ)) (hi := (1711/6250 : ℝ)) (c := (132459819930519171951/132470000000000000000 : ℝ)) (alpha := (5771135832349/1324700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132459819930519171951/132470000000000000000 : ℝ)*(X 0 2+X 1 2)+(5771135832349/1324700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (441/50000 : ℝ)) (hi := (1711/6250 : ℝ)) (c := (132459819930519171951/132470000000000000000 : ℝ)) (alpha := (5771135832349/1324700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410376539/2000000000 : ℝ)*X 0 0+(1417899887/2500000000 : ℝ)*X 0 1+(5025649993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706393993/5000000000 : ℝ)*X 1 0+(-299810679/1250000000 : ℝ)*X 1 1+(5025650227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((27063941/50000000 : ℝ)*X 2 0+(1005130017/2000000000 : ℝ)*X 2 1+(-1199242667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538433299/1250000000 : ℝ)*X 0 0+(924585861/2500000000 : ℝ)*X 0 1+(5012747609/10000000000 : ℝ)*X 0 2+(538433299/1250000000 : ℝ)*X 1 0+(924585861/2500000000 : ℝ)*X 1 1+(5012747609/10000000000 : ℝ)*X 1 2+(538433299/1250000000 : ℝ)*X 2 0+(924585861/2500000000 : ℝ)*X 2 1+(5012747609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-513135033/2500000000 : ℝ)*X 0 0+(2517040893/5000000000 : ℝ)*X 0 1+(2831504213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246247461/10000000000 : ℝ)*X 1 0+(-1761126887/10000000000 : ℝ)*X 1 1+(5663008807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246247381/10000000000 : ℝ)*X 2 0+(5663008551/10000000000 : ℝ)*X 2 1+(-880563687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538600491/1250000000 : ℝ)*X 0 0+(2497795221/5000000000 : ℝ)*X 0 1+(371582527/1000000000 : ℝ)*X 0 2+(538600491/1250000000 : ℝ)*X 1 0+(2497795221/5000000000 : ℝ)*X 1 1+(371582527/1000000000 : ℝ)*X 1 2+(538600491/1250000000 : ℝ)*X 2 0+(2497795221/5000000000 : ℝ)*X 2 1+(371582527/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1615886316836395863169478199/827937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860129/10000000000000 : ℝ)*(base1) + (3915377/800000000000 : ℝ)*(base19) + (27531419/5000000000000 : ℝ)*(base23) + (9005939/20000000000000 : ℝ)*(upper3) + (97787267/100000000000000 : ℝ)*(upper5) + (288614937939117/25000000000000 : ℝ)*(major0) + (288614937939117/25000000000000 : ℝ)*(major1) + (288614937939117/25000000000000 : ℝ)*(major2) + (1548111338004059/100000000000000 : ℝ)*(sp0) + (1548114453789763/100000000000000 : ℝ)*(sp1) + (387028598145877/25000000000000 : ℝ)*(sp2) + (760802807131989/100000000000000 : ℝ)*(sp3) + (3613809119/100000000000000 : ℝ)*(sp4) + (1679511071/100000000000000 : ℝ)*(sp7) + (15216089904887/2000000000000 : ℝ)*(f.failure) + (96757183950743/6250000000000 : ℝ)*(f.sum) + (28997864372473/66235000000000000000000000000 : ℝ)*base66 + (14225342085648407267/3311750000000000000000000000000000 : ℝ)*base67 + (1007718986060592733/3311750000000000000000000000000000 : ℝ)*base70 + (4385130931920907267/3311750000000000000000000000000000 : ℝ)*base71 + (51656485832031/33117500000000000000000000000 : ℝ)*base73 + (22733329479879407267/3311750000000000000000000000000000 : ℝ)*base75 + (10078630986507407267/3311750000000000000000000000000000 : ℝ)*base77 + (14011315890258907267/3311750000000000000000000000000000 : ℝ)*base79 + (216607106698433/66235000000000000000000000000 : ℝ)*base82 + (277949/200000000000000000000 : ℝ)*base90 + (277949/200000000000000000000 : ℝ)*base92 + (277949/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17470753439063750652472046019/3311750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7110021/50000000000000 : ℝ)*(base1) + (491597081/50000000000000 : ℝ)*(base19) + (185381641/20000000000000 : ℝ)*(base23) + (145074343/100000000000000 : ℝ)*(upper3) + (56149277/50000000000000 : ℝ)*(upper5) + (592850914722059/50000000000000 : ℝ)*(major0) + (592850914722059/50000000000000 : ℝ)*(major1) + (592850914722059/50000000000000 : ℝ)*(major2) + (1309555837/25000000000000 : ℝ)*(sp1) + (4228916019/100000000000000 : ℝ)*(sp2) + (795005026424839/50000000000000 : ℝ)*(sp4) + (795001908606063/50000000000000 : ℝ)*(sp5) + (397501220701353/25000000000000 : ℝ)*(sp6) + (781393430192413/100000000000000 : ℝ)*(sp7) + (156278688882491/20000000000000 : ℝ)*(f.failure) + (397502509657409/25000000000000 : ℝ)*(f.sum) + (81911620052351/33117500000000000000000000000 : ℝ)*base65 + (32117049254083867109/6623500000000000000000000000000000 : ℝ)*base67 + (52252609245409867109/6623500000000000000000000000000000 : ℝ)*base69 + (28987273134119867109/6623500000000000000000000000000000 : ℝ)*base71 + (197475213134951/33117500000000000000000000000 : ℝ)*base73 + (26734205424434867109/6623500000000000000000000000000000 : ℝ)*base75 + (22981132626206867109/6623500000000000000000000000000000 : ℝ)*base77 + (32418254777787367109/6623500000000000000000000000000000 : ℝ)*base79 + (146886753917161/33117500000000000000000000000 : ℝ)*base81 + (10505257/2000000000000000000000 : ℝ)*base90 + (10505257/2000000000000000000000 : ℝ)*base92 + (10505257/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1711/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (251/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s2_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099128641/10000000000 : ℝ)*x 0 + (219603193/400000000 : ℝ)*x 1 + (2588512427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099128641/10000000000 : ℝ)^8451 ≤ (12740697315011/100000000000000 : ℝ)^6403 := by
    have hnat : (2099128641 : ℕ)^8451*100000000000000^6403 ≤ 12740697315011^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099128641 10000000000 12740697315011 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219603193/400000000 : ℝ)^8451 ≤ (9063853357659/20000000000000 : ℝ)^6403 := by
    have hnat : (219603193 : ℕ)^8451*20000000000000^6403 ≤ 9063853357659^6403*400000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219603193 400000000 9063853357659 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588512427/5000000000 : ℝ)^8451 ≤ (10485008973457/25000000000000 : ℝ)^6403 := by
    have hnat : (2588512427 : ℕ)^8451*25000000000000^6403 ≤ 10485008973457^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588512427 5000000000 10485008973457 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099128641/10000000000 : ℝ), (219603193/400000000 : ℝ), (2588512427/5000000000 : ℝ)] ![(12740697315011/100000000000000 : ℝ), (9063853357659/20000000000000 : ℝ), (10485008973457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099128641/10000000000 : ℝ)|^8451 ≤ (12740697315011/100000000000000 : ℝ)^6403
        have hw : |(-2099128641/10000000000 : ℝ)|=(2099128641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219603193/400000000 : ℝ)|^8451 ≤ (9063853357659/20000000000000 : ℝ)^6403
        have hw : |(219603193/400000000 : ℝ)|=(219603193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588512427/5000000000 : ℝ)|^8451 ≤ (10485008973457/25000000000000 : ℝ)^6403
        have hw : |(2588512427/5000000000 : ℝ)|=(2588512427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369037857/10000000000 : ℝ)*x 0 + (-2261199137/10000000000 : ℝ)*x 1 + (1035405001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369037857/10000000000 : ℝ)^8451 ≤ (22002591525957/50000000000000 : ℝ)^6403 := by
    have hnat : (5369037857 : ℕ)^8451*50000000000000^6403 ≤ 22002591525957^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369037857 10000000000 22002591525957 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261199137/10000000000 : ℝ)^8451 ≤ (7027389715239/50000000000000 : ℝ)^6403 := by
    have hnat : (2261199137 : ℕ)^8451*50000000000000^6403 ≤ 7027389715239^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261199137 10000000000 7027389715239 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035405001/2000000000 : ℝ)^8451 ≤ (41940037508373/100000000000000 : ℝ)^6403 := by
    have hnat : (1035405001 : ℕ)^8451*100000000000000^6403 ≤ 41940037508373^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035405001 2000000000 41940037508373 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369037857/10000000000 : ℝ), (-2261199137/10000000000 : ℝ), (1035405001/2000000000 : ℝ)] ![(22002591525957/50000000000000 : ℝ), (7027389715239/50000000000000 : ℝ), (41940037508373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369037857/10000000000 : ℝ)|^8451 ≤ (22002591525957/50000000000000 : ℝ)^6403
        have hw : |(5369037857/10000000000 : ℝ)|=(5369037857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261199137/10000000000 : ℝ)|^8451 ≤ (7027389715239/50000000000000 : ℝ)^6403
        have hw : |(-2261199137/10000000000 : ℝ)|=(2261199137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035405001/2000000000 : ℝ)|^8451 ≤ (41940037508373/100000000000000 : ℝ)^6403
        have hw : |(1035405001/2000000000 : ℝ)|=(1035405001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536903777/1000000000 : ℝ)*x 0 + (1035405009/2000000000 : ℝ)*x 1 + (-2826499/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536903777/1000000000 : ℝ)^8451 ≤ (2200259105539/5000000000000 : ℝ)^6403 := by
    have hnat : (536903777 : ℕ)^8451*5000000000000^6403 ≤ 2200259105539^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536903777 1000000000 2200259105539 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035405009/2000000000 : ℝ)^8451 ≤ (41940037936067/100000000000000 : ℝ)^6403 := by
    have hnat : (1035405009 : ℕ)^8451*100000000000000^6403 ≤ 41940037936067^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035405009 2000000000 41940037936067 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2826499/12500000 : ℝ)^8451 ≤ (14054779947311/100000000000000 : ℝ)^6403 := by
    have hnat : (2826499 : ℕ)^8451*100000000000000^6403 ≤ 14054779947311^6403*12500000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826499 12500000 14054779947311 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536903777/1000000000 : ℝ), (1035405009/2000000000 : ℝ), (-2826499/12500000 : ℝ)] ![(2200259105539/5000000000000 : ℝ), (41940037936067/100000000000000 : ℝ), (14054779947311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536903777/1000000000 : ℝ)|^8451 ≤ (2200259105539/5000000000000 : ℝ)^6403
        have hw : |(536903777/1000000000 : ℝ)|=(536903777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035405009/2000000000 : ℝ)|^8451 ≤ (41940037936067/100000000000000 : ℝ)^6403
        have hw : |(1035405009/2000000000 : ℝ)|=(1035405009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2826499/12500000 : ℝ)|^8451 ≤ (14054779947311/100000000000000 : ℝ)^6403
        have hw : |(-2826499/12500000 : ℝ)|=(2826499/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4340134077/10000000000 : ℝ)*x 0 + (4032905453/10000000000 : ℝ)*x 1 + (4669921593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340134077/10000000000 : ℝ)^8451 ≤ (16616077388821/50000000000000 : ℝ)^6403 := by
    have hnat : (4340134077 : ℕ)^8451*50000000000000^6403 ≤ 16616077388821^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340134077 10000000000 16616077388821 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032905453/10000000000 : ℝ)^8451 ≤ (30163028408463/100000000000000 : ℝ)^6403 := by
    have hnat : (4032905453 : ℕ)^8451*100000000000000^6403 ≤ 30163028408463^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032905453 10000000000 30163028408463 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4669921593/10000000000 : ℝ)^8451 ≤ (7320963360887/20000000000000 : ℝ)^6403 := by
    have hnat : (4669921593 : ℕ)^8451*20000000000000^6403 ≤ 7320963360887^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669921593 10000000000 7320963360887 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340134077/10000000000 : ℝ), (4032905453/10000000000 : ℝ), (4669921593/10000000000 : ℝ)] ![(16616077388821/50000000000000 : ℝ), (30163028408463/100000000000000 : ℝ), (7320963360887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340134077/10000000000 : ℝ)|^8451 ≤ (16616077388821/50000000000000 : ℝ)^6403
        have hw : |(4340134077/10000000000 : ℝ)|=(4340134077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032905453/10000000000 : ℝ)|^8451 ≤ (30163028408463/100000000000000 : ℝ)^6403
        have hw : |(4032905453/10000000000 : ℝ)|=(4032905453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4669921593/10000000000 : ℝ)|^8451 ≤ (7320963360887/20000000000000 : ℝ)^6403
        have hw : |(4669921593/10000000000 : ℝ)|=(4669921593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-262400473/1250000000 : ℝ)*x 0 + (1294753787/2500000000 : ℝ)*x 1 + (1372017767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262400473/1250000000 : ℝ)^8451 ≤ (12741299277959/100000000000000 : ℝ)^6403 := by
    have hnat : (262400473 : ℕ)^8451*100000000000000^6403 ≤ 12741299277959^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262400473 1250000000 12741299277959 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294753787/2500000000 : ℝ)^8451 ≤ (20980659060631/50000000000000 : ℝ)^6403 := by
    have hnat : (1294753787 : ℕ)^8451*50000000000000^6403 ≤ 20980659060631^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294753787 2500000000 20980659060631 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372017767/2500000000 : ℝ)^8451 ≤ (45297382581833/100000000000000 : ℝ)^6403 := by
    have hnat : (1372017767 : ℕ)^8451*100000000000000^6403 ≤ 45297382581833^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372017767 2500000000 45297382581833 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262400473/1250000000 : ℝ), (1294753787/2500000000 : ℝ), (1372017767/2500000000 : ℝ)] ![(12741299277959/100000000000000 : ℝ), (20980659060631/50000000000000 : ℝ), (45297382581833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262400473/1250000000 : ℝ)|^8451 ≤ (12741299277959/100000000000000 : ℝ)^6403
        have hw : |(-262400473/1250000000 : ℝ)|=(262400473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294753787/2500000000 : ℝ)|^8451 ≤ (20980659060631/50000000000000 : ℝ)^6403
        have hw : |(1294753787/2500000000 : ℝ)|=(1294753787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372017767/2500000000 : ℝ)|^8451 ≤ (45297382581833/100000000000000 : ℝ)^6403
        have hw : |(1372017767/2500000000 : ℝ)|=(1372017767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289012857/10000000000 : ℝ)*x 0 + (-1950152813/10000000000 : ℝ)*x 1 + (5488071113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289012857/10000000000 : ℝ)^8451 ≤ (43141573036369/100000000000000 : ℝ)^6403 := by
    have hnat : (5289012857 : ℕ)^8451*100000000000000^6403 ≤ 43141573036369^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289012857 10000000000 43141573036369 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950152813/10000000000 : ℝ)^8451 ≤ (2890260970413/25000000000000 : ℝ)^6403 := by
    have hnat : (1950152813 : ℕ)^8451*25000000000000^6403 ≤ 2890260970413^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950152813 10000000000 2890260970413 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488071113/10000000000 : ℝ)^8451 ≤ (45297383072053/100000000000000 : ℝ)^6403 := by
    have hnat : (5488071113 : ℕ)^8451*100000000000000^6403 ≤ 45297383072053^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488071113 10000000000 45297383072053 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289012857/10000000000 : ℝ), (-1950152813/10000000000 : ℝ), (5488071113/10000000000 : ℝ)] ![(43141573036369/100000000000000 : ℝ), (2890260970413/25000000000000 : ℝ), (45297383072053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289012857/10000000000 : ℝ)|^8451 ≤ (43141573036369/100000000000000 : ℝ)^6403
        have hw : |(5289012857/10000000000 : ℝ)|=(5289012857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950152813/10000000000 : ℝ)|^8451 ≤ (2890260970413/25000000000000 : ℝ)^6403
        have hw : |(-1950152813/10000000000 : ℝ)|=(1950152813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488071113/10000000000 : ℝ)|^8451 ≤ (45297383072053/100000000000000 : ℝ)^6403
        have hw : |(5488071113/10000000000 : ℝ)|=(5488071113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20660207/39062500 : ℝ)*x 0 + (5488071219/10000000000 : ℝ)*x 1 + (-1950152479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20660207/39062500 : ℝ)^8451 ≤ (43141574489751/100000000000000 : ℝ)^6403 := by
    have hnat : (20660207 : ℕ)^8451*100000000000000^6403 ≤ 43141574489751^6403*39062500^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20660207 39062500 43141574489751 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488071219/10000000000 : ℝ)^8451 ≤ (5662173028349/12500000000000 : ℝ)^6403 := by
    have hnat : (5488071219 : ℕ)^8451*12500000000000^6403 ≤ 5662173028349^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488071219 10000000000 5662173028349 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950152479/10000000000 : ℝ)^8451 ≤ (11561041268291/100000000000000 : ℝ)^6403 := by
    have hnat : (1950152479 : ℕ)^8451*100000000000000^6403 ≤ 11561041268291^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950152479 10000000000 11561041268291 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20660207/39062500 : ℝ), (5488071219/10000000000 : ℝ), (-1950152479/10000000000 : ℝ)] ![(43141574489751/100000000000000 : ℝ), (5662173028349/12500000000000 : ℝ), (11561041268291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20660207/39062500 : ℝ)|^8451 ≤ (43141574489751/100000000000000 : ℝ)^6403
        have hw : |(20660207/39062500 : ℝ)|=(20660207/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488071219/10000000000 : ℝ)|^8451 ≤ (5662173028349/12500000000000 : ℝ)^6403
        have hw : |(5488071219/10000000000 : ℝ)|=(5488071219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950152479/10000000000 : ℝ)|^8451 ≤ (11561041268291/100000000000000 : ℝ)^6403
        have hw : |(-1950152479/10000000000 : ℝ)|=(1950152479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s2_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4340286519/10000000000 : ℝ)*x 0 + (4665872109/10000000000 : ℝ)*x 1 + (2018496049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340286519/10000000000 : ℝ)^8451 ≤ (6646739073499/20000000000000 : ℝ)^6403 := by
    have hnat : (4340286519 : ℕ)^8451*20000000000000^6403 ≤ 6646739073499^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340286519 10000000000 6646739073499 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4665872109/10000000000 : ℝ)^8451 ≤ (36562928508507/100000000000000 : ℝ)^6403 := by
    have hnat : (4665872109 : ℕ)^8451*100000000000000^6403 ≤ 36562928508507^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4665872109 10000000000 36562928508507 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018496049/5000000000 : ℝ)^8451 ≤ (30203376107583/100000000000000 : ℝ)^6403 := by
    have hnat : (2018496049 : ℕ)^8451*100000000000000^6403 ≤ 30203376107583^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018496049 5000000000 30203376107583 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340286519/10000000000 : ℝ), (4665872109/10000000000 : ℝ), (2018496049/5000000000 : ℝ)] ![(6646739073499/20000000000000 : ℝ), (36562928508507/100000000000000 : ℝ), (30203376107583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340286519/10000000000 : ℝ)|^8451 ≤ (6646739073499/20000000000000 : ℝ)^6403
        have hw : |(4340286519/10000000000 : ℝ)|=(4340286519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4665872109/10000000000 : ℝ)|^8451 ≤ (36562928508507/100000000000000 : ℝ)^6403
        have hw : |(4665872109/10000000000 : ℝ)|=(4665872109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018496049/5000000000 : ℝ)|^8451 ≤ (30203376107583/100000000000000 : ℝ)^6403
        have hw : |(2018496049/5000000000 : ℝ)|=(2018496049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2391/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8091/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (251/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (251/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (251/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (251/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (251/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (251/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (251/4000 : ℝ) ^ (4225/1024 : ℝ) ≤ (1093912113487489/100000000000000000000 : ℝ) := by
    have hpowers : (251/4000 : ℝ)^4225 ≤ (1093912113487489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (251 : ℕ)^4225*100000000000000000000^1024 ≤ 1093912113487489^1024*4000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251 4000 1093912113487489 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (251/4000 : ℝ)) (X := (1093912113487489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19931/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (64393709413661613/50000000000000000000 : ℝ) := by
    have hpowers : (19931/100000 : ℝ)^4225 ≤ (64393709413661613/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19931 : ℕ)^4225*50000000000000000000^1024 ≤ 64393709413661613^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19931 100000 64393709413661613 50000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19931/100000 : ℝ)) (X := (64393709413661613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001093912113487489/50000000000000000000 : ℝ) ≤ (2000010605034041/2000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50001093912113487489/50000000000000000000 : ℝ)^1024 ≤ (2000010605034041/2000000000000000 : ℝ)^4225 := by
      have hnat : (50001093912113487489 : ℕ)^1024*2000000000000000^4225 ≤ 2000010605034041^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001093912113487489 50000000000000000000 2000010605034041 2000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000010605034041/2000000000000000 : ℝ)) (X := (50001093912113487489/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20025976266188162143/20000000000000000000 : ℝ) ≤ (10003146345462323/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (20025976266188162143/20000000000000000000 : ℝ)^1024 ≤ (10003146345462323/10000000000000000 : ℝ)^4225 := by
      have hnat : (20025976266188162143 : ℕ)^1024*10000000000000000^4225 ≤ 10003146345462323^4225*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20025976266188162143 20000000000000000000 10003146345462323 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003146345462323/10000000000000000 : ℝ)) (X := (20025976266188162143/20000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064393709413661613/25000000000000000000 : ℝ) ≤ (10006239665754441/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (25064393709413661613/25000000000000000000 : ℝ)^1024 ≤ (10006239665754441/10000000000000000 : ℝ)^4225 := by
      have hnat : (25064393709413661613 : ℕ)^1024*10000000000000000^4225 ≤ 10006239665754441^4225*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064393709413661613 25000000000000000000 10006239665754441 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006239665754441/10000000000000000 : ℝ)) (X := (25064393709413661613/25000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1093912113487489/100000000000000000000 : ℝ) ≤ ((6826095147102911929/6828000000000000000 : ℝ)+2*(1546660146059/682800000000000 : ℝ)*(251/4000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (6826095147102911929/6828000000000000000 : ℝ)+2*(1546660146059/682800000000000 : ℝ)*(251/4000 : ℝ)=(2000010605034041/2000000000000000 : ℝ) by norm_num, show 1+2*(1093912113487489/100000000000000000000 : ℝ)=(50001093912113487489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64393709413661613/50000000000000000000 : ℝ)+(1093912113487489/100000000000000000000 : ℝ) ≤ ((6826095147102911929/6828000000000000000 : ℝ)+(1546660146059/682800000000000 : ℝ)*((19931/100000 : ℝ)+(251/4000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (6826095147102911929/6828000000000000000 : ℝ)+(1546660146059/682800000000000 : ℝ)*((19931/100000 : ℝ)+(251/4000 : ℝ))=(10003146345462323/10000000000000000 : ℝ) by norm_num, show 1+(64393709413661613/50000000000000000000 : ℝ)+(1093912113487489/100000000000000000000 : ℝ)=(20025976266188162143/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64393709413661613/50000000000000000000 : ℝ) ≤ ((6826095147102911929/6828000000000000000 : ℝ)+2*(1546660146059/682800000000000 : ℝ)*(19931/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (6826095147102911929/6828000000000000000 : ℝ)+2*(1546660146059/682800000000000 : ℝ)*(19931/100000 : ℝ)=(10006239665754441/10000000000000000 : ℝ) by norm_num, show 1+2*(64393709413661613/50000000000000000000 : ℝ)=(25064393709413661613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6826095147102911929/6828000000000000000 : ℝ)*(X 1 0+X 2 0)+(1546660146059/682800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (251/4000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (6826095147102911929/6828000000000000000 : ℝ)) (alpha := (1546660146059/682800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6826095147102911929/6828000000000000000 : ℝ)*(X 0 1+X 2 1)+(1546660146059/682800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (251/4000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (6826095147102911929/6828000000000000000 : ℝ)) (alpha := (1546660146059/682800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6826095147102911929/6828000000000000000 : ℝ)*(X 0 2+X 1 2)+(1546660146059/682800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (251/4000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (6826095147102911929/6828000000000000000 : ℝ)) (alpha := (1546660146059/682800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2099128641/10000000000 : ℝ)*X 0 0+(219603193/400000000 : ℝ)*X 0 1+(2588512427/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369037857/10000000000 : ℝ)*X 1 0+(-2261199137/10000000000 : ℝ)*X 1 1+(1035405001/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536903777/1000000000 : ℝ)*X 2 0+(1035405009/2000000000 : ℝ)*X 2 1+(-2826499/12500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340134077/10000000000 : ℝ)*X 0 0+(4032905453/10000000000 : ℝ)*X 0 1+(4669921593/10000000000 : ℝ)*X 0 2+(4340134077/10000000000 : ℝ)*X 1 0+(4032905453/10000000000 : ℝ)*X 1 1+(4669921593/10000000000 : ℝ)*X 1 2+(4340134077/10000000000 : ℝ)*X 2 0+(4032905453/10000000000 : ℝ)*X 2 1+(4669921593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262400473/1250000000 : ℝ)*X 0 0+(1294753787/2500000000 : ℝ)*X 0 1+(1372017767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289012857/10000000000 : ℝ)*X 1 0+(-1950152813/10000000000 : ℝ)*X 1 1+(5488071113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20660207/39062500 : ℝ)*X 2 0+(5488071219/10000000000 : ℝ)*X 2 1+(-1950152479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340286519/10000000000 : ℝ)*X 0 0+(4665872109/10000000000 : ℝ)*X 0 1+(2018496049/5000000000 : ℝ)*X 0 2+(4340286519/10000000000 : ℝ)*X 1 0+(4665872109/10000000000 : ℝ)*X 1 1+(2018496049/5000000000 : ℝ)*X 1 2+(4340286519/10000000000 : ℝ)*X 2 0+(4665872109/10000000000 : ℝ)*X 2 1+(2018496049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33109897652645520955401/5690000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511903009/50000000000000 : ℝ)*(base19) + (229775269/25000000000000 : ℝ)*(base23) + (28425617/100000000000000 : ℝ)*(lower2) + (168010809/100000000000000 : ℝ)*(upper3) + (17106017/25000000000000 : ℝ)*(upper5) + (1191045957227057/50000000000000 : ℝ)*(major0) + (1191045957227057/50000000000000 : ℝ)*(major1) + (1191045957227057/50000000000000 : ℝ)*(major2) + (6238947300761/195312500000 : ℝ)*(sp0) + (319435201821697/10000000000000 : ℝ)*(sp1) + (3194352122921913/100000000000000 : ℝ)*(sp2) + (31396485740307/2000000000000 : ℝ)*(sp3) + (6012016679/50000000000000 : ℝ)*(sp4) + (6305904457/100000000000000 : ℝ)*(sp7) + (6132150753593/390625000000 : ℝ)*(f.failure) + (3194353042022989/100000000000000 : ℝ)*(f.sum) + (138027832360933/17070000000000000000000000000 : ℝ)*base65 + (380805061505102349/113800000000000000000000000000000 : ℝ)*base68 + (1718815237126902349/113800000000000000000000000000000 : ℝ)*base70 + (27741982566097651/113800000000000000000000000000000 : ℝ)*base71 + (102967449984253/17070000000000000000000000000 : ℝ)*base73 + (497970665136697651/113800000000000000000000000000000 : ℝ)*base75 + (245347984630097651/113800000000000000000000000000000 : ℝ)*base77 + (419341121478902349/113800000000000000000000000000000 : ℝ)*base80 + (7386967744843/17070000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (377739/39062500000000000000 : ℝ)*base89 + (377739/39062500000000000000 : ℝ)*base91 + (377739/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (551913615492974727006820869/56900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1171650459/50000000000000 : ℝ)*(base19) + (1274223593/50000000000000 : ℝ)*(base23) + (18037453/100000000000000 : ℝ)*(upper2) + (305821123/100000000000000 : ℝ)*(upper3) + (95243829/50000000000000 : ℝ)*(upper5) + (2412894258314139/100000000000000 : ℝ)*(major0) + (2412894258314139/100000000000000 : ℝ)*(major1) + (2412894258314139/100000000000000 : ℝ)*(major2) + (384800291/1562500000000 : ℝ)*(sp1) + (30473390827/100000000000000 : ℝ)*(sp2) + (1617829220860077/50000000000000 : ℝ)*(sp4) + (808907867800153/25000000000000 : ℝ)*(sp5) + (1617812709941071/50000000000000 : ℝ)*(sp6) + (1590129751584381/100000000000000 : ℝ)*(sp7) + (1590129751584381/100000000000000 : ℝ)*(f.failure) + (1617829220860077/50000000000000 : ℝ)*(f.sum) + (15286189618073/11380000000000000000000000000 : ℝ)*base66 + (2066012737611891377/227600000000000000000000000000000 : ℝ)*base67 + (1507913983515491377/227600000000000000000000000000000 : ℝ)*base69 + (262110974719891377/227600000000000000000000000000000 : ℝ)*base71 + (57656384356767/11380000000000000000000000000 : ℝ)*base73 + (1763984512125091377/227600000000000000000000000000000 : ℝ)*base75 + (873078730024691377/227600000000000000000000000000000 : ℝ)*base77 + (2165444644967708623/227600000000000000000000000000000 : ℝ)*base80 + (11241092046467/11380000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (51076287/10000000000000000000000 : ℝ)*base90 + (51076287/10000000000000000000000 : ℝ)*base92 + (51076287/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1258_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1258_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1258_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1258_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

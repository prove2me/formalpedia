-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:19.732952+00:00
-- url     : https://prove2.me/submissions/34b28ca0-9576-4881-942c-9eb6db887025

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
theorem support_rectangle_w1158_s9_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079631219/5000000000 : ℝ)*x 0 + (1078538793/2000000000 : ℝ)*x 1 + (5266041607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079631219/5000000000 : ℝ)^8351 ≤ (13122145895317/100000000000000 : ℝ)^6303 := by
    have hnat : (1079631219 : ℕ)^8351*100000000000000^6303 ≤ 13122145895317^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079631219 5000000000 13122145895317 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078538793/2000000000 : ℝ)^8351 ≤ (44122779512101/100000000000000 : ℝ)^6303 := by
    have hnat : (1078538793 : ℕ)^8351*100000000000000^6303 ≤ 44122779512101^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078538793 2000000000 44122779512101 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266041607/10000000000 : ℝ)^8351 ≤ (21377537290651/50000000000000 : ℝ)^6303 := by
    have hnat : (5266041607 : ℕ)^8351*50000000000000^6303 ≤ 21377537290651^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266041607 10000000000 21377537290651 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079631219/5000000000 : ℝ), (1078538793/2000000000 : ℝ), (5266041607/10000000000 : ℝ)] ![(13122145895317/100000000000000 : ℝ), (44122779512101/100000000000000 : ℝ), (21377537290651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079631219/5000000000 : ℝ)|^8351 ≤ (13122145895317/100000000000000 : ℝ)^6303
        have hw : |(-1079631219/5000000000 : ℝ)|=(1079631219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078538793/2000000000 : ℝ)|^8351 ≤ (44122779512101/100000000000000 : ℝ)^6303
        have hw : |(1078538793/2000000000 : ℝ)|=(1078538793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266041607/10000000000 : ℝ)|^8351 ≤ (21377537290651/50000000000000 : ℝ)^6303
        have hw : |(5266041607/10000000000 : ℝ)|=(5266041607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s9_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534468443/1000000000 : ℝ)*x 0 + (-1111749029/5000000000 : ℝ)*x 1 + (210641661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534468443/1000000000 : ℝ)^8351 ≤ (21801543833819/50000000000000 : ℝ)^6303 := by
    have hnat : (534468443 : ℕ)^8351*50000000000000^6303 ≤ 21801543833819^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534468443 1000000000 21801543833819 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111749029/5000000000 : ℝ)^8351 ≤ (1364183861951/10000000000000 : ℝ)^6303 := by
    have hnat : (1111749029 : ℕ)^8351*10000000000000^6303 ≤ 1364183861951^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111749029 5000000000 1364183861951 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210641661/400000000 : ℝ)^8351 ≤ (42755073699221/100000000000000 : ℝ)^6303 := by
    have hnat : (210641661 : ℕ)^8351*100000000000000^6303 ≤ 42755073699221^6303*400000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210641661 400000000 42755073699221 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534468443/1000000000 : ℝ), (-1111749029/5000000000 : ℝ), (210641661/400000000 : ℝ)] ![(21801543833819/50000000000000 : ℝ), (1364183861951/10000000000000 : ℝ), (42755073699221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534468443/1000000000 : ℝ)|^8351 ≤ (21801543833819/50000000000000 : ℝ)^6303
        have hw : |(534468443/1000000000 : ℝ)|=(534468443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111749029/5000000000 : ℝ)|^8351 ≤ (1364183861951/10000000000000 : ℝ)^6303
        have hw : |(-1111749029/5000000000 : ℝ)|=(1111749029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210641661/400000000 : ℝ)|^8351 ≤ (42755073699221/100000000000000 : ℝ)^6303
        have hw : |(210641661/400000000 : ℝ)|=(210641661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s9_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344684369/10000000000 : ℝ)*x 0 + (2633020797/5000000000 : ℝ)*x 1 + (-2223498047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344684369/10000000000 : ℝ)^8351 ≤ (43603087008287/100000000000000 : ℝ)^6303 := by
    have hnat : (5344684369 : ℕ)^8351*100000000000000^6303 ≤ 43603087008287^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344684369 10000000000 43603087008287 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633020797/5000000000 : ℝ)^8351 ≤ (2137753722073/5000000000000 : ℝ)^6303 := by
    have hnat : (2633020797 : ℕ)^8351*5000000000000^6303 ≤ 2137753722073^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633020797 5000000000 2137753722073 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223498047/10000000000 : ℝ)^8351 ≤ (13641838530093/100000000000000 : ℝ)^6303 := by
    have hnat : (2223498047 : ℕ)^8351*100000000000000^6303 ≤ 13641838530093^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223498047 10000000000 13641838530093 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344684369/10000000000 : ℝ), (2633020797/5000000000 : ℝ), (-2223498047/10000000000 : ℝ)] ![(43603087008287/100000000000000 : ℝ), (2137753722073/5000000000000 : ℝ), (13641838530093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344684369/10000000000 : ℝ)|^8351 ≤ (43603087008287/100000000000000 : ℝ)^6303
        have hw : |(5344684369/10000000000 : ℝ)|=(5344684369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633020797/5000000000 : ℝ)|^8351 ≤ (2137753722073/5000000000000 : ℝ)^6303
        have hw : |(2633020797/5000000000 : ℝ)|=(2633020797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223498047/10000000000 : ℝ)|^8351 ≤ (13641838530093/100000000000000 : ℝ)^6303
        have hw : |(-2223498047/10000000000 : ℝ)|=(2223498047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s9_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181213197/5000000000 : ℝ)*x 0 + (2118929931/5000000000 : ℝ)*x 1 + (561327843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181213197/5000000000 : ℝ)^8351 ≤ (33317077512767/100000000000000 : ℝ)^6303 := by
    have hnat : (2181213197 : ℕ)^8351*100000000000000^6303 ≤ 33317077512767^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181213197 5000000000 33317077512767 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118929931/5000000000 : ℝ)^8351 ≤ (32062496280697/100000000000000 : ℝ)^6303 := by
    have hnat : (2118929931 : ℕ)^8351*100000000000000^6303 ≤ 32062496280697^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118929931 5000000000 32062496280697 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561327843/1250000000 : ℝ)^8351 ≤ (4327553273977/12500000000000 : ℝ)^6303 := by
    have hnat : (561327843 : ℕ)^8351*12500000000000^6303 ≤ 4327553273977^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561327843 1250000000 4327553273977 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181213197/5000000000 : ℝ), (2118929931/5000000000 : ℝ), (561327843/1250000000 : ℝ)] ![(33317077512767/100000000000000 : ℝ), (32062496280697/100000000000000 : ℝ), (4327553273977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181213197/5000000000 : ℝ)|^8351 ≤ (33317077512767/100000000000000 : ℝ)^6303
        have hw : |(2181213197/5000000000 : ℝ)|=(2181213197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118929931/5000000000 : ℝ)|^8351 ≤ (32062496280697/100000000000000 : ℝ)^6303
        have hw : |(2118929931/5000000000 : ℝ)|=(2118929931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561327843/1250000000 : ℝ)|^8351 ≤ (4327553273977/12500000000000 : ℝ)^6303
        have hw : |(561327843/1250000000 : ℝ)|=(561327843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s9_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-539816819/2500000000 : ℝ)*x 0 + (5266359707/10000000000 : ℝ)*x 1 + (674046839/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539816819/2500000000 : ℝ)^8351 ≤ (13122184849727/100000000000000 : ℝ)^6303 := by
    have hnat : (539816819 : ℕ)^8351*100000000000000^6303 ≤ 13122184849727^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539816819 2500000000 13122184849727 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266359707/10000000000 : ℝ)^8351 ≤ (21379248221647/50000000000000 : ℝ)^6303 := by
    have hnat : (5266359707 : ℕ)^8351*50000000000000^6303 ≤ 21379248221647^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266359707 10000000000 21379248221647 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674046839/1250000000 : ℝ)^8351 ≤ (44119318691601/100000000000000 : ℝ)^6303 := by
    have hnat : (674046839 : ℕ)^8351*100000000000000^6303 ≤ 44119318691601^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674046839 1250000000 44119318691601 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539816819/2500000000 : ℝ), (5266359707/10000000000 : ℝ), (674046839/1250000000 : ℝ)] ![(13122184849727/100000000000000 : ℝ), (21379248221647/50000000000000 : ℝ), (44119318691601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539816819/2500000000 : ℝ)|^8351 ≤ (13122184849727/100000000000000 : ℝ)^6303
        have hw : |(-539816819/2500000000 : ℝ)|=(539816819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266359707/10000000000 : ℝ)|^8351 ≤ (21379248221647/50000000000000 : ℝ)^6303
        have hw : |(5266359707/10000000000 : ℝ)|=(5266359707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674046839/1250000000 : ℝ)|^8351 ≤ (44119318691601/100000000000000 : ℝ)^6303
        have hw : |(674046839/1250000000 : ℝ)|=(674046839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s9_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362436063/10000000000 : ℝ)*x 0 + (4489987743/10000000000 : ℝ)*x 1 + (2119248569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362436063/10000000000 : ℝ)^8351 ≤ (16658587675847/50000000000000 : ℝ)^6303 := by
    have hnat : (4362436063 : ℕ)^8351*50000000000000^6303 ≤ 16658587675847^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362436063 10000000000 16658587675847 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489987743/10000000000 : ℝ)^8351 ≤ (17306970062289/50000000000000 : ℝ)^6303 := by
    have hnat : (4489987743 : ℕ)^8351*50000000000000^6303 ≤ 17306970062289^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489987743 10000000000 17306970062289 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119248569/5000000000 : ℝ)^8351 ≤ (32068884504019/100000000000000 : ℝ)^6303 := by
    have hnat : (2119248569 : ℕ)^8351*100000000000000^6303 ≤ 32068884504019^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119248569 5000000000 32068884504019 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362436063/10000000000 : ℝ), (4489987743/10000000000 : ℝ), (2119248569/5000000000 : ℝ)] ![(16658587675847/50000000000000 : ℝ), (17306970062289/50000000000000 : ℝ), (32068884504019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362436063/10000000000 : ℝ)|^8351 ≤ (16658587675847/50000000000000 : ℝ)^6303
        have hw : |(4362436063/10000000000 : ℝ)|=(4362436063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489987743/10000000000 : ℝ)|^8351 ≤ (17306970062289/50000000000000 : ℝ)^6303
        have hw : |(4489987743/10000000000 : ℝ)|=(4489987743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119248569/5000000000 : ℝ)|^8351 ≤ (32068884504019/100000000000000 : ℝ)^6303
        have hw : |(2119248569/5000000000 : ℝ)|=(2119248569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5687/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (7076004173047401/50000000000000000000 : ℝ) := by
    have hpowers : (5687/50000 : ℝ)^4175 ≤ (7076004173047401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5687 : ℕ)^4175*50000000000000000000^1024 ≤ 7076004173047401^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5687 50000 7076004173047401 50000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5687/50000 : ℝ)) (X := (7076004173047401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (3357049834838973/10000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^4175 ≤ (3357049834838973/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7029 : ℕ)^4175*10000000000000000000^1024 ≤ 3357049834838973^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 3357049834838973 10000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (3357049834838973/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007076004173047401/25000000000000000000 : ℝ) ≤ (10000694136955957/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (25007076004173047401/25000000000000000000 : ℝ)^1024 ≤ (10000694136955957/10000000000000000 : ℝ)^4175 := by
      have hnat : (25007076004173047401 : ℕ)^1024*10000000000000000^4175 ≤ 10000694136955957^4175*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007076004173047401 25000000000000000000 10000694136955957 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000694136955957/10000000000000000 : ℝ)) (X := (25007076004173047401/25000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011930626673621133/25000000000000000000 : ℝ) ≤ (2500292569154431/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (25011930626673621133/25000000000000000000 : ℝ)^1024 ≤ (2500292569154431/2500000000000000 : ℝ)^4175 := by
      have hnat : (25011930626673621133 : ℕ)^1024*2500000000000000^4175 ≤ 2500292569154431^4175*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011930626673621133 25000000000000000000 2500292569154431 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500292569154431/2500000000000000 : ℝ)) (X := (25011930626673621133/25000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003357049834838973/5000000000000000000 : ℝ) ≤ (10001646416279491/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (5003357049834838973/5000000000000000000 : ℝ)^1024 ≤ (10001646416279491/10000000000000000 : ℝ)^4175 := by
      have hnat : (5003357049834838973 : ℕ)^1024*10000000000000000^4175 ≤ 10001646416279491^4175*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003357049834838973 5000000000000000000 10001646416279491 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001646416279491/10000000000000000 : ℝ)) (X := (5003357049834838973/5000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7076004173047401/50000000000000000000 : ℝ) ≤ ((304898089074589919/305000000000000000 : ℝ)+2*(43285423797/24400000000000 : ℝ)*(5687/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (304898089074589919/305000000000000000 : ℝ)+2*(43285423797/24400000000000 : ℝ)*(5687/50000 : ℝ)=(10000694136955957/10000000000000000 : ℝ) by norm_num, show 1+2*(7076004173047401/50000000000000000000 : ℝ)=(25007076004173047401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3357049834838973/10000000000000000000 : ℝ)+(7076004173047401/50000000000000000000 : ℝ) ≤ ((304898089074589919/305000000000000000 : ℝ)+(43285423797/24400000000000 : ℝ)*((7029/50000 : ℝ)+(5687/50000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (304898089074589919/305000000000000000 : ℝ)+(43285423797/24400000000000 : ℝ)*((7029/50000 : ℝ)+(5687/50000 : ℝ))=(2500292569154431/2500000000000000 : ℝ) by norm_num, show 1+(3357049834838973/10000000000000000000 : ℝ)+(7076004173047401/50000000000000000000 : ℝ)=(25011930626673621133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3357049834838973/10000000000000000000 : ℝ) ≤ ((304898089074589919/305000000000000000 : ℝ)+2*(43285423797/24400000000000 : ℝ)*(7029/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (304898089074589919/305000000000000000 : ℝ)+2*(43285423797/24400000000000 : ℝ)*(7029/50000 : ℝ)=(10001646416279491/10000000000000000 : ℝ) by norm_num, show 1+2*(3357049834838973/10000000000000000000 : ℝ)=(5003357049834838973/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (304898089074589919/305000000000000000 : ℝ)*(X 1 0+X 2 0)+(43285423797/24400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (304898089074589919/305000000000000000 : ℝ)) (alpha := (43285423797/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (304898089074589919/305000000000000000 : ℝ)*(X 0 1+X 2 1)+(43285423797/24400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (304898089074589919/305000000000000000 : ℝ)) (alpha := (43285423797/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (304898089074589919/305000000000000000 : ℝ)*(X 0 2+X 1 2)+(43285423797/24400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (304898089074589919/305000000000000000 : ℝ)) (alpha := (43285423797/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079631219/5000000000 : ℝ)*X 0 0+(1078538793/2000000000 : ℝ)*X 0 1+(5266041607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534468443/1000000000 : ℝ)*X 1 0+(-1111749029/5000000000 : ℝ)*X 1 1+(210641661/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344684369/10000000000 : ℝ)*X 2 0+(2633020797/5000000000 : ℝ)*X 2 1+(-2223498047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181213197/5000000000 : ℝ)*X 0 0+(2118929931/5000000000 : ℝ)*X 0 1+(561327843/1250000000 : ℝ)*X 0 2+(2181213197/5000000000 : ℝ)*X 1 0+(2118929931/5000000000 : ℝ)*X 1 1+(561327843/1250000000 : ℝ)*X 1 2+(2181213197/5000000000 : ℝ)*X 2 0+(2118929931/5000000000 : ℝ)*X 2 1+(561327843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-539816819/2500000000 : ℝ)*X 0 0+(5266359707/10000000000 : ℝ)*X 0 1+(674046839/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4362436063/10000000000 : ℝ)*X 0 0+(4489987743/10000000000 : ℝ)*X 0 1+(2119248569/5000000000 : ℝ)*X 0 2+(4362436063/10000000000 : ℝ)*X 1 0+(4489987743/10000000000 : ℝ)*X 1 1+(2119248569/5000000000 : ℝ)*X 1 2+(4362436063/10000000000 : ℝ)*X 2 0+(4489987743/10000000000 : ℝ)*X 2 1+(2119248569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37240732382464247313/10000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193845223/25000000000000 : ℝ)*(base19) + (634066251/100000000000000 : ℝ)*(base23) + (27364667/100000000000000 : ℝ)*(lower2) + (88374893/100000000000000 : ℝ)*(upper3) + (1596639/3125000000000 : ℝ)*(upper5) + (2962991014333617/50000000000000 : ℝ)*(major0) + (2962991014333617/50000000000000 : ℝ)*(major1) + (2962991014333617/50000000000000 : ℝ)*(major2) + (3947823785042209/50000000000000 : ℝ)*(sp0) + (493478983094791/6250000000000 : ℝ)*(sp1) + (7895663870831297/100000000000000 : ℝ)*(sp2) + (1978143971982767/50000000000000 : ℝ)*(sp3) + (1693481313/10000000000000 : ℝ)*(sp4) + (2296867121/20000000000000 : ℝ)*(sp5) + (1978149714150569/50000000000000 : ℝ)*(f.failure) + (7895664504897547/100000000000000 : ℝ)*(f.sum) + (25074185739/10000000000000000000000000 : ℝ)*base65 + (2175956734542943/250000000000000000000000000000 : ℝ)*base67 + (810412257707057/250000000000000000000000000000 : ℝ)*base70 + (1430177362542943/250000000000000000000000000000 : ℝ)*base71 + (18622106541/10000000000000000000000000 : ℝ)*base74 + (892210286207057/250000000000000000000000000000 : ℝ)*base76 + (2589419734292943/250000000000000000000000000000 : ℝ)*base77 + (1439862549957057/250000000000000000000000000000 : ℝ)*base80 + (18310942939/10000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14257/39062500000000000000 : ℝ)*base89 + (14257/39062500000000000000 : ℝ)*base91 + (14257/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1158_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s10_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344684433/10000000000 : ℝ)*x 0 + (-2223490577/10000000000 : ℝ)*x 1 + (2633023587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344684433/10000000000 : ℝ)^8351 ≤ (8720617540013/20000000000000 : ℝ)^6303 := by
    have hnat : (5344684433 : ℕ)^8351*20000000000000^6303 ≤ 8720617540013^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344684433 10000000000 8720617540013 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223490577/10000000000 : ℝ)^8351 ≤ (6820888903933/50000000000000 : ℝ)^6303 := by
    have hnat : (2223490577 : ℕ)^8351*50000000000000^6303 ≤ 6820888903933^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223490577 10000000000 6820888903933 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633023587/5000000000 : ℝ)^8351 ≤ (42755134465999/100000000000000 : ℝ)^6303 := by
    have hnat : (2633023587 : ℕ)^8351*100000000000000^6303 ≤ 42755134465999^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633023587 5000000000 42755134465999 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344684433/10000000000 : ℝ), (-2223490577/10000000000 : ℝ), (2633023587/5000000000 : ℝ)] ![(8720617540013/20000000000000 : ℝ), (6820888903933/50000000000000 : ℝ), (42755134465999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344684433/10000000000 : ℝ)|^8351 ≤ (8720617540013/20000000000000 : ℝ)^6303
        have hw : |(5344684433/10000000000 : ℝ)|=(5344684433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223490577/10000000000 : ℝ)|^8351 ≤ (6820888903933/50000000000000 : ℝ)^6303
        have hw : |(-2223490577/10000000000 : ℝ)|=(2223490577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633023587/5000000000 : ℝ)|^8351 ≤ (42755134465999/100000000000000 : ℝ)^6303
        have hw : |(2633023587/5000000000 : ℝ)|=(2633023587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s10_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269908021/1250000000 : ℝ)*x 0 + (329147829/625000000 : ℝ)*x 1 + (2696185753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269908021/1250000000 : ℝ)^8351 ≤ (1640269978107/12500000000000 : ℝ)^6303 := by
    have hnat : (269908021 : ℕ)^8351*12500000000000^6303 ≤ 1640269978107^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269908021 1250000000 1640269978107 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329147829/625000000 : ℝ)^8351 ≤ (42758556221593/100000000000000 : ℝ)^6303 := by
    have hnat : (329147829 : ℕ)^8351*100000000000000^6303 ≤ 42758556221593^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329147829 625000000 42758556221593 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696185753/5000000000 : ℝ)^8351 ≤ (22059641968857/50000000000000 : ℝ)^6303 := by
    have hnat : (2696185753 : ℕ)^8351*50000000000000^6303 ≤ 22059641968857^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696185753 5000000000 22059641968857 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269908021/1250000000 : ℝ), (329147829/625000000 : ℝ), (2696185753/5000000000 : ℝ)] ![(1640269978107/12500000000000 : ℝ), (42758556221593/100000000000000 : ℝ), (22059641968857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269908021/1250000000 : ℝ)|^8351 ≤ (1640269978107/12500000000000 : ℝ)^6303
        have hw : |(-269908021/1250000000 : ℝ)|=(269908021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329147829/625000000 : ℝ)|^8351 ≤ (42758556221593/100000000000000 : ℝ)^6303
        have hw : |(329147829/625000000 : ℝ)|=(329147829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696185753/5000000000 : ℝ)|^8351 ≤ (22059641968857/50000000000000 : ℝ)^6303
        have hw : |(2696185753/5000000000 : ℝ)|=(2696185753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s10_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062512139/2000000000 : ℝ)*x 0 + (-2097166501/10000000000 : ℝ)*x 1 + (539237143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062512139/2000000000 : ℝ)^8351 ≤ (43256201061577/100000000000000 : ℝ)^6303 := by
    have hnat : (1062512139 : ℕ)^8351*100000000000000^6303 ≤ 43256201061577^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062512139 2000000000 43256201061577 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097166501/10000000000 : ℝ)^8351 ≤ (12624515813437/100000000000000 : ℝ)^6303 := by
    have hnat : (2097166501 : ℕ)^8351*100000000000000^6303 ≤ 12624515813437^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097166501 10000000000 12624515813437 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539237143/1000000000 : ℝ)^8351 ≤ (22059641556927/50000000000000 : ℝ)^6303 := by
    have hnat : (539237143 : ℕ)^8351*50000000000000^6303 ≤ 22059641556927^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539237143 1000000000 22059641556927 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062512139/2000000000 : ℝ), (-2097166501/10000000000 : ℝ), (539237143/1000000000 : ℝ)] ![(43256201061577/100000000000000 : ℝ), (12624515813437/100000000000000 : ℝ), (22059641556927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062512139/2000000000 : ℝ)|^8351 ≤ (43256201061577/100000000000000 : ℝ)^6303
        have hw : |(1062512139/2000000000 : ℝ)|=(1062512139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097166501/10000000000 : ℝ)|^8351 ≤ (12624515813437/100000000000000 : ℝ)^6303
        have hw : |(-2097166501/10000000000 : ℝ)|=(2097166501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539237143/1000000000 : ℝ)|^8351 ≤ (22059641556927/50000000000000 : ℝ)^6303
        have hw : |(539237143/1000000000 : ℝ)|=(539237143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s10_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312560989/10000000000 : ℝ)*x 0 + (5392371279/10000000000 : ℝ)*x 1 + (-2097166307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312560989/10000000000 : ℝ)^8351 ≤ (43256204233211/100000000000000 : ℝ)^6303 := by
    have hnat : (5312560989 : ℕ)^8351*100000000000000^6303 ≤ 43256204233211^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312560989 10000000000 43256204233211 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392371279/10000000000 : ℝ)^8351 ≤ (22059640738487/50000000000000 : ℝ)^6303 := by
    have hnat : (5392371279 : ℕ)^8351*50000000000000^6303 ≤ 22059640738487^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392371279 10000000000 22059640738487 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097166307/10000000000 : ℝ)^8351 ≤ (1578064283267/12500000000000 : ℝ)^6303 := by
    have hnat : (2097166307 : ℕ)^8351*12500000000000^6303 ≤ 1578064283267^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097166307 10000000000 1578064283267 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312560989/10000000000 : ℝ), (5392371279/10000000000 : ℝ), (-2097166307/10000000000 : ℝ)] ![(43256204233211/100000000000000 : ℝ), (22059640738487/50000000000000 : ℝ), (1578064283267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312560989/10000000000 : ℝ)|^8351 ≤ (43256204233211/100000000000000 : ℝ)^6303
        have hw : |(5312560989/10000000000 : ℝ)|=(5312560989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392371279/10000000000 : ℝ)|^8351 ≤ (22059640738487/50000000000000 : ℝ)^6303
        have hw : |(5392371279/10000000000 : ℝ)|=(5392371279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097166307/10000000000 : ℝ)|^8351 ≤ (1578064283267/12500000000000 : ℝ)^6303
        have hw : |(-2097166307/10000000000 : ℝ)|=(2097166307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s10_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545304531/1250000000 : ℝ)*x 0 + (4489978853/10000000000 : ℝ)*x 1 + (423850601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545304531/1250000000 : ℝ)^8351 ≤ (33317177223677/100000000000000 : ℝ)^6303 := by
    have hnat : (545304531 : ℕ)^8351*100000000000000^6303 ≤ 33317177223677^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545304531 1250000000 33317177223677 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489978853/10000000000 : ℝ)^8351 ≤ (6922769864379/20000000000000 : ℝ)^6303 := by
    have hnat : (4489978853 : ℕ)^8351*20000000000000^6303 ≤ 6922769864379^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489978853 10000000000 6922769864379 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423850601/1000000000 : ℝ)^8351 ≤ (32068973441499/100000000000000 : ℝ)^6303 := by
    have hnat : (423850601 : ℕ)^8351*100000000000000^6303 ≤ 32068973441499^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423850601 1000000000 32068973441499 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545304531/1250000000 : ℝ), (4489978853/10000000000 : ℝ), (423850601/1000000000 : ℝ)] ![(33317177223677/100000000000000 : ℝ), (6922769864379/20000000000000 : ℝ), (32068973441499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545304531/1250000000 : ℝ)|^8351 ≤ (33317177223677/100000000000000 : ℝ)^6303
        have hw : |(545304531/1250000000 : ℝ)|=(545304531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489978853/10000000000 : ℝ)|^8351 ≤ (6922769864379/20000000000000 : ℝ)^6303
        have hw : |(4489978853/10000000000 : ℝ)|=(4489978853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423850601/1000000000 : ℝ)|^8351 ≤ (32068973441499/100000000000000 : ℝ)^6303
        have hw : |(423850601/1000000000 : ℝ)|=(423850601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (91/800 : ℝ) ^ (4175/1024 : ℝ) ≤ (1769635248953727/12500000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^4175 ≤ (1769635248953727/12500000000000000000 : ℝ)^1024 := by
      have hnat : (91 : ℕ)^4175*12500000000000000000^1024 ≤ 1769635248953727^1024*800^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 1769635248953727 12500000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (1769635248953727/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (3357049834838973/10000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^4175 ≤ (3357049834838973/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7029 : ℕ)^4175*10000000000000000000^1024 ≤ 3357049834838973^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 3357049834838973 10000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (3357049834838973/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251769635248953727/6250000000000000000 : ℝ) ≤ (1250086798223107/1250000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (6251769635248953727/6250000000000000000 : ℝ)^1024 ≤ (1250086798223107/1250000000000000 : ℝ)^4175 := by
      have hnat : (6251769635248953727 : ℕ)^1024*1250000000000000^4175 ≤ 1250086798223107^4175*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251769635248953727 6250000000000000000 1250086798223107 1250000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086798223107/1250000000000000 : ℝ)) (X := (6251769635248953727/6250000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023863790170009773/50000000000000000000 : ℝ) ≤ (200023408020279/200000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50023863790170009773/50000000000000000000 : ℝ)^1024 ≤ (200023408020279/200000000000000 : ℝ)^4175 := by
      have hnat : (50023863790170009773 : ℕ)^1024*200000000000000^4175 ≤ 200023408020279^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023863790170009773 50000000000000000000 200023408020279 200000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200023408020279/200000000000000 : ℝ)) (X := (50023863790170009773/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003357049834838973/5000000000000000000 : ℝ) ≤ (2500411604060761/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (5003357049834838973/5000000000000000000 : ℝ)^1024 ≤ (2500411604060761/2500000000000000 : ℝ)^4175 := by
      have hnat : (5003357049834838973 : ℕ)^1024*2500000000000000^4175 ≤ 2500411604060761^4175*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003357049834838973 5000000000000000000 2500411604060761 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500411604060761/2500000000000000 : ℝ)) (X := (5003357049834838973/5000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1769635248953727/12500000000000000000 : ℝ) ≤ ((6705258422649720037/6707500000000000000 : ℝ)+2*(238007614547/134150000000000 : ℝ)*(91/800 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (6705258422649720037/6707500000000000000 : ℝ)+2*(238007614547/134150000000000 : ℝ)*(91/800 : ℝ)=(1250086798223107/1250000000000000 : ℝ) by norm_num, show 1+2*(1769635248953727/12500000000000000000 : ℝ)=(6251769635248953727/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3357049834838973/10000000000000000000 : ℝ)+(1769635248953727/12500000000000000000 : ℝ) ≤ ((6705258422649720037/6707500000000000000 : ℝ)+(238007614547/134150000000000 : ℝ)*((7029/50000 : ℝ)+(91/800 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (6705258422649720037/6707500000000000000 : ℝ)+(238007614547/134150000000000 : ℝ)*((7029/50000 : ℝ)+(91/800 : ℝ))=(200023408020279/200000000000000 : ℝ) by norm_num, show 1+(3357049834838973/10000000000000000000 : ℝ)+(1769635248953727/12500000000000000000 : ℝ)=(50023863790170009773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3357049834838973/10000000000000000000 : ℝ) ≤ ((6705258422649720037/6707500000000000000 : ℝ)+2*(238007614547/134150000000000 : ℝ)*(7029/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (6705258422649720037/6707500000000000000 : ℝ)+2*(238007614547/134150000000000 : ℝ)*(7029/50000 : ℝ)=(2500411604060761/2500000000000000 : ℝ) by norm_num, show 1+2*(3357049834838973/10000000000000000000 : ℝ)=(5003357049834838973/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6705258422649720037/6707500000000000000 : ℝ)*(X 1 0+X 2 0)+(238007614547/134150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (6705258422649720037/6707500000000000000 : ℝ)) (alpha := (238007614547/134150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6705258422649720037/6707500000000000000 : ℝ)*(X 0 1+X 2 1)+(238007614547/134150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (6705258422649720037/6707500000000000000 : ℝ)) (alpha := (238007614547/134150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6705258422649720037/6707500000000000000 : ℝ)*(X 0 2+X 1 2)+(238007614547/134150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (6705258422649720037/6707500000000000000 : ℝ)) (alpha := (238007614547/134150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344684433/10000000000 : ℝ)*X 1 0+(-2223490577/10000000000 : ℝ)*X 1 1+(2633023587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s10_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-269908021/1250000000 : ℝ)*X 0 0+(329147829/625000000 : ℝ)*X 0 1+(2696185753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s10_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1062512139/2000000000 : ℝ)*X 1 0+(-2097166501/10000000000 : ℝ)*X 1 1+(539237143/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s10_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312560989/10000000000 : ℝ)*X 2 0+(5392371279/10000000000 : ℝ)*X 2 1+(-2097166307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s10_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((545304531/1250000000 : ℝ)*X 0 0+(4489978853/10000000000 : ℝ)*X 0 1+(423850601/1000000000 : ℝ)*X 0 2+(545304531/1250000000 : ℝ)*X 1 0+(4489978853/10000000000 : ℝ)*X 1 1+(423850601/1000000000 : ℝ)*X 1 2+(545304531/1250000000 : ℝ)*X 2 0+(4489978853/10000000000 : ℝ)*X 2 1+(423850601/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s10_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43193832981266055183927423/13415000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13623039/50000000000000 : ℝ)*(base15) + (3703103/50000000000000 : ℝ)*(lower1) + (54701563/25000000000000 : ℝ)*(lower2) + (84326313/100000000000000 : ℝ)*(lower3) + (314481/25000000000000 : ℝ)*(upper4) + (1544593/50000000000000 : ℝ)*(lower5) + (238254078423731/4000000000000 : ℝ)*(major0) + (238254078423731/4000000000000 : ℝ)*(major1) + (238254078423731/4000000000000 : ℝ)*(major2) + (151469811/100000000000000 : ℝ)*(sp0) + (7936128835660253/100000000000000 : ℝ)*(sp1) + (1984032164236091/25000000000000 : ℝ)*(sp2) + (7936128835660253/100000000000000 : ℝ)*(sp3) + (1988287489099539/50000000000000 : ℝ)*(sp4) + (1988287489099539/50000000000000 : ℝ)*(f.failure) + (7936128835660253/100000000000000 : ℝ)*(f.sum) + (2679987872343/53660000000000000000000000 : ℝ)*base66 + (315185939266731953/26830000000000000000000000000000 : ℝ)*base68 + (200701268730491953/26830000000000000000000000000000 : ℝ)*base70 + (450018901236361953/26830000000000000000000000000000 : ℝ)*base72 + (12946220357739/2683000000000000000000000000 : ℝ)*base74 + (59093430647771953/26830000000000000000000000000000 : ℝ)*base76 + (563680039571781953/26830000000000000000000000000000 : ℝ)*base78 + (271571676026581953/26830000000000000000000000000000 : ℝ)*base80 + (15105195272877/2683000000000000000000000000 : ℝ)*base82 + (105229/19531250000000000000 : ℝ)*base90 + (105229/19531250000000000000 : ℝ)*base92 + (105229/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_box_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032903999/10000000000 : ℝ)*x 0 + (1344018957/2500000000 : ℝ)*x 1 + (5376077267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032903999/10000000000 : ℝ)^8351 ≤ (37857943229/312500000000 : ℝ)^6303 := by
    have hnat : (2032903999 : ℕ)^8351*312500000000^6303 ≤ 37857943229^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032903999 10000000000 37857943229 312500000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344018957/2500000000 : ℝ)^8351 ≤ (21971360643009/50000000000000 : ℝ)^6303 := by
    have hnat : (1344018957 : ℕ)^8351*50000000000000^6303 ≤ 21971360643009^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344018957 2500000000 21971360643009 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376077267/10000000000 : ℝ)^8351 ≤ (686605263591/1562500000000 : ℝ)^6303 := by
    have hnat : (5376077267 : ℕ)^8351*1562500000000^6303 ≤ 686605263591^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376077267 10000000000 686605263591 1562500000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032903999/10000000000 : ℝ), (1344018957/2500000000 : ℝ), (5376077267/10000000000 : ℝ)] ![(37857943229/312500000000 : ℝ), (21971360643009/50000000000000 : ℝ), (686605263591/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032903999/10000000000 : ℝ)|^8351 ≤ (37857943229/312500000000 : ℝ)^6303
        have hw : |(-2032903999/10000000000 : ℝ)|=(2032903999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344018957/2500000000 : ℝ)|^8351 ≤ (21971360643009/50000000000000 : ℝ)^6303
        have hw : |(1344018957/2500000000 : ℝ)|=(1344018957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376077267/10000000000 : ℝ)|^8351 ≤ (686605263591/1562500000000 : ℝ)^6303
        have hw : |(5376077267/10000000000 : ℝ)|=(5376077267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059226563/2000000000 : ℝ)*x 0 + (-2141360349/10000000000 : ℝ)*x 1 + (2688038523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059226563/2000000000 : ℝ)^8351 ≤ (21539534172729/50000000000000 : ℝ)^6303 := by
    have hnat : (1059226563 : ℕ)^8351*50000000000000^6303 ≤ 21539534172729^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059226563 2000000000 21539534172729 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141360349/10000000000 : ℝ)^8351 ≤ (12978197158773/100000000000000 : ℝ)^6303 := by
    have hnat : (2141360349 : ℕ)^8351*100000000000000^6303 ≤ 12978197158773^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141360349 10000000000 12978197158773 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688038523/5000000000 : ℝ)^8351 ≤ (43942734476481/100000000000000 : ℝ)^6303 := by
    have hnat : (2688038523 : ℕ)^8351*100000000000000^6303 ≤ 43942734476481^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688038523 5000000000 43942734476481 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059226563/2000000000 : ℝ), (-2141360349/10000000000 : ℝ), (2688038523/5000000000 : ℝ)] ![(21539534172729/50000000000000 : ℝ), (12978197158773/100000000000000 : ℝ), (43942734476481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059226563/2000000000 : ℝ)|^8351 ≤ (21539534172729/50000000000000 : ℝ)^6303
        have hw : |(1059226563/2000000000 : ℝ)|=(1059226563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141360349/10000000000 : ℝ)|^8351 ≤ (12978197158773/100000000000000 : ℝ)^6303
        have hw : |(-2141360349/10000000000 : ℝ)|=(2141360349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688038523/5000000000 : ℝ)|^8351 ≤ (43942734476481/100000000000000 : ℝ)^6303
        have hw : |(2688038523/5000000000 : ℝ)|=(2688038523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1324033097/2500000000 : ℝ)*x 0 + (5376076501/10000000000 : ℝ)*x 1 + (-2141361659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324033097/2500000000 : ℝ)^8351 ≤ (5384882967959/12500000000000 : ℝ)^6303 := by
    have hnat : (1324033097 : ℕ)^8351*12500000000000^6303 ≤ 5384882967959^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324033097 2500000000 5384882967959 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376076501/10000000000 : ℝ)^8351 ≤ (5492841071793/12500000000000 : ℝ)^6303 := by
    have hnat : (5376076501 : ℕ)^8351*12500000000000^6303 ≤ 5492841071793^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376076501 10000000000 5492841071793 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141361659/10000000000 : ℝ)^8351 ≤ (20278449497/156250000000 : ℝ)^6303 := by
    have hnat : (2141361659 : ℕ)^8351*156250000000^6303 ≤ 20278449497^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141361659 10000000000 20278449497 156250000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324033097/2500000000 : ℝ), (5376076501/10000000000 : ℝ), (-2141361659/10000000000 : ℝ)] ![(5384882967959/12500000000000 : ℝ), (5492841071793/12500000000000 : ℝ), (20278449497/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324033097/2500000000 : ℝ)|^8351 ≤ (5384882967959/12500000000000 : ℝ)^6303
        have hw : |(1324033097/2500000000 : ℝ)|=(1324033097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376076501/10000000000 : ℝ)|^8351 ≤ (5492841071793/12500000000000 : ℝ)^6303
        have hw : |(5376076501/10000000000 : ℝ)|=(5376076501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141361659/10000000000 : ℝ)|^8351 ≤ (20278449497/156250000000 : ℝ)^6303
        have hw : |(-2141361659/10000000000 : ℝ)|=(2141361659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4469792853/10000000000 : ℝ)*x 0 + (4310840199/10000000000 : ℝ)*x 1 + (2155419961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469792853/10000000000 : ℝ)^8351 ≤ (6881563964817/20000000000000 : ℝ)^6303 := by
    have hnat : (4469792853 : ℕ)^8351*20000000000000^6303 ≤ 6881563964817^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469792853 10000000000 6881563964817 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310840199/10000000000 : ℝ)^8351 ≤ (3279609147757/10000000000000 : ℝ)^6303 := by
    have hnat : (4310840199 : ℕ)^8351*10000000000000^6303 ≤ 3279609147757^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310840199 10000000000 3279609147757 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155419961/5000000000 : ℝ)^8351 ≤ (3279608868547/10000000000000 : ℝ)^6303 := by
    have hnat : (2155419961 : ℕ)^8351*10000000000000^6303 ≤ 3279608868547^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155419961 5000000000 3279608868547 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469792853/10000000000 : ℝ), (4310840199/10000000000 : ℝ), (2155419961/5000000000 : ℝ)] ![(6881563964817/20000000000000 : ℝ), (3279609147757/10000000000000 : ℝ), (3279608868547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469792853/10000000000 : ℝ)|^8351 ≤ (6881563964817/20000000000000 : ℝ)^6303
        have hw : |(4469792853/10000000000 : ℝ)|=(4469792853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310840199/10000000000 : ℝ)|^8351 ≤ (3279609147757/10000000000000 : ℝ)^6303
        have hw : |(4310840199/10000000000 : ℝ)|=(4310840199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2155419961/5000000000 : ℝ)|^8351 ≤ (3279608868547/10000000000000 : ℝ)^6303
        have hw : |(2155419961/5000000000 : ℝ)|=(2155419961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2287004659/10000000000 : ℝ)*x 0 + (2640672753/5000000000 : ℝ)*x 1 + (5281344807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2287004659/10000000000 : ℝ)^8351 ≤ (7080226169587/50000000000000 : ℝ)^6303 := by
    have hnat : (2287004659 : ℕ)^8351*50000000000000^6303 ≤ 7080226169587^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287004659 10000000000 7080226169587 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640672753/5000000000 : ℝ)^8351 ≤ (42919777583291/100000000000000 : ℝ)^6303 := by
    have hnat : (2640672753 : ℕ)^8351*100000000000000^6303 ≤ 42919777583291^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640672753 5000000000 42919777583291 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281344807/10000000000 : ℝ)^8351 ≤ (10729942514249/25000000000000 : ℝ)^6303 := by
    have hnat : (5281344807 : ℕ)^8351*25000000000000^6303 ≤ 10729942514249^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281344807 10000000000 10729942514249 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2287004659/10000000000 : ℝ), (2640672753/5000000000 : ℝ), (5281344807/10000000000 : ℝ)] ![(7080226169587/50000000000000 : ℝ), (42919777583291/100000000000000 : ℝ), (10729942514249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2287004659/10000000000 : ℝ)|^8351 ≤ (7080226169587/50000000000000 : ℝ)^6303
        have hw : |(-2287004659/10000000000 : ℝ)|=(2287004659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640672753/5000000000 : ℝ)|^8351 ≤ (42919777583291/100000000000000 : ℝ)^6303
        have hw : |(2640672753/5000000000 : ℝ)|=(2640672753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281344807/10000000000 : ℝ)|^8351 ≤ (10729942514249/25000000000000 : ℝ)^6303
        have hw : |(5281344807/10000000000 : ℝ)|=(5281344807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363036421/10000000000 : ℝ)*x 0 + (-2178672777/10000000000 : ℝ)*x 1 + (1056269029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363036421/10000000000 : ℝ)^8351 ≤ (21900782646441/50000000000000 : ℝ)^6303 := by
    have hnat : (5363036421 : ℕ)^8351*50000000000000^6303 ≤ 21900782646441^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363036421 10000000000 21900782646441 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178672777/10000000000 : ℝ)^8351 ≤ (13278660996427/100000000000000 : ℝ)^6303 := by
    have hnat : (2178672777 : ℕ)^8351*100000000000000^6303 ≤ 13278660996427^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178672777 10000000000 13278660996427 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056269029/2000000000 : ℝ)^8351 ≤ (42919773696321/100000000000000 : ℝ)^6303 := by
    have hnat : (1056269029 : ℕ)^8351*100000000000000^6303 ≤ 42919773696321^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056269029 2000000000 42919773696321 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363036421/10000000000 : ℝ), (-2178672777/10000000000 : ℝ), (1056269029/2000000000 : ℝ)] ![(21900782646441/50000000000000 : ℝ), (13278660996427/100000000000000 : ℝ), (42919773696321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363036421/10000000000 : ℝ)|^8351 ≤ (21900782646441/50000000000000 : ℝ)^6303
        have hw : |(5363036421/10000000000 : ℝ)|=(5363036421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178672777/10000000000 : ℝ)|^8351 ≤ (13278660996427/100000000000000 : ℝ)^6303
        have hw : |(-2178672777/10000000000 : ℝ)|=(2178672777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056269029/2000000000 : ℝ)|^8351 ≤ (42919773696321/100000000000000 : ℝ)^6303
        have hw : |(1056269029/2000000000 : ℝ)|=(1056269029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363036519/10000000000 : ℝ)*x 0 + (1320336243/2500000000 : ℝ)*x 1 + (-544668219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363036519/10000000000 : ℝ)^8351 ≤ (21900783176673/50000000000000 : ℝ)^6303 := by
    have hnat : (5363036519 : ℕ)^8351*50000000000000^6303 ≤ 21900783176673^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363036519 10000000000 21900783176673 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320336243/2500000000 : ℝ)^8351 ≤ (4291977183359/10000000000000 : ℝ)^6303 := by
    have hnat : (1320336243 : ℕ)^8351*10000000000000^6303 ≤ 4291977183359^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320336243 2500000000 4291977183359 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544668219/2500000000 : ℝ)^8351 ≤ (414958181121/3125000000000 : ℝ)^6303 := by
    have hnat : (544668219 : ℕ)^8351*3125000000000^6303 ≤ 414958181121^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544668219 2500000000 414958181121 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363036519/10000000000 : ℝ), (1320336243/2500000000 : ℝ), (-544668219/2500000000 : ℝ)] ![(21900783176673/50000000000000 : ℝ), (4291977183359/10000000000000 : ℝ), (414958181121/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363036519/10000000000 : ℝ)|^8351 ≤ (21900783176673/50000000000000 : ℝ)^6303
        have hw : |(5363036519/10000000000 : ℝ)|=(5363036519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320336243/2500000000 : ℝ)|^8351 ≤ (4291977183359/10000000000000 : ℝ)^6303
        have hw : |(1320336243/2500000000 : ℝ)|=(1320336243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544668219/2500000000 : ℝ)|^8351 ≤ (414958181121/3125000000000 : ℝ)^6303
        have hw : |(-544668219/2500000000 : ℝ)|=(544668219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4254691643/10000000000 : ℝ)*x 0 + (1104592423/2500000000 : ℝ)*x 1 + (4418370209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254691643/10000000000 : ℝ)^8351 ≤ (16115663580061/50000000000000 : ℝ)^6303 := by
    have hnat : (4254691643 : ℕ)^8351*50000000000000^6303 ≤ 16115663580061^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254691643 10000000000 16115663580061 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104592423/2500000000 : ℝ)^8351 ≤ (33884333783023/100000000000000 : ℝ)^6303 := by
    have hnat : (1104592423 : ℕ)^8351*100000000000000^6303 ≤ 33884333783023^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104592423 2500000000 33884333783023 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418370209/10000000000 : ℝ)^8351 ≤ (33884339036159/100000000000000 : ℝ)^6303 := by
    have hnat : (4418370209 : ℕ)^8351*100000000000000^6303 ≤ 33884339036159^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418370209 10000000000 33884339036159 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254691643/10000000000 : ℝ), (1104592423/2500000000 : ℝ), (4418370209/10000000000 : ℝ)] ![(16115663580061/50000000000000 : ℝ), (33884333783023/100000000000000 : ℝ), (33884339036159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254691643/10000000000 : ℝ)|^8351 ≤ (16115663580061/50000000000000 : ℝ)^6303
        have hw : |(4254691643/10000000000 : ℝ)|=(4254691643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104592423/2500000000 : ℝ)|^8351 ≤ (33884333783023/100000000000000 : ℝ)^6303
        have hw : |(1104592423/2500000000 : ℝ)|=(1104592423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418370209/10000000000 : ℝ)|^8351 ≤ (33884339036159/100000000000000 : ℝ)^6303
        have hw : |(4418370209/10000000000 : ℝ)|=(4418370209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_8 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1116925017/5000000000 : ℝ)*x 0 + (5216887907/10000000000 : ℝ)*x 1 + (1077137107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116925017/5000000000 : ℝ)^8351 ≤ (13726051516901/100000000000000 : ℝ)^6303 := by
    have hnat : (1116925017 : ℕ)^8351*100000000000000^6303 ≤ 13726051516901^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116925017 5000000000 13726051516901 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216887907/10000000000 : ℝ)^8351 ≤ (10556781902719/25000000000000 : ℝ)^6303 := by
    have hnat : (5216887907 : ℕ)^8351*25000000000000^6303 ≤ 10556781902719^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216887907 10000000000 10556781902719 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077137107/2000000000 : ℝ)^8351 ≤ (5505852607011/12500000000000 : ℝ)^6303 := by
    have hnat : (1077137107 : ℕ)^8351*12500000000000^6303 ≤ 5505852607011^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077137107 2000000000 5505852607011 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1116925017/5000000000 : ℝ), (5216887907/10000000000 : ℝ), (1077137107/2000000000 : ℝ)] ![(13726051516901/100000000000000 : ℝ), (10556781902719/25000000000000 : ℝ), (5505852607011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1116925017/5000000000 : ℝ)|^8351 ≤ (13726051516901/100000000000000 : ℝ)^6303
        have hw : |(-1116925017/5000000000 : ℝ)|=(1116925017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216887907/10000000000 : ℝ)|^8351 ≤ (10556781902719/25000000000000 : ℝ)^6303
        have hw : |(5216887907/10000000000 : ℝ)|=(5216887907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077137107/2000000000 : ℝ)|^8351 ≤ (5505852607011/12500000000000 : ℝ)^6303
        have hw : |(1077137107/2000000000 : ℝ)|=(1077137107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_9 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057868611/2000000000 : ℝ)*x 0 + (-1068753801/5000000000 : ℝ)*x 1 + (134642139/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057868611/2000000000 : ℝ)^8351 ≤ (43005910224179/100000000000000 : ℝ)^6303 := by
    have hnat : (1057868611 : ℕ)^8351*100000000000000^6303 ≤ 43005910224179^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057868611 2000000000 43005910224179 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068753801/5000000000 : ℝ)^8351 ≤ (12947268629933/100000000000000 : ℝ)^6303 := by
    have hnat : (1068753801 : ℕ)^8351*100000000000000^6303 ≤ 12947268629933^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068753801 5000000000 12947268629933 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134642139/250000000 : ℝ)^8351 ≤ (8809364225397/20000000000000 : ℝ)^6303 := by
    have hnat : (134642139 : ℕ)^8351*20000000000000^6303 ≤ 8809364225397^6303*250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134642139 250000000 8809364225397 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057868611/2000000000 : ℝ), (-1068753801/5000000000 : ℝ), (134642139/250000000 : ℝ)] ![(43005910224179/100000000000000 : ℝ), (12947268629933/100000000000000 : ℝ), (8809364225397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057868611/2000000000 : ℝ)|^8351 ≤ (43005910224179/100000000000000 : ℝ)^6303
        have hw : |(1057868611/2000000000 : ℝ)|=(1057868611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068753801/5000000000 : ℝ)|^8351 ≤ (12947268629933/100000000000000 : ℝ)^6303
        have hw : |(-1068753801/5000000000 : ℝ)|=(1068753801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134642139/250000000 : ℝ)|^8351 ≤ (8809364225397/20000000000000 : ℝ)^6303
        have hw : |(134642139/250000000 : ℝ)|=(134642139/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_10 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322335733/2500000000 : ℝ)*x 0 + (5385685727/10000000000 : ℝ)*x 1 + (-1068753771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322335733/2500000000 : ℝ)^8351 ≤ (21502954449579/50000000000000 : ℝ)^6303 := by
    have hnat : (1322335733 : ℕ)^8351*50000000000000^6303 ≤ 21502954449579^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322335733 2500000000 21502954449579 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385685727/10000000000 : ℝ)^8351 ≤ (44046822936579/100000000000000 : ℝ)^6303 := by
    have hnat : (5385685727 : ℕ)^8351*100000000000000^6303 ≤ 44046822936579^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385685727 10000000000 44046822936579 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068753771/5000000000 : ℝ)^8351 ≤ (6473634074207/50000000000000 : ℝ)^6303 := by
    have hnat : (1068753771 : ℕ)^8351*50000000000000^6303 ≤ 6473634074207^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068753771 5000000000 6473634074207 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322335733/2500000000 : ℝ), (5385685727/10000000000 : ℝ), (-1068753771/5000000000 : ℝ)] ![(21502954449579/50000000000000 : ℝ), (44046822936579/100000000000000 : ℝ), (6473634074207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322335733/2500000000 : ℝ)|^8351 ≤ (21502954449579/50000000000000 : ℝ)^6303
        have hw : |(1322335733/2500000000 : ℝ)|=(1322335733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385685727/10000000000 : ℝ)|^8351 ≤ (44046822936579/100000000000000 : ℝ)^6303
        have hw : |(5385685727/10000000000 : ℝ)|=(5385685727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068753771/5000000000 : ℝ)|^8351 ≤ (6473634074207/50000000000000 : ℝ)^6303
        have hw : |(-1068753771/5000000000 : ℝ)|=(1068753771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_11 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (449133899/1000000000 : ℝ)*x 0 + (4299926463/10000000000 : ℝ)*x 1 + (429992649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449133899/1000000000 : ℝ)^8351 ≤ (6925548494901/20000000000000 : ℝ)^6303 := by
    have hnat : (449133899 : ℕ)^8351*20000000000000^6303 ≤ 6925548494901^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449133899 1000000000 6925548494901 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299926463/10000000000 : ℝ)^8351 ≤ (32686128619409/100000000000000 : ℝ)^6303 := by
    have hnat : (4299926463 : ℕ)^8351*100000000000000^6303 ≤ 32686128619409^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299926463 10000000000 32686128619409 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429992649/1000000000 : ℝ)^8351 ≤ (1634306444567/5000000000000 : ℝ)^6303 := by
    have hnat : (429992649 : ℕ)^8351*5000000000000^6303 ≤ 1634306444567^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429992649 1000000000 1634306444567 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449133899/1000000000 : ℝ), (4299926463/10000000000 : ℝ), (429992649/1000000000 : ℝ)] ![(6925548494901/20000000000000 : ℝ), (32686128619409/100000000000000 : ℝ), (1634306444567/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449133899/1000000000 : ℝ)|^8351 ≤ (6925548494901/20000000000000 : ℝ)^6303
        have hw : |(449133899/1000000000 : ℝ)|=(449133899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4299926463/10000000000 : ℝ)|^8351 ≤ (32686128619409/100000000000000 : ℝ)^6303
        have hw : |(4299926463/10000000000 : ℝ)|=(4299926463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429992649/1000000000 : ℝ)|^8351 ≤ (1634306444567/5000000000000 : ℝ)^6303
        have hw : |(429992649/1000000000 : ℝ)|=(429992649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_12 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-260796009/1250000000 : ℝ)*x 0 + (5439267543/10000000000 : ℝ)*x 1 + (329581253/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260796009/1250000000 : ℝ)^8351 ≤ (6269231041791/50000000000000 : ℝ)^6303 := by
    have hnat : (260796009 : ℕ)^8351*50000000000000^6303 ≤ 6269231041791^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260796009 1250000000 6269231041791 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439267543/10000000000 : ℝ)^8351 ≤ (22314183093137/50000000000000 : ℝ)^6303 := by
    have hnat : (5439267543 : ℕ)^8351*50000000000000^6303 ≤ 22314183093137^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439267543 10000000000 22314183093137 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329581253/625000000 : ℝ)^8351 ≤ (2677073232473/6250000000000 : ℝ)^6303 := by
    have hnat : (329581253 : ℕ)^8351*6250000000000^6303 ≤ 2677073232473^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329581253 625000000 2677073232473 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260796009/1250000000 : ℝ), (5439267543/10000000000 : ℝ), (329581253/625000000 : ℝ)] ![(6269231041791/50000000000000 : ℝ), (22314183093137/50000000000000 : ℝ), (2677073232473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260796009/1250000000 : ℝ)|^8351 ≤ (6269231041791/50000000000000 : ℝ)^6303
        have hw : |(-260796009/1250000000 : ℝ)|=(260796009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439267543/10000000000 : ℝ)|^8351 ≤ (22314183093137/50000000000000 : ℝ)^6303
        have hw : |(5439267543/10000000000 : ℝ)|=(5439267543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329581253/625000000 : ℝ)|^8351 ≤ (2677073232473/6250000000000 : ℝ)^6303
        have hw : |(329581253/625000000 : ℝ)|=(329581253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_13 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368716223/10000000000 : ℝ)*x 0 + (-2181784229/10000000000 : ℝ)*x 1 + (1054659981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368716223/10000000000 : ℝ)^8351 ≤ (8772607475951/20000000000000 : ℝ)^6303 := by
    have hnat : (5368716223 : ℕ)^8351*20000000000000^6303 ≤ 8772607475951^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368716223 10000000000 8772607475951 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181784229/10000000000 : ℝ)^8351 ≤ (13303792430961/100000000000000 : ℝ)^6303 := by
    have hnat : (2181784229 : ℕ)^8351*100000000000000^6303 ≤ 13303792430961^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181784229 10000000000 13303792430961 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054659981/2000000000 : ℝ)^8351 ≤ (42833170180617/100000000000000 : ℝ)^6303 := by
    have hnat : (1054659981 : ℕ)^8351*100000000000000^6303 ≤ 42833170180617^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054659981 2000000000 42833170180617 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368716223/10000000000 : ℝ), (-2181784229/10000000000 : ℝ), (1054659981/2000000000 : ℝ)] ![(8772607475951/20000000000000 : ℝ), (13303792430961/100000000000000 : ℝ), (42833170180617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368716223/10000000000 : ℝ)|^8351 ≤ (8772607475951/20000000000000 : ℝ)^6303
        have hw : |(5368716223/10000000000 : ℝ)|=(5368716223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181784229/10000000000 : ℝ)|^8351 ≤ (13303792430961/100000000000000 : ℝ)^6303
        have hw : |(-2181784229/10000000000 : ℝ)|=(2181784229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054659981/2000000000 : ℝ)|^8351 ≤ (42833170180617/100000000000000 : ℝ)^6303
        have hw : |(1054659981/2000000000 : ℝ)|=(1054659981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_14 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342179121/2500000000 : ℝ)*x 0 + (20598827/39062500 : ℝ)*x 1 + (-272723017/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342179121/2500000000 : ℝ)^8351 ≤ (1754521608201/4000000000000 : ℝ)^6303 := by
    have hnat : (1342179121 : ℕ)^8351*4000000000000^6303 ≤ 1754521608201^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342179121 2500000000 1754521608201 4000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20598827/39062500 : ℝ)^8351 ≤ (4283316810357/10000000000000 : ℝ)^6303 := by
    have hnat : (20598827 : ℕ)^8351*10000000000000^6303 ≤ 4283316810357^6303*39062500^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20598827 39062500 4283316810357 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272723017/1250000000 : ℝ)^8351 ≤ (13303791679619/100000000000000 : ℝ)^6303 := by
    have hnat : (272723017 : ℕ)^8351*100000000000000^6303 ≤ 13303791679619^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272723017 1250000000 13303791679619 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342179121/2500000000 : ℝ), (20598827/39062500 : ℝ), (-272723017/1250000000 : ℝ)] ![(1754521608201/4000000000000 : ℝ), (4283316810357/10000000000000 : ℝ), (13303791679619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342179121/2500000000 : ℝ)|^8351 ≤ (1754521608201/4000000000000 : ℝ)^6303
        have hw : |(1342179121/2500000000 : ℝ)|=(1342179121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20598827/39062500 : ℝ)|^8351 ≤ (4283316810357/10000000000000 : ℝ)^6303
        have hw : |(20598827/39062500 : ℝ)|=(20598827/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272723017/1250000000 : ℝ)|^8351 ≤ (13303791679619/100000000000000 : ℝ)^6303
        have hw : |(-272723017/1250000000 : ℝ)|=(272723017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_box_15 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4236192803/10000000000 : ℝ)*x 0 + (4427497211/10000000000 : ℝ)*x 1 + (276718561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236192803/10000000000 : ℝ)^8351 ≤ (16022893358129/50000000000000 : ℝ)^6303 := by
    have hnat : (4236192803 : ℕ)^8351*50000000000000^6303 ≤ 16022893358129^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236192803 10000000000 16022893358129 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4427497211/10000000000 : ℝ)^8351 ≤ (6795421565349/20000000000000 : ℝ)^6303 := by
    have hnat : (4427497211 : ℕ)^8351*20000000000000^6303 ≤ 6795421565349^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427497211 10000000000 6795421565349 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276718561/625000000 : ℝ)^8351 ≤ (16988552718677/50000000000000 : ℝ)^6303 := by
    have hnat : (276718561 : ℕ)^8351*50000000000000^6303 ≤ 16988552718677^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276718561 625000000 16988552718677 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236192803/10000000000 : ℝ), (4427497211/10000000000 : ℝ), (276718561/625000000 : ℝ)] ![(16022893358129/50000000000000 : ℝ), (6795421565349/20000000000000 : ℝ), (16988552718677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236192803/10000000000 : ℝ)|^8351 ≤ (16022893358129/50000000000000 : ℝ)^6303
        have hw : |(4236192803/10000000000 : ℝ)|=(4236192803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4427497211/10000000000 : ℝ)|^8351 ≤ (6795421565349/20000000000000 : ℝ)^6303
        have hw : |(4427497211/10000000000 : ℝ)|=(4427497211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276718561/625000000 : ℝ)|^8351 ≤ (16988552718677/50000000000000 : ℝ)^6303
        have hw : |(276718561/625000000 : ℝ)|=(276718561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    -(62233/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59311/100000 : ℝ) ∧ (79857/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2079/2500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (4175/1024 : ℝ) ≤ (1769635248953727/12500000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^4175 ≤ (1769635248953727/12500000000000000000 : ℝ)^1024 := by
      have hnat : (91 : ℕ)^4175*12500000000000000000^1024 ≤ 1769635248953727^1024*800^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 1769635248953727 12500000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (1769635248953727/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (1342430527403467/4000000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^4175 ≤ (1342430527403467/4000000000000000000 : ℝ)^1024 := by
      have hnat : (14057 : ℕ)^4175*4000000000000000000^1024 ≤ 1342430527403467^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 1342430527403467 4000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (1342430527403467/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251769635248953727/6250000000000000000 : ℝ) ≤ (1250086798223107/1250000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (6251769635248953727/6250000000000000000 : ℝ)^1024 ≤ (1250086798223107/1250000000000000 : ℝ)^4175 := by
      have hnat : (6251769635248953727 : ℕ)^1024*1250000000000000^4175 ≤ 1250086798223107^4175*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251769635248953727 6250000000000000000 1250086798223107 1250000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086798223107/1250000000000000 : ℝ)) (X := (6251769635248953727/6250000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047717845176716491/100000000000000000000 : ℝ) ≤ (1000117016232609/1000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (100047717845176716491/100000000000000000000 : ℝ)^1024 ≤ (1000117016232609/1000000000000000 : ℝ)^4175 := by
      have hnat : (100047717845176716491 : ℕ)^1024*1000000000000000^4175 ≤ 1000117016232609^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047717845176716491 100000000000000000000 1000117016232609 1000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000117016232609/1000000000000000 : ℝ)) (X := (100047717845176716491/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001342430527403467/2000000000000000000 : ℝ) ≤ (2500411484716831/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (2001342430527403467/2000000000000000000 : ℝ)^1024 ≤ (2500411484716831/2500000000000000 : ℝ)^4175 := by
      have hnat : (2001342430527403467 : ℕ)^1024*2500000000000000^4175 ≤ 2500411484716831^4175*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001342430527403467 2000000000000000000 2500411484716831 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500411484716831/2500000000000000 : ℝ)) (X := (2001342430527403467/2000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1769635248953727/12500000000000000000 : ℝ) ≤ ((6702759606590477573/6705000000000000000 : ℝ)+2*(237888270617/134100000000000 : ℝ)*(91/800 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (6702759606590477573/6705000000000000000 : ℝ)+2*(237888270617/134100000000000 : ℝ)*(91/800 : ℝ)=(1250086798223107/1250000000000000 : ℝ) by norm_num, show 1+2*(1769635248953727/12500000000000000000 : ℝ)=(6251769635248953727/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1342430527403467/4000000000000000000 : ℝ)+(1769635248953727/12500000000000000000 : ℝ) ≤ ((6702759606590477573/6705000000000000000 : ℝ)+(237888270617/134100000000000 : ℝ)*((14057/100000 : ℝ)+(91/800 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (6702759606590477573/6705000000000000000 : ℝ)+(237888270617/134100000000000 : ℝ)*((14057/100000 : ℝ)+(91/800 : ℝ))=(1000117016232609/1000000000000000 : ℝ) by norm_num, show 1+(1342430527403467/4000000000000000000 : ℝ)+(1769635248953727/12500000000000000000 : ℝ)=(100047717845176716491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1342430527403467/4000000000000000000 : ℝ) ≤ ((6702759606590477573/6705000000000000000 : ℝ)+2*(237888270617/134100000000000 : ℝ)*(14057/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (6702759606590477573/6705000000000000000 : ℝ)+2*(237888270617/134100000000000 : ℝ)*(14057/100000 : ℝ)=(2500411484716831/2500000000000000 : ℝ) by norm_num, show 1+2*(1342430527403467/4000000000000000000 : ℝ)=(2001342430527403467/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6702759606590477573/6705000000000000000 : ℝ)*(X 1 0+X 2 0)+(237888270617/134100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6702759606590477573/6705000000000000000 : ℝ)) (alpha := (237888270617/134100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6702759606590477573/6705000000000000000 : ℝ)*(X 0 1+X 2 1)+(237888270617/134100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6702759606590477573/6705000000000000000 : ℝ)) (alpha := (237888270617/134100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6702759606590477573/6705000000000000000 : ℝ)*(X 0 2+X 1 2)+(237888270617/134100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6702759606590477573/6705000000000000000 : ℝ)) (alpha := (237888270617/134100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2032903999/10000000000 : ℝ)*X 0 0+(1344018957/2500000000 : ℝ)*X 0 1+(5376077267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059226563/2000000000 : ℝ)*X 1 0+(-2141360349/10000000000 : ℝ)*X 1 1+(2688038523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1324033097/2500000000 : ℝ)*X 2 0+(5376076501/10000000000 : ℝ)*X 2 1+(-2141361659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4469792853/10000000000 : ℝ)*X 0 0+(4310840199/10000000000 : ℝ)*X 0 1+(2155419961/5000000000 : ℝ)*X 0 2+(4469792853/10000000000 : ℝ)*X 1 0+(4310840199/10000000000 : ℝ)*X 1 1+(2155419961/5000000000 : ℝ)*X 1 2+(4469792853/10000000000 : ℝ)*X 2 0+(4310840199/10000000000 : ℝ)*X 2 1+(2155419961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2287004659/10000000000 : ℝ)*X 0 0+(2640672753/5000000000 : ℝ)*X 0 1+(5281344807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363036421/10000000000 : ℝ)*X 1 0+(-2178672777/10000000000 : ℝ)*X 1 1+(1056269029/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363036519/10000000000 : ℝ)*X 2 0+(1320336243/2500000000 : ℝ)*X 2 1+(-544668219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254691643/10000000000 : ℝ)*X 0 0+(1104592423/2500000000 : ℝ)*X 0 1+(4418370209/10000000000 : ℝ)*X 0 2+(4254691643/10000000000 : ℝ)*X 1 0+(1104592423/2500000000 : ℝ)*X 1 1+(4418370209/10000000000 : ℝ)*X 1 2+(4254691643/10000000000 : ℝ)*X 2 0+(1104592423/2500000000 : ℝ)*X 2 1+(4418370209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1116925017/5000000000 : ℝ)*X 0 0+(5216887907/10000000000 : ℝ)*X 0 1+(1077137107/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057868611/2000000000 : ℝ)*X 1 0+(-1068753801/5000000000 : ℝ)*X 1 1+(134642139/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322335733/2500000000 : ℝ)*X 2 0+(5385685727/10000000000 : ℝ)*X 2 1+(-1068753771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((449133899/1000000000 : ℝ)*X 0 0+(4299926463/10000000000 : ℝ)*X 0 1+(429992649/1000000000 : ℝ)*X 0 2+(449133899/1000000000 : ℝ)*X 1 0+(4299926463/10000000000 : ℝ)*X 1 1+(429992649/1000000000 : ℝ)*X 1 2+(449133899/1000000000 : ℝ)*X 2 0+(4299926463/10000000000 : ℝ)*X 2 1+(429992649/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-260796009/1250000000 : ℝ)*X 0 0+(5439267543/10000000000 : ℝ)*X 0 1+(329581253/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368716223/10000000000 : ℝ)*X 1 0+(-2181784229/10000000000 : ℝ)*X 1 1+(1054659981/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342179121/2500000000 : ℝ)*X 2 0+(20598827/39062500 : ℝ)*X 2 1+(-272723017/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4236192803/10000000000 : ℝ)*X 0 0+(4427497211/10000000000 : ℝ)*X 0 1+(276718561/625000000 : ℝ)*X 0 2+(4236192803/10000000000 : ℝ)*X 1 0+(4427497211/10000000000 : ℝ)*X 1 1+(276718561/625000000 : ℝ)*X 1 2+(4236192803/10000000000 : ℝ)*X 2 0+(4427497211/10000000000 : ℝ)*X 2 1+(276718561/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62233/100000 : ℝ) ≤ (-579521082531518070277945460823/931250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1380993/25000000000000 : ℝ)*(upper0) + (119328549/100000000000000 : ℝ)*(lower1) + (22237381/100000000000000 : ℝ)*(lower4) + (196707375959247/5000000000000 : ℝ)*(major0) + (196707375959247/5000000000000 : ℝ)*(major1) + (196707375959247/5000000000000 : ℝ)*(major2) + (8797138079/100000000000000 : ℝ)*(sp1) + (19829293007/100000000000000 : ℝ)*(sp2) + (41411563/800000000000 : ℝ)*(sp3) + (5262512473663833/100000000000000 : ℝ)*(sp4) + (526251727445597/10000000000000 : ℝ)*(sp5) + (2631253121150521/50000000000000 : ℝ)*(sp6) + (656626818567233/25000000000000 : ℝ)*(sp7) + (1699741277/12500000000000 : ℝ)*(sp8) + (656628112678577/25000000000000 : ℝ)*(f.failure) + (82226969868657/1562500000000 : ℝ)*(f.sum) + (10789759943/1164062500000000000000000 : ℝ)*base65 + (27566328815061941/3725000000000000000000000000000 : ℝ)*base68 + (8525906943811941/3725000000000000000000000000000 : ℝ)*base70 + (18244758168136941/3725000000000000000000000000000 : ℝ)*base72 + (249220940119/18625000000000000000000000 : ℝ)*base73 + (149534805236941/3725000000000000000000000000000 : ℝ)*base76 + (48057861820411941/3725000000000000000000000000000 : ℝ)*base78 + (60329490404213059/3725000000000000000000000000000 : ℝ)*base79 + (653382619027/149000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (247381/19531250000000000000 : ℝ)*base89 + (247381/19531250000000000000 : ℝ)*base91 + (247381/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59311/100000 : ℝ) ≤ (22094262140553277024546245777491/37250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114316047/25000000000000 : ℝ)*(lower0) + (97405383/12500000000000 : ℝ)*(upper2) + (969567/100000000000000 : ℝ)*(upper3) + (3998550169721301/100000000000000 : ℝ)*(major0) + (3998550169721301/100000000000000 : ℝ)*(major1) + (3998550169721301/100000000000000 : ℝ)*(major2) + (212310882350947/4000000000000 : ℝ)*(sp0) + (1326945111889061/25000000000000 : ℝ)*(sp1) + (5307398995578691/100000000000000 : ℝ)*(sp2) + (1334748850442001/50000000000000 : ℝ)*(sp3) + (1245088359/3125000000000 : ℝ)*(sp5) + (11196371233/100000000000000 : ℝ)*(sp7) + (210647402521/50000000000000 : ℝ)*(sp10) + (48231610057/100000000000000 : ℝ)*(sp12) + (1334754448627617/50000000000000 : ℝ)*(f.failure) + (1326955072595933/25000000000000 : ℝ)*(f.sum) + (14415569105321/2235000000000000000000000000 : ℝ)*base66 + (868138066517307503/74500000000000000000000000000000 : ℝ)*base68 + (445000422216192497/74500000000000000000000000000000 : ℝ)*base69 + (232870885556692497/74500000000000000000000000000000 : ℝ)*base71 + (10825234275731/2235000000000000000000000000 : ℝ)*base74 + (18597583497307503/74500000000000000000000000000000 : ℝ)*base76 + (307844150271307503/74500000000000000000000000000000 : ℝ)*base78 + (2236387773130307503/74500000000000000000000000000000 : ℝ)*base80 + (525242042359/2235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (46563/19531250000000000000 : ℝ)*base89 + (46563/19531250000000000000 : ℝ)*base91 + (46563/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79857/100000 : ℝ) ≤ (118990889667471738477491781/149000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11967019/50000000000000 : ℝ)*(upper0) + (2327451/12500000000000 : ℝ)*(upper1) + (1360609/25000000000000 : ℝ)*(upper2) + (893269250062533/20000000000000 : ℝ)*(major0) + (893269250062533/20000000000000 : ℝ)*(major1) + (893269250062533/20000000000000 : ℝ)*(major2) + (42681256037/100000000000000 : ℝ)*(sp1) + (70996437833/50000000000000 : ℝ)*(sp2) + (9830539407/100000000000000 : ℝ)*(sp3) + (36323791/5000000000000 : ℝ)*(sp4) + (23141614618189/390625000000 : ℝ)*(sp8) + (5924211387476167/100000000000000 : ℝ)*(sp9) + (2962056037928269/50000000000000 : ℝ)*(sp10) + (2981808715522063/100000000000000 : ℝ)*(sp11) + (298181854606147/10000000000000 : ℝ)*(f.failure) + (1481063517183051/25000000000000 : ℝ)*(f.sum) + (64636182777/18625000000000000000000000 : ℝ)*base66 + (137418705909986399/14900000000000000000000000000000 : ℝ)*base68 + (63353743973413601/14900000000000000000000000000000 : ℝ)*base69 + (66115210523886399/14900000000000000000000000000000 : ℝ)*base72 + (1236256254553/74500000000000000000000000 : ℝ)*base74 + (41265938647613601/14900000000000000000000000000000 : ℝ)*base75 + (158553849235486399/14900000000000000000000000000000 : ℝ)*base78 + (64539699788413601/14900000000000000000000000000000 : ℝ)*base79 + (276063831963/149000000000000000000000000 : ℝ)*base81 + (21179/1953125000000000000 : ℝ)*base89 + (21179/1953125000000000000 : ℝ)*base91 + (21179/1953125000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-2079/2500 : ℝ) ≤ (-6195242638901691357881567892487/7450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74344729/50000000000000 : ℝ)*(lower0) + (73321949/50000000000000 : ℝ)*(lower1) + (67178581/50000000000000 : ℝ)*(lower2) + (900276146994657/20000000000000 : ℝ)*(major0) + (900276146994657/20000000000000 : ℝ)*(major1) + (900276146994657/20000000000000 : ℝ)*(major2) + (1396652997/100000000000000 : ℝ)*(sp0) + (30721234589/10000000000000 : ℝ)*(sp5) + (86881247689/25000000000000 : ℝ)*(sp6) + (35847477449/50000000000000 : ℝ)*(sp7) + (1506317759692523/25000000000000 : ℝ)*(sp12) + (6024965223077199/100000000000000 : ℝ)*(sp13) + (6024924910432333/100000000000000 : ℝ)*(sp14) + (300513654600661/10000000000000 : ℝ)*(sp15) + (751302060240377/25000000000000 : ℝ)*(f.failure) + (6025272435423089/100000000000000 : ℝ)*(f.sum) + (85151843419/111750000000000000000000000 : ℝ)*base66 + (50725317687330829/14900000000000000000000000000000 : ℝ)*base67 + (111239700008230829/14900000000000000000000000000000 : ℝ)*base69 + (74127857236369171/14900000000000000000000000000000 : ℝ)*base72 + (5661795581237/111750000000000000000000000 : ℝ)*base73 + (45040690711230829/14900000000000000000000000000000 : ℝ)*base75 + (46365230624469171/14900000000000000000000000000000 : ℝ)*base78 + (533168149492930829/14900000000000000000000000000000 : ℝ)*base79 + (668256481517/447000000000000000000000000 : ℝ)*base81 + (319937/39062500000000000000 : ℝ)*base89 + (319937/39062500000000000000 : ℝ)*base91 + (319937/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1158_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59311/100000 : ℝ) else (79857/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2079/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1158_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1158_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59311/100000 : ℝ) else (79857/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2079/2500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1158_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1158_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1158_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59311/100000 : ℝ) else (79857/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2079/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

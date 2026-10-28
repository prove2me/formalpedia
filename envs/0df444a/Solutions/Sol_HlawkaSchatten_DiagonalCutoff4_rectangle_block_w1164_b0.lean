-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:43.18903+00:00
-- url     : https://prove2.me/submissions/25d01a0b-450c-4cfa-9422-c5a2dff5b7b7

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
theorem support_rectangle_w1164_s0_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-471216841/2500000000 : ℝ)*x 0 + (3024629683/5000000000 : ℝ)*x 1 + (4783248311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471216841/2500000000 : ℝ)^8357 ≤ (10965428679703/100000000000000 : ℝ)^6309 := by
    have hnat : (471216841 : ℕ)^8357*100000000000000^6309 ≤ 10965428679703^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471216841 2500000000 10965428679703 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3024629683/5000000000 : ℝ)^8357 ≤ (51385351285297/100000000000000 : ℝ)^6309 := by
    have hnat : (3024629683 : ℕ)^8357*100000000000000^6309 ≤ 51385351285297^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3024629683 5000000000 51385351285297 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783248311/10000000000 : ℝ)^8357 ≤ (9412305007071/25000000000000 : ℝ)^6309 := by
    have hnat : (4783248311 : ℕ)^8357*25000000000000^6309 ≤ 9412305007071^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783248311 10000000000 9412305007071 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471216841/2500000000 : ℝ), (3024629683/5000000000 : ℝ), (4783248311/10000000000 : ℝ)] ![(10965428679703/100000000000000 : ℝ), (51385351285297/100000000000000 : ℝ), (9412305007071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471216841/2500000000 : ℝ)|^8357 ≤ (10965428679703/100000000000000 : ℝ)^6309
        have hw : |(-471216841/2500000000 : ℝ)|=(471216841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3024629683/5000000000 : ℝ)|^8357 ≤ (51385351285297/100000000000000 : ℝ)^6309
        have hw : |(3024629683/5000000000 : ℝ)|=(3024629683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783248311/10000000000 : ℝ)|^8357 ≤ (9412305007071/25000000000000 : ℝ)^6309
        have hw : |(4783248311/10000000000 : ℝ)|=(4783248311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757777173/5000000000 : ℝ)*x 0 + (-2610787011/10000000000 : ℝ)*x 1 + (956649651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757777173/5000000000 : ℝ)^8357 ≤ (45467908103911/100000000000000 : ℝ)^6309 := by
    have hnat : (2757777173 : ℕ)^8357*100000000000000^6309 ≤ 45467908103911^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757777173 5000000000 45467908103911 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610787011/10000000000 : ℝ)^8357 ≤ (8441436215561/50000000000000 : ℝ)^6309 := by
    have hnat : (2610787011 : ℕ)^8357*50000000000000^6309 ≤ 8441436215561^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610787011 10000000000 8441436215561 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956649651/2000000000 : ℝ)^8357 ≤ (37649219444421/100000000000000 : ℝ)^6309 := by
    have hnat : (956649651 : ℕ)^8357*100000000000000^6309 ≤ 37649219444421^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956649651 2000000000 37649219444421 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757777173/5000000000 : ℝ), (-2610787011/10000000000 : ℝ), (956649651/2000000000 : ℝ)] ![(45467908103911/100000000000000 : ℝ), (8441436215561/50000000000000 : ℝ), (37649219444421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757777173/5000000000 : ℝ)|^8357 ≤ (45467908103911/100000000000000 : ℝ)^6309
        have hw : |(2757777173/5000000000 : ℝ)|=(2757777173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2610787011/10000000000 : ℝ)|^8357 ≤ (8441436215561/50000000000000 : ℝ)^6309
        have hw : |(-2610787011/10000000000 : ℝ)|=(2610787011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956649651/2000000000 : ℝ)|^8357 ≤ (37649219444421/100000000000000 : ℝ)^6309
        have hw : |(956649651/2000000000 : ℝ)|=(956649651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757777137/5000000000 : ℝ)*x 0 + (1195812091/2500000000 : ℝ)*x 1 + (-261078697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757777137/5000000000 : ℝ)^8357 ≤ (22733953658851/50000000000000 : ℝ)^6309 := by
    have hnat : (2757777137 : ℕ)^8357*50000000000000^6309 ≤ 22733953658851^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757777137 5000000000 22733953658851 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195812091/2500000000 : ℝ)^8357 ≤ (37649220580869/100000000000000 : ℝ)^6309 := by
    have hnat : (1195812091 : ℕ)^8357*100000000000000^6309 ≤ 37649220580869^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195812091 2500000000 37649220580869 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261078697/1000000000 : ℝ)^8357 ≤ (16882872079927/100000000000000 : ℝ)^6309 := by
    have hnat : (261078697 : ℕ)^8357*100000000000000^6309 ≤ 16882872079927^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261078697 1000000000 16882872079927 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757777137/5000000000 : ℝ), (1195812091/2500000000 : ℝ), (-261078697/1000000000 : ℝ)] ![(22733953658851/50000000000000 : ℝ), (37649220580869/100000000000000 : ℝ), (16882872079927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757777137/5000000000 : ℝ)|^8357 ≤ (22733953658851/50000000000000 : ℝ)^6309
        have hw : |(2757777137/5000000000 : ℝ)|=(2757777137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195812091/2500000000 : ℝ)|^8357 ≤ (37649220580869/100000000000000 : ℝ)^6309
        have hw : |(1195812091/2500000000 : ℝ)|=(1195812091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261078697/1000000000 : ℝ)|^8357 ≤ (16882872079927/100000000000000 : ℝ)^6309
        have hw : |(-261078697/1000000000 : ℝ)|=(261078697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1049804331/2500000000 : ℝ)*x 0 + (3120081233/10000000000 : ℝ)*x 1 + (2824825223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049804331/2500000000 : ℝ)^8357 ≤ (31684211893249/100000000000000 : ℝ)^6309 := by
    have hnat : (1049804331 : ℕ)^8357*100000000000000^6309 ≤ 31684211893249^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049804331 2500000000 31684211893249 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120081233/10000000000 : ℝ)^8357 ≤ (21377860923979/100000000000000 : ℝ)^6309 := by
    have hnat : (3120081233 : ℕ)^8357*100000000000000^6309 ≤ 21377860923979^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120081233 10000000000 21377860923979 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2824825223/5000000000 : ℝ)^8357 ≤ (46937927172567/100000000000000 : ℝ)^6309 := by
    have hnat : (2824825223 : ℕ)^8357*100000000000000^6309 ≤ 46937927172567^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824825223 5000000000 46937927172567 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049804331/2500000000 : ℝ), (3120081233/10000000000 : ℝ), (2824825223/5000000000 : ℝ)] ![(31684211893249/100000000000000 : ℝ), (21377860923979/100000000000000 : ℝ), (46937927172567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049804331/2500000000 : ℝ)|^8357 ≤ (31684211893249/100000000000000 : ℝ)^6309
        have hw : |(1049804331/2500000000 : ℝ)|=(1049804331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120081233/10000000000 : ℝ)|^8357 ≤ (21377860923979/100000000000000 : ℝ)^6309
        have hw : |(3120081233/10000000000 : ℝ)|=(3120081233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2824825223/5000000000 : ℝ)|^8357 ≤ (46937927172567/100000000000000 : ℝ)^6309
        have hw : |(2824825223/5000000000 : ℝ)|=(2824825223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-472487113/2500000000 : ℝ)*x 0 + (192635863/400000000 : ℝ)*x 1 + (6015461677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472487113/2500000000 : ℝ)^8357 ≤ (11004601178377/100000000000000 : ℝ)^6309 := by
    have hnat : (472487113 : ℕ)^8357*100000000000000^6309 ≤ 11004601178377^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472487113 2500000000 11004601178377 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192635863/400000000 : ℝ)^8357 ≤ (18994995718869/50000000000000 : ℝ)^6309 := by
    have hnat : (192635863 : ℕ)^8357*50000000000000^6309 ≤ 18994995718869^6309*400000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192635863 400000000 18994995718869 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015461677/10000000000 : ℝ)^8357 ≤ (10201081473097/20000000000000 : ℝ)^6309 := by
    have hnat : (6015461677 : ℕ)^8357*20000000000000^6309 ≤ 10201081473097^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015461677 10000000000 10201081473097 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472487113/2500000000 : ℝ), (192635863/400000000 : ℝ), (6015461677/10000000000 : ℝ)] ![(11004601178377/100000000000000 : ℝ), (18994995718869/50000000000000 : ℝ), (10201081473097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472487113/2500000000 : ℝ)|^8357 ≤ (11004601178377/100000000000000 : ℝ)^6309
        have hw : |(-472487113/2500000000 : ℝ)|=(472487113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192635863/400000000 : ℝ)|^8357 ≤ (18994995718869/50000000000000 : ℝ)^6309
        have hw : |(192635863/400000000 : ℝ)|=(192635863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6015461677/10000000000 : ℝ)|^8357 ≤ (10201081473097/20000000000000 : ℝ)^6309
        have hw : |(6015461677/10000000000 : ℝ)|=(6015461677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171444561/10000000000 : ℝ)*x 0 + (-11028591/80000000 : ℝ)*x 1 + (1203092293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171444561/10000000000 : ℝ)^8357 ≤ (41748974443973/100000000000000 : ℝ)^6309 := by
    have hnat : (5171444561 : ℕ)^8357*100000000000000^6309 ≤ 41748974443973^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171444561 10000000000 41748974443973 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11028591/80000000 : ℝ)^8357 ≤ (1811405139401/25000000000000 : ℝ)^6309 := by
    have hnat : (11028591 : ℕ)^8357*25000000000000^6309 ≤ 1811405139401^6309*80000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11028591 80000000 1811405139401 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203092293/2000000000 : ℝ)^8357 ≤ (51005404984411/100000000000000 : ℝ)^6309 := by
    have hnat : (1203092293 : ℕ)^8357*100000000000000^6309 ≤ 51005404984411^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203092293 2000000000 51005404984411 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171444561/10000000000 : ℝ), (-11028591/80000000 : ℝ), (1203092293/2000000000 : ℝ)] ![(41748974443973/100000000000000 : ℝ), (1811405139401/25000000000000 : ℝ), (51005404984411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171444561/10000000000 : ℝ)|^8357 ≤ (41748974443973/100000000000000 : ℝ)^6309
        have hw : |(5171444561/10000000000 : ℝ)|=(5171444561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11028591/80000000 : ℝ)|^8357 ≤ (1811405139401/25000000000000 : ℝ)^6309
        have hw : |(-11028591/80000000 : ℝ)|=(11028591/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203092293/2000000000 : ℝ)|^8357 ≤ (51005404984411/100000000000000 : ℝ)^6309
        have hw : |(1203092293/2000000000 : ℝ)|=(1203092293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517144453/1000000000 : ℝ)*x 0 + (6015461551/10000000000 : ℝ)*x 1 + (-172321723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517144453/1000000000 : ℝ)^8357 ≤ (41748974112471/100000000000000 : ℝ)^6309 := by
    have hnat : (517144453 : ℕ)^8357*100000000000000^6309 ≤ 41748974112471^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517144453 1000000000 41748974112471 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6015461551/10000000000 : ℝ)^8357 ≤ (25502702975159/50000000000000 : ℝ)^6309 := by
    have hnat : (6015461551 : ℕ)^8357*50000000000000^6309 ≤ 25502702975159^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015461551 10000000000 25502702975159 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172321723/1250000000 : ℝ)^8357 ≤ (362280996203/5000000000000 : ℝ)^6309 := by
    have hnat : (172321723 : ℕ)^8357*5000000000000^6309 ≤ 362280996203^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172321723 1250000000 362280996203 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517144453/1000000000 : ℝ), (6015461551/10000000000 : ℝ), (-172321723/1250000000 : ℝ)] ![(41748974112471/100000000000000 : ℝ), (25502702975159/50000000000000 : ℝ), (362280996203/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517144453/1000000000 : ℝ)|^8357 ≤ (41748974112471/100000000000000 : ℝ)^6309
        have hw : |(517144453/1000000000 : ℝ)|=(517144453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6015461551/10000000000 : ℝ)|^8357 ≤ (25502702975159/50000000000000 : ℝ)^6309
        have hw : |(6015461551/10000000000 : ℝ)|=(6015461551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-172321723/1250000000 : ℝ)|^8357 ≤ (362280996203/5000000000000 : ℝ)^6309
        have hw : |(-172321723/1250000000 : ℝ)|=(172321723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s0_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4209370009/10000000000 : ℝ)*x 0 + (2792208527/5000000000 : ℝ)*x 1 + (3187611281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209370009/10000000000 : ℝ)^8357 ≤ (31785723486527/100000000000000 : ℝ)^6309 := by
    have hnat : (4209370009 : ℕ)^8357*100000000000000^6309 ≤ 31785723486527^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209370009 10000000000 31785723486527 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2792208527/5000000000 : ℝ)^8357 ≤ (4622137903853/10000000000000 : ℝ)^6309 := by
    have hnat : (2792208527 : ℕ)^8357*10000000000000^6309 ≤ 4622137903853^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792208527 5000000000 4622137903853 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187611281/10000000000 : ℝ)^8357 ≤ (21992897457983/100000000000000 : ℝ)^6309 := by
    have hnat : (3187611281 : ℕ)^8357*100000000000000^6309 ≤ 21992897457983^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187611281 10000000000 21992897457983 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209370009/10000000000 : ℝ), (2792208527/5000000000 : ℝ), (3187611281/10000000000 : ℝ)] ![(31785723486527/100000000000000 : ℝ), (4622137903853/10000000000000 : ℝ), (21992897457983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209370009/10000000000 : ℝ)|^8357 ≤ (31785723486527/100000000000000 : ℝ)^6309
        have hw : |(4209370009/10000000000 : ℝ)|=(4209370009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2792208527/5000000000 : ℝ)|^8357 ≤ (4622137903853/10000000000000 : ℝ)^6309
        have hw : |(2792208527/5000000000 : ℝ)|=(2792208527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187611281/10000000000 : ℝ)|^8357 ≤ (21992897457983/100000000000000 : ℝ)^6309
        have hw : |(3187611281/10000000000 : ℝ)|=(3187611281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (63/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27731/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2089/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2089 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2089*1^512 ≤ 0^512*1^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2089/512 : ℝ) ≤ (297360780880700613/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2089 ≤ (297360780880700613/12500000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2089*12500000000000000000^512 ≤ 297360780880700613^512*5^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 297360780880700613 12500000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (297360780880700613/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2089 := by
      have hnat : (1 : ℕ)^512*1^2089 ≤ 1^2089*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12797360780880700613/12500000000000000000 : ℝ) ≤ (10057788556405849/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (12797360780880700613/12500000000000000000 : ℝ)^512 ≤ (10057788556405849/10000000000000000 : ℝ)^2089 := by
      have hnat : (12797360780880700613 : ℕ)^512*10000000000000000^2089 ≤ 10057788556405849^2089*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12797360780880700613 12500000000000000000 10057788556405849 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057788556405849/10000000000000000 : ℝ)) (X := (12797360780880700613/12500000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6547360780880700613/6250000000000000000 : ℝ) ≤ (5057788556405849/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (6547360780880700613/6250000000000000000 : ℝ)^512 ≤ (5057788556405849/5000000000000000 : ℝ)^2089 := by
      have hnat : (6547360780880700613 : ℕ)^512*5000000000000000^2089 ≤ 5057788556405849^2089*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6547360780880700613 6250000000000000000 5057788556405849 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057788556405849/5000000000000000 : ℝ)) (X := (6547360780880700613/6250000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57788556405849/4000000000000000 : ℝ)*(0 : ℝ))^(2089/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(57788556405849/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(297360780880700613/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57788556405849/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (1 : ℝ)+(57788556405849/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057788556405849/10000000000000000 : ℝ) by norm_num, show 1+(297360780880700613/12500000000000000000 : ℝ)+(0 : ℝ)=(12797360780880700613/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(297360780880700613/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57788556405849/4000000000000000 : ℝ)*(2/5 : ℝ))^(2089/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(57788556405849/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057788556405849/5000000000000000 : ℝ) by norm_num, show 1+2*(297360780880700613/12500000000000000000 : ℝ)=(6547360780880700613/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57788556405849/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57788556405849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57788556405849/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57788556405849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57788556405849/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57788556405849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-471216841/2500000000 : ℝ)*X 0 0+(3024629683/5000000000 : ℝ)*X 0 1+(4783248311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757777173/5000000000 : ℝ)*X 1 0+(-2610787011/10000000000 : ℝ)*X 1 1+(956649651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757777137/5000000000 : ℝ)*X 2 0+(1195812091/2500000000 : ℝ)*X 2 1+(-261078697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1049804331/2500000000 : ℝ)*X 0 0+(3120081233/10000000000 : ℝ)*X 0 1+(2824825223/5000000000 : ℝ)*X 0 2+(1049804331/2500000000 : ℝ)*X 1 0+(3120081233/10000000000 : ℝ)*X 1 1+(2824825223/5000000000 : ℝ)*X 1 2+(1049804331/2500000000 : ℝ)*X 2 0+(3120081233/10000000000 : ℝ)*X 2 1+(2824825223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472487113/2500000000 : ℝ)*X 0 0+(192635863/400000000 : ℝ)*X 0 1+(6015461677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171444561/10000000000 : ℝ)*X 1 0+(-11028591/80000000 : ℝ)*X 1 1+(1203092293/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517144453/1000000000 : ℝ)*X 2 0+(6015461551/10000000000 : ℝ)*X 2 1+(-172321723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209370009/10000000000 : ℝ)*X 0 0+(2792208527/5000000000 : ℝ)*X 0 1+(3187611281/10000000000 : ℝ)*X 0 2+(4209370009/10000000000 : ℝ)*X 1 0+(2792208527/5000000000 : ℝ)*X 1 1+(3187611281/10000000000 : ℝ)*X 1 2+(4209370009/10000000000 : ℝ)*X 2 0+(2792208527/5000000000 : ℝ)*X 2 1+(3187611281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105222252915206883899181/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16212699/100000000000000 : ℝ)*(base1) + (70014421/10000000000000 : ℝ)*(base19) + (641007897/100000000000000 : ℝ)*(base23) + (976503/2000000000000 : ℝ)*(base24) + (19556899/12500000000000 : ℝ)*(upper3) + (592606393905177/100000000000000 : ℝ)*(major0) + (592606393905177/100000000000000 : ℝ)*(major1) + (592606393905177/100000000000000 : ℝ)*(major2) + (394942452795799/50000000000000 : ℝ)*(sp0) + (78988578485413/10000000000000 : ℝ)*(sp1) + (197471448791323/25000000000000 : ℝ)*(sp2) + (395324968063641/100000000000000 : ℝ)*(sp3) + (19945243/1250000000000 : ℝ)*(sp4) + (615425229/50000000000000 : ℝ)*(sp7) + (197663107563399/50000000000000 : ℝ)*(f.failure) + (789886484998339/100000000000000 : ℝ)*(f.sum) + (752331183380273/200000000000000000000000000000 : ℝ)*base65 + (1178320452980273/400000000000000000000000000000 : ℝ)*base67 + (787177457380273/400000000000000000000000000000 : ℝ)*base69 + (416762519780273/400000000000000000000000000000 : ℝ)*base71 + (876323503180273/200000000000000000000000000000 : ℝ)*base73 + (1119443059419727/400000000000000000000000000000 : ℝ)*base76 + (1564958908580273/400000000000000000000000000000 : ℝ)*base77 + (2779617484980273/400000000000000000000000000000 : ℝ)*base79 + (706713365380273/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (658773/156250000000000000000 : ℝ)*base90 + (658773/156250000000000000000 : ℝ)*base92 + (658773/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140501240775564592575561/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13974079/20000000000000 : ℝ)*(base1) + (1398085849/100000000000000 : ℝ)*(base19) + (69675359/5000000000000 : ℝ)*(base23) + (149054211/100000000000000 : ℝ)*(upper3) + (83485111/50000000000000 : ℝ)*(upper5) + (78178603998363/12500000000000 : ℝ)*(major0) + (78178603998363/12500000000000 : ℝ)*(major1) + (78178603998363/12500000000000 : ℝ)*(major2) + (2826744101/100000000000000 : ℝ)*(sp1) + (1416517037/50000000000000 : ℝ)*(sp2) + (833635566585519/100000000000000 : ℝ)*(sp4) + (833631271885173/100000000000000 : ℝ)*(sp5) + (833631270173869/100000000000000 : ℝ)*(sp6) + (26076369378331/6250000000000 : ℝ)*(sp7) + (104305494980923/25000000000000 : ℝ)*(f.failure) + (833635496715123/100000000000000 : ℝ)*(f.sum) + (52029632725187/25000000000000000000000000000 : ℝ)*base65 + (149012410824813/50000000000000000000000000000 : ℝ)*base68 + (414036417324813/50000000000000000000000000000 : ℝ)*base70 + (127702373524813/50000000000000000000000000000 : ℝ)*base72 + (21838397175187/25000000000000000000000000000 : ℝ)*base73 + (75961259174813/50000000000000000000000000000 : ℝ)*base76 + (167677965874813/50000000000000000000000000000 : ℝ)*base78 + (37264172675187/50000000000000000000000000000 : ℝ)*base79 + (86371192874813/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (558579/78125000000000000000 : ℝ)*base89 + (558579/78125000000000000000 : ℝ)*base91 + (558579/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1164_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s1_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-208793843/1000000000 : ℝ)*x 0 + (5695667393/10000000000 : ℝ)*x 1 + (5006842103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208793843/1000000000 : ℝ)^8357 ≤ (6278522022341/50000000000000 : ℝ)^6309 := by
    have hnat : (208793843 : ℕ)^8357*50000000000000^6309 ≤ 6278522022341^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208793843 1000000000 6278522022341 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5695667393/10000000000 : ℝ)^8357 ≤ (23722507228989/50000000000000 : ℝ)^6309 := by
    have hnat : (5695667393 : ℕ)^8357*50000000000000^6309 ≤ 23722507228989^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5695667393 10000000000 23722507228989 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5006842103/10000000000 : ℝ)^8357 ≤ (39997941488921/100000000000000 : ℝ)^6309 := by
    have hnat : (5006842103 : ℕ)^8357*100000000000000^6309 ≤ 39997941488921^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006842103 10000000000 39997941488921 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208793843/1000000000 : ℝ), (5695667393/10000000000 : ℝ), (5006842103/10000000000 : ℝ)] ![(6278522022341/50000000000000 : ℝ), (23722507228989/50000000000000 : ℝ), (39997941488921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208793843/1000000000 : ℝ)|^8357 ≤ (6278522022341/50000000000000 : ℝ)^6309
        have hw : |(-208793843/1000000000 : ℝ)|=(208793843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5695667393/10000000000 : ℝ)|^8357 ≤ (23722507228989/50000000000000 : ℝ)^6309
        have hw : |(5695667393/10000000000 : ℝ)|=(5695667393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5006842103/10000000000 : ℝ)|^8357 ≤ (39997941488921/100000000000000 : ℝ)^6309
        have hw : |(5006842103/10000000000 : ℝ)|=(5006842103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417915583/10000000000 : ℝ)*x 0 + (-491850479/2000000000 : ℝ)*x 1 + (1251710287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417915583/10000000000 : ℝ)^8357 ≤ (4440481012151/10000000000000 : ℝ)^6309 := by
    have hnat : (5417915583 : ℕ)^8357*10000000000000^6309 ≤ 4440481012151^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417915583 10000000000 4440481012151 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491850479/2000000000 : ℝ)^8357 ≤ (3119451696207/20000000000000 : ℝ)^6309 := by
    have hnat : (491850479 : ℕ)^8357*20000000000000^6309 ≤ 3119451696207^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491850479 2000000000 3119451696207 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251710287/2500000000 : ℝ)^8357 ≤ (4999741422901/12500000000000 : ℝ)^6309 := by
    have hnat : (1251710287 : ℕ)^8357*12500000000000^6309 ≤ 4999741422901^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251710287 2500000000 4999741422901 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417915583/10000000000 : ℝ), (-491850479/2000000000 : ℝ), (1251710287/2500000000 : ℝ)] ![(4440481012151/10000000000000 : ℝ), (3119451696207/20000000000000 : ℝ), (4999741422901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417915583/10000000000 : ℝ)|^8357 ≤ (4440481012151/10000000000000 : ℝ)^6309
        have hw : |(5417915583/10000000000 : ℝ)|=(5417915583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491850479/2000000000 : ℝ)|^8357 ≤ (3119451696207/20000000000000 : ℝ)^6309
        have hw : |(-491850479/2000000000 : ℝ)|=(491850479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251710287/2500000000 : ℝ)|^8357 ≤ (4999741422901/12500000000000 : ℝ)^6309
        have hw : |(1251710287/2500000000 : ℝ)|=(1251710287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083583539/2000000000 : ℝ)*x 0 + (1001367843/2000000000 : ℝ)*x 1 + (-24592521/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083583539/2000000000 : ℝ)^8357 ≤ (11101208262581/25000000000000 : ℝ)^6309 := by
    have hnat : (1083583539 : ℕ)^8357*25000000000000^6309 ≤ 11101208262581^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083583539 2000000000 11101208262581 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001367843/2000000000 : ℝ)^8357 ≤ (39997910928399/100000000000000 : ℝ)^6309 := by
    have hnat : (1001367843 : ℕ)^8357*100000000000000^6309 ≤ 39997910928399^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001367843 2000000000 39997910928399 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24592521/100000000 : ℝ)^8357 ≤ (15597256002717/100000000000000 : ℝ)^6309 := by
    have hnat : (24592521 : ℕ)^8357*100000000000000^6309 ≤ 15597256002717^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24592521 100000000 15597256002717 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083583539/2000000000 : ℝ), (1001367843/2000000000 : ℝ), (-24592521/100000000 : ℝ)] ![(11101208262581/25000000000000 : ℝ), (39997910928399/100000000000000 : ℝ), (15597256002717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083583539/2000000000 : ℝ)|^8357 ≤ (11101208262581/25000000000000 : ℝ)^6309
        have hw : |(1083583539/2000000000 : ℝ)|=(1083583539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001367843/2000000000 : ℝ)|^8357 ≤ (39997910928399/100000000000000 : ℝ)^6309
        have hw : |(1001367843/2000000000 : ℝ)|=(1001367843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24592521/100000000 : ℝ)|^8357 ≤ (15597256002717/100000000000000 : ℝ)^6309
        have hw : |(-24592521/100000000 : ℝ)|=(24592521/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315571073/10000000000 : ℝ)*x 0 + (1840578621/5000000000 : ℝ)*x 1 + (5057468701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315571073/10000000000 : ℝ)^8357 ≤ (32852316118501/100000000000000 : ℝ)^6309 := by
    have hnat : (4315571073 : ℕ)^8357*100000000000000^6309 ≤ 32852316118501^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315571073 10000000000 32852316118501 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840578621/5000000000 : ℝ)^8357 ≤ (3326642449701/12500000000000 : ℝ)^6309 := by
    have hnat : (1840578621 : ℕ)^8357*12500000000000^6309 ≤ 3326642449701^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840578621 5000000000 3326642449701 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057468701/10000000000 : ℝ)^8357 ≤ (40534544270519/100000000000000 : ℝ)^6309 := by
    have hnat : (5057468701 : ℕ)^8357*100000000000000^6309 ≤ 40534544270519^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057468701 10000000000 40534544270519 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315571073/10000000000 : ℝ), (1840578621/5000000000 : ℝ), (5057468701/10000000000 : ℝ)] ![(32852316118501/100000000000000 : ℝ), (3326642449701/12500000000000 : ℝ), (40534544270519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315571073/10000000000 : ℝ)|^8357 ≤ (32852316118501/100000000000000 : ℝ)^6309
        have hw : |(4315571073/10000000000 : ℝ)|=(4315571073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1840578621/5000000000 : ℝ)|^8357 ≤ (3326642449701/12500000000000 : ℝ)^6309
        have hw : |(1840578621/5000000000 : ℝ)|=(1840578621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057468701/10000000000 : ℝ)|^8357 ≤ (40534544270519/100000000000000 : ℝ)^6309
        have hw : |(5057468701/10000000000 : ℝ)|=(5057468701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-522179663/2500000000 : ℝ)*x 0 + (2508084327/5000000000 : ℝ)*x 1 + (5686154421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522179663/2500000000 : ℝ)^8357 ≤ (12563259946327/100000000000000 : ℝ)^6309 := by
    have hnat : (522179663 : ℕ)^8357*100000000000000^6309 ≤ 12563259946327^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522179663 2500000000 12563259946327 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508084327/5000000000 : ℝ)^8357 ≤ (20048331968851/50000000000000 : ℝ)^6309 := by
    have hnat : (2508084327 : ℕ)^8357*50000000000000^6309 ≤ 20048331968851^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508084327 5000000000 20048331968851 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686154421/10000000000 : ℝ)^8357 ≤ (23670038050041/50000000000000 : ℝ)^6309 := by
    have hnat : (5686154421 : ℕ)^8357*50000000000000^6309 ≤ 23670038050041^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686154421 10000000000 23670038050041 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522179663/2500000000 : ℝ), (2508084327/5000000000 : ℝ), (5686154421/10000000000 : ℝ)] ![(12563259946327/100000000000000 : ℝ), (20048331968851/50000000000000 : ℝ), (23670038050041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522179663/2500000000 : ℝ)|^8357 ≤ (12563259946327/100000000000000 : ℝ)^6309
        have hw : |(-522179663/2500000000 : ℝ)|=(522179663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508084327/5000000000 : ℝ)|^8357 ≤ (20048331968851/50000000000000 : ℝ)^6309
        have hw : |(2508084327/5000000000 : ℝ)|=(2508084327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686154421/10000000000 : ℝ)|^8357 ≤ (23670038050041/50000000000000 : ℝ)^6309
        have hw : |(5686154421/10000000000 : ℝ)|=(5686154421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241119413/10000000000 : ℝ)*x 0 + (-444983921/2500000000 : ℝ)*x 1 + (5686157637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241119413/10000000000 : ℝ)^8357 ≤ (42495673626829/100000000000000 : ℝ)^6309 := by
    have hnat : (5241119413 : ℕ)^8357*100000000000000^6309 ≤ 42495673626829^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241119413 10000000000 42495673626829 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444983921/2500000000 : ℝ)^8357 ≤ (10164214785521/100000000000000 : ℝ)^6309 := by
    have hnat : (444983921 : ℕ)^8357*100000000000000^6309 ≤ 10164214785521^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444983921 2500000000 10164214785521 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686157637/10000000000 : ℝ)^8357 ≤ (47340111566413/100000000000000 : ℝ)^6309 := by
    have hnat : (5686157637 : ℕ)^8357*100000000000000^6309 ≤ 47340111566413^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686157637 10000000000 47340111566413 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241119413/10000000000 : ℝ), (-444983921/2500000000 : ℝ), (5686157637/10000000000 : ℝ)] ![(42495673626829/100000000000000 : ℝ), (10164214785521/100000000000000 : ℝ), (47340111566413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241119413/10000000000 : ℝ)|^8357 ≤ (42495673626829/100000000000000 : ℝ)^6309
        have hw : |(5241119413/10000000000 : ℝ)|=(5241119413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444983921/2500000000 : ℝ)|^8357 ≤ (10164214785521/100000000000000 : ℝ)^6309
        have hw : |(-444983921/2500000000 : ℝ)|=(444983921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686157637/10000000000 : ℝ)|^8357 ≤ (47340111566413/100000000000000 : ℝ)^6309
        have hw : |(5686157637/10000000000 : ℝ)|=(5686157637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (209644741/400000000 : ℝ)*x 0 + (2843079523/5000000000 : ℝ)*x 1 + (-1779934891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209644741/400000000 : ℝ)^8357 ≤ (10623916022393/25000000000000 : ℝ)^6309 := by
    have hnat : (209644741 : ℕ)^8357*25000000000000^6309 ≤ 10623916022393^6309*400000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209644741 400000000 10623916022393 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2843079523/5000000000 : ℝ)^8357 ≤ (47340127104991/100000000000000 : ℝ)^6309 := by
    have hnat : (2843079523 : ℕ)^8357*100000000000000^6309 ≤ 47340127104991^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843079523 5000000000 47340127104991 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1779934891/10000000000 : ℝ)^8357 ≤ (254105219679/2500000000000 : ℝ)^6309 := by
    have hnat : (1779934891 : ℕ)^8357*2500000000000^6309 ≤ 254105219679^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779934891 10000000000 254105219679 2500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209644741/400000000 : ℝ), (2843079523/5000000000 : ℝ), (-1779934891/10000000000 : ℝ)] ![(10623916022393/25000000000000 : ℝ), (47340127104991/100000000000000 : ℝ), (254105219679/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209644741/400000000 : ℝ)|^8357 ≤ (10623916022393/25000000000000 : ℝ)^6309
        have hw : |(209644741/400000000 : ℝ)|=(209644741/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2843079523/5000000000 : ℝ)|^8357 ≤ (47340127104991/100000000000000 : ℝ)^6309
        have hw : |(2843079523/5000000000 : ℝ)|=(2843079523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1779934891/10000000000 : ℝ)|^8357 ≤ (254105219679/2500000000000 : ℝ)^6309
        have hw : |(-1779934891/10000000000 : ℝ)|=(1779934891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4317118251/10000000000 : ℝ)*x 0 + (5038836053/10000000000 : ℝ)*x 1 + (370015617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317118251/10000000000 : ℝ)^8357 ≤ (32867918221631/100000000000000 : ℝ)^6309 := by
    have hnat : (4317118251 : ℕ)^8357*100000000000000^6309 ≤ 32867918221631^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317118251 10000000000 32867918221631 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5038836053/10000000000 : ℝ)^8357 ≤ (10084212218597/25000000000000 : ℝ)^6309 := by
    have hnat : (5038836053 : ℕ)^8357*25000000000000^6309 ≤ 10084212218597^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038836053 10000000000 10084212218597 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370015617/1000000000 : ℝ)^8357 ≤ (3349404111121/12500000000000 : ℝ)^6309 := by
    have hnat : (370015617 : ℕ)^8357*12500000000000^6309 ≤ 3349404111121^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370015617 1000000000 3349404111121 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317118251/10000000000 : ℝ), (5038836053/10000000000 : ℝ), (370015617/1000000000 : ℝ)] ![(32867918221631/100000000000000 : ℝ), (10084212218597/25000000000000 : ℝ), (3349404111121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317118251/10000000000 : ℝ)|^8357 ≤ (32867918221631/100000000000000 : ℝ)^6309
        have hw : |(4317118251/10000000000 : ℝ)|=(4317118251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5038836053/10000000000 : ℝ)|^8357 ≤ (10084212218597/25000000000000 : ℝ)^6309
        have hw : |(5038836053/10000000000 : ℝ)|=(5038836053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370015617/1000000000 : ℝ)|^8357 ≤ (3349404111121/12500000000000 : ℝ)^6309
        have hw : |(370015617/1000000000 : ℝ)|=(370015617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_8 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1366899/2500000000 : ℝ)*x 0 + (686314177/1250000000 : ℝ)*x 1 + (6350374723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1366899/2500000000 : ℝ)^8357 ≤ (298341843/6250000000000 : ℝ)^6309 := by
    have hnat : (1366899 : ℕ)^8357*6250000000000^6309 ≤ 298341843^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366899 2500000000 298341843 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686314177/1250000000 : ℝ)^8357 ≤ (5649334190433/12500000000000 : ℝ)^6309 := by
    have hnat : (686314177 : ℕ)^8357*12500000000000^6309 ≤ 5649334190433^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686314177 1250000000 5649334190433 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6350374723/10000000000 : ℝ)^8357 ≤ (54800552984717/100000000000000 : ℝ)^6309 := by
    have hnat : (6350374723 : ℕ)^8357*100000000000000^6309 ≤ 54800552984717^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6350374723 10000000000 54800552984717 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1366899/2500000000 : ℝ), (686314177/1250000000 : ℝ), (6350374723/10000000000 : ℝ)] ![(298341843/6250000000000 : ℝ), (5649334190433/12500000000000 : ℝ), (54800552984717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1366899/2500000000 : ℝ)|^8357 ≤ (298341843/6250000000000 : ℝ)^6309
        have hw : |(1366899/2500000000 : ℝ)|=(1366899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686314177/1250000000 : ℝ)|^8357 ≤ (5649334190433/12500000000000 : ℝ)^6309
        have hw : |(686314177/1250000000 : ℝ)|=(686314177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6350374723/10000000000 : ℝ)|^8357 ≤ (54800552984717/100000000000000 : ℝ)^6309
        have hw : |(6350374723/10000000000 : ℝ)|=(6350374723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_9 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (984401729/10000000000 : ℝ)*x 0 + (-4395265571/10000000000 : ℝ)*x 1 + (3472703497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984401729/10000000000 : ℝ)^8357 ≤ (927620587841/20000000000000 : ℝ)^6309 := by
    have hnat : (984401729 : ℕ)^8357*20000000000000^6309 ≤ 927620587841^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984401729 10000000000 927620587841 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4395265571/10000000000 : ℝ)^8357 ≤ (3365832595397/10000000000000 : ℝ)^6309 := by
    have hnat : (4395265571 : ℕ)^8357*10000000000000^6309 ≤ 3365832595397^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395265571 10000000000 3365832595397 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3472703497/5000000000 : ℝ)^8357 ≤ (61703571080969/100000000000000 : ℝ)^6309 := by
    have hnat : (3472703497 : ℕ)^8357*100000000000000^6309 ≤ 61703571080969^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472703497 5000000000 61703571080969 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984401729/10000000000 : ℝ), (-4395265571/10000000000 : ℝ), (3472703497/5000000000 : ℝ)] ![(927620587841/20000000000000 : ℝ), (3365832595397/10000000000000 : ℝ), (61703571080969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984401729/10000000000 : ℝ)|^8357 ≤ (927620587841/20000000000000 : ℝ)^6309
        have hw : |(984401729/10000000000 : ℝ)|=(984401729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4395265571/10000000000 : ℝ)|^8357 ≤ (3365832595397/10000000000000 : ℝ)^6309
        have hw : |(-4395265571/10000000000 : ℝ)|=(4395265571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3472703497/5000000000 : ℝ)|^8357 ≤ (61703571080969/100000000000000 : ℝ)^6309
        have hw : |(3472703497/5000000000 : ℝ)|=(3472703497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_10 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (984394943/10000000000 : ℝ)*x 0 + (6945390503/10000000000 : ℝ)*x 1 + (-4395288879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984394943/10000000000 : ℝ)^8357 ≤ (579757573433/12500000000000 : ℝ)^6309 := by
    have hnat : (984394943 : ℕ)^8357*12500000000000^6309 ≤ 579757573433^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984394943 10000000000 579757573433 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6945390503/10000000000 : ℝ)^8357 ≤ (61703377015039/100000000000000 : ℝ)^6309 := by
    have hnat : (6945390503 : ℕ)^8357*100000000000000^6309 ≤ 61703377015039^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6945390503 10000000000 61703377015039 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4395288879/10000000000 : ℝ)^8357 ≤ (33658562384007/100000000000000 : ℝ)^6309 := by
    have hnat : (4395288879 : ℕ)^8357*100000000000000^6309 ≤ 33658562384007^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395288879 10000000000 33658562384007 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984394943/10000000000 : ℝ), (6945390503/10000000000 : ℝ), (-4395288879/10000000000 : ℝ)] ![(579757573433/12500000000000 : ℝ), (61703377015039/100000000000000 : ℝ), (33658562384007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984394943/10000000000 : ℝ)|^8357 ≤ (579757573433/12500000000000 : ℝ)^6309
        have hw : |(984394943/10000000000 : ℝ)|=(984394943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6945390503/10000000000 : ℝ)|^8357 ≤ (61703377015039/100000000000000 : ℝ)^6309
        have hw : |(6945390503/10000000000 : ℝ)|=(6945390503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4395288879/10000000000 : ℝ)|^8357 ≤ (33658562384007/100000000000000 : ℝ)^6309
        have hw : |(-4395288879/10000000000 : ℝ)|=(4395288879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s1_11 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (478337111/2500000000 : ℝ)*x 0 + (725827419/1250000000 : ℝ)*x 1 + (5020396561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478337111/2500000000 : ℝ)^8357 ≤ (2796360803881/25000000000000 : ℝ)^6309 := by
    have hnat : (478337111 : ℕ)^8357*25000000000000^6309 ≤ 2796360803881^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478337111 2500000000 2796360803881 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (725827419/1250000000 : ℝ)^8357 ≤ (48673120391553/100000000000000 : ℝ)^6309 := by
    have hnat : (725827419 : ℕ)^8357*100000000000000^6309 ≤ 48673120391553^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725827419 1250000000 48673120391553 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020396561/10000000000 : ℝ)^8357 ≤ (20070718191173/50000000000000 : ℝ)^6309 := by
    have hnat : (5020396561 : ℕ)^8357*50000000000000^6309 ≤ 20070718191173^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020396561 10000000000 20070718191173 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(478337111/2500000000 : ℝ), (725827419/1250000000 : ℝ), (5020396561/10000000000 : ℝ)] ![(2796360803881/25000000000000 : ℝ), (48673120391553/100000000000000 : ℝ), (20070718191173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(478337111/2500000000 : ℝ)|^8357 ≤ (2796360803881/25000000000000 : ℝ)^6309
        have hw : |(478337111/2500000000 : ℝ)|=(478337111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(725827419/1250000000 : ℝ)|^8357 ≤ (48673120391553/100000000000000 : ℝ)^6309
        have hw : |(725827419/1250000000 : ℝ)|=(725827419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020396561/10000000000 : ℝ)|^8357 ≤ (20070718191173/50000000000000 : ℝ)^6309
        have hw : |(5020396561/10000000000 : ℝ)|=(5020396561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1443/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10169/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/12500 : ℝ) ^ (2089/512 : ℝ) ≤ (21120641037/50000000000000000000 : ℝ) := by
    have hpowers : (63/12500 : ℝ)^2089 ≤ (21120641037/50000000000000000000 : ℝ)^512 := by
      have hnat : (63 : ℕ)^2089*50000000000000000000^512 ≤ 21120641037^512*12500^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 12500 21120641037 50000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/12500 : ℝ)) (X := (21120641037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27731/100000 : ℝ) ^ (2089/512 : ℝ) ≤ (533649181299191329/100000000000000000000 : ℝ) := by
    have hpowers : (27731/100000 : ℝ)^2089 ≤ (533649181299191329/100000000000000000000 : ℝ)^512 := by
      have hnat : (27731 : ℕ)^2089*100000000000000000000^512 ≤ 533649181299191329^512*100000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27731 100000 533649181299191329 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27731/100000 : ℝ)) (X := (533649181299191329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000021120641037/25000000000000000000 : ℝ) ≤ (2500000000517653/2500000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (25000000021120641037/25000000000000000000 : ℝ)^512 ≤ (2500000000517653/2500000000000000 : ℝ)^2089 := by
      have hnat : (25000000021120641037 : ℕ)^512*2500000000000000^2089 ≤ 2500000000517653^2089*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000021120641037 25000000000000000000 2500000000517653 2500000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000517653/2500000000000000 : ℝ)) (X := (25000000021120641037/25000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100533649223540473403/100000000000000000000 : ℝ) ≤ (5006526561909689/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (100533649223540473403/100000000000000000000 : ℝ)^512 ≤ (5006526561909689/5000000000000000 : ℝ)^2089 := by
      have hnat : (100533649223540473403 : ℕ)^512*5000000000000000^2089 ≤ 5006526561909689^2089*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100533649223540473403 100000000000000000000 5006526561909689 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006526561909689/5000000000000000 : ℝ)) (X := (100533649223540473403/100000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50533649181299191329/50000000000000000000 : ℝ) ≤ (626631640348009/625000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50533649181299191329/50000000000000000000 : ℝ)^512 ≤ (626631640348009/625000000000000 : ℝ)^2089 := by
      have hnat : (50533649181299191329 : ℕ)^512*625000000000000^2089 ≤ 626631640348009^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50533649181299191329 50000000000000000000 626631640348009 625000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626631640348009/625000000000000 : ℝ)) (X := (50533649181299191329/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21120641037/50000000000000000000 : ℝ) ≤ ((68064210627413449199/68067500000000000000 : ℝ)+2*(6526560874383/1361350000000000 : ℝ)*(63/12500 : ℝ))^(2089/512 : ℝ) := by
    rw [show (68064210627413449199/68067500000000000000 : ℝ)+2*(6526560874383/1361350000000000 : ℝ)*(63/12500 : ℝ)=(2500000000517653/2500000000000000 : ℝ) by norm_num, show 1+2*(21120641037/50000000000000000000 : ℝ)=(25000000021120641037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(533649181299191329/100000000000000000000 : ℝ)+(21120641037/50000000000000000000 : ℝ) ≤ ((68064210627413449199/68067500000000000000 : ℝ)+(6526560874383/1361350000000000 : ℝ)*((27731/100000 : ℝ)+(63/12500 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (68064210627413449199/68067500000000000000 : ℝ)+(6526560874383/1361350000000000 : ℝ)*((27731/100000 : ℝ)+(63/12500 : ℝ))=(5006526561909689/5000000000000000 : ℝ) by norm_num, show 1+(533649181299191329/100000000000000000000 : ℝ)+(21120641037/50000000000000000000 : ℝ)=(100533649223540473403/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(533649181299191329/100000000000000000000 : ℝ) ≤ ((68064210627413449199/68067500000000000000 : ℝ)+2*(6526560874383/1361350000000000 : ℝ)*(27731/100000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (68064210627413449199/68067500000000000000 : ℝ)+2*(6526560874383/1361350000000000 : ℝ)*(27731/100000 : ℝ)=(626631640348009/625000000000000 : ℝ) by norm_num, show 1+2*(533649181299191329/100000000000000000000 : ℝ)=(50533649181299191329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68064210627413449199/68067500000000000000 : ℝ)*(X 1 0+X 2 0)+(6526560874383/1361350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (63/12500 : ℝ)) (hi := (27731/100000 : ℝ)) (c := (68064210627413449199/68067500000000000000 : ℝ)) (alpha := (6526560874383/1361350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68064210627413449199/68067500000000000000 : ℝ)*(X 0 1+X 2 1)+(6526560874383/1361350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (63/12500 : ℝ)) (hi := (27731/100000 : ℝ)) (c := (68064210627413449199/68067500000000000000 : ℝ)) (alpha := (6526560874383/1361350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68064210627413449199/68067500000000000000 : ℝ)*(X 0 2+X 1 2)+(6526560874383/1361350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (63/12500 : ℝ)) (hi := (27731/100000 : ℝ)) (c := (68064210627413449199/68067500000000000000 : ℝ)) (alpha := (6526560874383/1361350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208793843/1000000000 : ℝ)*X 0 0+(5695667393/10000000000 : ℝ)*X 0 1+(5006842103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417915583/10000000000 : ℝ)*X 1 0+(-491850479/2000000000 : ℝ)*X 1 1+(1251710287/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083583539/2000000000 : ℝ)*X 2 0+(1001367843/2000000000 : ℝ)*X 2 1+(-24592521/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315571073/10000000000 : ℝ)*X 0 0+(1840578621/5000000000 : ℝ)*X 0 1+(5057468701/10000000000 : ℝ)*X 0 2+(4315571073/10000000000 : ℝ)*X 1 0+(1840578621/5000000000 : ℝ)*X 1 1+(5057468701/10000000000 : ℝ)*X 1 2+(4315571073/10000000000 : ℝ)*X 2 0+(1840578621/5000000000 : ℝ)*X 2 1+(5057468701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-522179663/2500000000 : ℝ)*X 0 0+(2508084327/5000000000 : ℝ)*X 0 1+(5686154421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241119413/10000000000 : ℝ)*X 1 0+(-444983921/2500000000 : ℝ)*X 1 1+(5686157637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((209644741/400000000 : ℝ)*X 2 0+(2843079523/5000000000 : ℝ)*X 2 1+(-1779934891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317118251/10000000000 : ℝ)*X 0 0+(5038836053/10000000000 : ℝ)*X 0 1+(370015617/1000000000 : ℝ)*X 0 2+(4317118251/10000000000 : ℝ)*X 1 0+(5038836053/10000000000 : ℝ)*X 1 1+(370015617/1000000000 : ℝ)*X 1 2+(4317118251/10000000000 : ℝ)*X 2 0+(5038836053/10000000000 : ℝ)*X 2 1+(370015617/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1366899/2500000000 : ℝ)*X 0 0+(686314177/1250000000 : ℝ)*X 0 1+(6350374723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((984401729/10000000000 : ℝ)*X 1 0+(-4395265571/10000000000 : ℝ)*X 1 1+(3472703497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((984394943/10000000000 : ℝ)*X 2 0+(6945390503/10000000000 : ℝ)*X 2 1+(-4395288879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((478337111/2500000000 : ℝ)*X 0 0+(725827419/1250000000 : ℝ)*X 0 1+(5020396561/10000000000 : ℝ)*X 0 2+(478337111/2500000000 : ℝ)*X 1 0+(725827419/1250000000 : ℝ)*X 1 1+(5020396561/10000000000 : ℝ)*X 1 2+(478337111/2500000000 : ℝ)*X 2 0+(725827419/1250000000 : ℝ)*X 2 1+(5020396561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498084257801630008282687299/85084375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291421397/100000000000000 : ℝ)*(lower2) + (54458307573533/5000000000000 : ℝ)*(major0) + (54458307573533/5000000000000 : ℝ)*(major1) + (54458307573533/5000000000000 : ℝ)*(major2) + (1451748255094529/100000000000000 : ℝ)*(sp0) + (725873807196939/50000000000000 : ℝ)*(sp1) + (181468238747673/12500000000000 : ℝ)*(sp2) + (22705594853563/3125000000000 : ℝ)*(sp3) + (3888788713/100000000000000 : ℝ)*(sp4) + (1887071843/50000000000000 : ℝ)*(sp5) + (5513670087/100000000000000 : ℝ)*(sp6) + (377672839/50000000000000 : ℝ)*(sp9) + (720231771/100000000000000 : ℝ)*(sp10) + (464305297/50000000000000 : ℝ)*(sp11) + (72657996392461/10000000000000 : ℝ)*(f.failure) + (725876071941621/50000000000000 : ℝ)*(f.sum) + (94143494949223/13613500000000000000000000000 : ℝ)*base65 + (10020464020737567/340337500000000000000000000000000 : ℝ)*base67 + (48814003265224933/340337500000000000000000000000000 : ℝ)*base70 + (204279936231075067/340337500000000000000000000000000 : ℝ)*base71 + (24625214921809/6806750000000000000000000000 : ℝ)*base73 + (359322403060450067/340337500000000000000000000000000 : ℝ)*base75 + (1534750722106600067/340337500000000000000000000000000 : ℝ)*base77 + (585018568346337567/340337500000000000000000000000000 : ℝ)*base79 + (6942571674383/3403375000000000000000000000 : ℝ)*base81 + (291947/31250000000000000000 : ℝ)*base90 + (291947/31250000000000000000 : ℝ)*base92 + (291947/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11221110025794798595879703301/1701687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1119787938196667/100000000000000 : ℝ)*(major0) + (1119787938196667/100000000000000 : ℝ)*(major1) + (1119787938196667/100000000000000 : ℝ)*(major2) + (577654101/12500000000000 : ℝ)*(sp1) + (724239503/10000000000000 : ℝ)*(sp2) + (314178341/25000000000000 : ℝ)*(sp3) + (373141162242319/25000000000000 : ℝ)*(sp4) + (746281459555943/50000000000000 : ℝ)*(sp5) + (46642515638929/3125000000000 : ℝ)*(sp6) + (373502479499867/50000000000000 : ℝ)*(sp7) + (3327810051/100000000000000 : ℝ)*(sp8) + (436434633/100000000000000 : ℝ)*(sp9) + (233938569/100000000000000 : ℝ)*(sp10) + (1464097327/100000000000000 : ℝ)*(sp11) + (373503839905213/50000000000000 : ℝ)*(f.failure) + (1492567976779327/100000000000000 : ℝ)*(f.sum) + (16729976295099/17016875000000000000000000000 : ℝ)*base65 + (13937468902354169733/6806750000000000000000000000000000 : ℝ)*base67 + (19690543218693669733/6806750000000000000000000000000000 : ℝ)*base69 + (12668951952225919733/6806750000000000000000000000000000 : ℝ)*base71 + (444815301207877/136135000000000000000000000000 : ℝ)*base73 + (11222469072325419733/6806750000000000000000000000000000 : ℝ)*base75 + (3686668917125580267/6806750000000000000000000000000000 : ℝ)*base78 + (21786002710485419733/6806750000000000000000000000000000 : ℝ)*base79 + (61338836170501/68067500000000000000000000000 : ℝ)*base81 + (670249/156250000000000000000 : ℝ)*base89 + (670249/156250000000000000000 : ℝ)*base91 + (670249/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1164_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1443/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10169/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s2_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070000119/5000000000 : ℝ)*x 0 + (1376666883/2500000000 : ℝ)*x 1 + (5162715101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070000119/5000000000 : ℝ)^8357 ≤ (3243364002331/25000000000000 : ℝ)^6309 := by
    have hnat : (1070000119 : ℕ)^8357*25000000000000^6309 ≤ 3243364002331^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070000119 5000000000 3243364002331 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376666883/2500000000 : ℝ)^8357 ≤ (45370893270971/100000000000000 : ℝ)^6309 := by
    have hnat : (1376666883 : ℕ)^8357*100000000000000^6309 ≤ 45370893270971^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376666883 2500000000 45370893270971 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162715101/10000000000 : ℝ)^8357 ≤ (20827825351043/50000000000000 : ℝ)^6309 := by
    have hnat : (5162715101 : ℕ)^8357*50000000000000^6309 ≤ 20827825351043^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162715101 10000000000 20827825351043 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070000119/5000000000 : ℝ), (1376666883/2500000000 : ℝ), (5162715101/10000000000 : ℝ)] ![(3243364002331/25000000000000 : ℝ), (45370893270971/100000000000000 : ℝ), (20827825351043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070000119/5000000000 : ℝ)|^8357 ≤ (3243364002331/25000000000000 : ℝ)^6309
        have hw : |(-1070000119/5000000000 : ℝ)|=(1070000119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376666883/2500000000 : ℝ)|^8357 ≤ (45370893270971/100000000000000 : ℝ)^6309
        have hw : |(1376666883/2500000000 : ℝ)|=(1376666883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162715101/10000000000 : ℝ)|^8357 ≤ (20827825351043/50000000000000 : ℝ)^6309
        have hw : |(5162715101/10000000000 : ℝ)|=(5162715101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343230763/2500000000 : ℝ)*x 0 + (-2318669153/10000000000 : ℝ)*x 1 + (2581358869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343230763/2500000000 : ℝ)^8357 ≤ (2195850538639/5000000000000 : ℝ)^6309 := by
    have hnat : (1343230763 : ℕ)^8357*5000000000000^6309 ≤ 2195850538639^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343230763 2500000000 2195850538639 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2318669153/10000000000 : ℝ)^8357 ≤ (7213655162129/50000000000000 : ℝ)^6309 := by
    have hnat : (2318669153 : ℕ)^8357*50000000000000^6309 ≤ 7213655162129^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318669153 10000000000 7213655162129 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581358869/5000000000 : ℝ)^8357 ≤ (41655678885643/100000000000000 : ℝ)^6309 := by
    have hnat : (2581358869 : ℕ)^8357*100000000000000^6309 ≤ 41655678885643^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581358869 5000000000 41655678885643 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343230763/2500000000 : ℝ), (-2318669153/10000000000 : ℝ), (2581358869/5000000000 : ℝ)] ![(2195850538639/5000000000000 : ℝ), (7213655162129/50000000000000 : ℝ), (41655678885643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343230763/2500000000 : ℝ)|^8357 ≤ (2195850538639/5000000000000 : ℝ)^6309
        have hw : |(1343230763/2500000000 : ℝ)|=(1343230763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2318669153/10000000000 : ℝ)|^8357 ≤ (7213655162129/50000000000000 : ℝ)^6309
        have hw : |(-2318669153/10000000000 : ℝ)|=(2318669153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581358869/5000000000 : ℝ)|^8357 ≤ (41655678885643/100000000000000 : ℝ)^6309
        have hw : |(2581358869/5000000000 : ℝ)|=(2581358869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074584689/2000000000 : ℝ)*x 0 + (2581358509/5000000000 : ℝ)*x 1 + (-231866957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074584689/2000000000 : ℝ)^8357 ≤ (43917015027829/100000000000000 : ℝ)^6309 := by
    have hnat : (1074584689 : ℕ)^8357*100000000000000^6309 ≤ 43917015027829^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074584689 2000000000 43917015027829 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581358509/5000000000 : ℝ)^8357 ≤ (20827835595237/50000000000000 : ℝ)^6309 := by
    have hnat : (2581358509 : ℕ)^8357*50000000000000^6309 ≤ 20827835595237^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581358509 5000000000 20827835595237 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231866957/1000000000 : ℝ)^8357 ≤ (14427313761203/100000000000000 : ℝ)^6309 := by
    have hnat : (231866957 : ℕ)^8357*100000000000000^6309 ≤ 14427313761203^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231866957 1000000000 14427313761203 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074584689/2000000000 : ℝ), (2581358509/5000000000 : ℝ), (-231866957/1000000000 : ℝ)] ![(43917015027829/100000000000000 : ℝ), (20827835595237/50000000000000 : ℝ), (14427313761203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074584689/2000000000 : ℝ)|^8357 ≤ (43917015027829/100000000000000 : ℝ)^6309
        have hw : |(1074584689/2000000000 : ℝ)|=(1074584689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2581358509/5000000000 : ℝ)|^8357 ≤ (20827835595237/50000000000000 : ℝ)^6309
        have hw : |(2581358509/5000000000 : ℝ)|=(2581358509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231866957/1000000000 : ℝ)|^8357 ≤ (14427313761203/100000000000000 : ℝ)^6309
        have hw : |(-231866957/1000000000 : ℝ)|=(231866957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351339389/10000000000 : ℝ)*x 0 + (2010550029/5000000000 : ℝ)*x 1 + (4708333779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351339389/10000000000 : ℝ)^8357 ≤ (6642695090063/20000000000000 : ℝ)^6309 := by
    have hnat : (4351339389 : ℕ)^8357*20000000000000^6309 ≤ 6642695090063^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351339389 10000000000 6642695090063 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010550029/5000000000 : ℝ)^8357 ≤ (29916380233869/100000000000000 : ℝ)^6309 := by
    have hnat : (2010550029 : ℕ)^8357*100000000000000^6309 ≤ 29916380233869^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010550029 5000000000 29916380233869 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4708333779/10000000000 : ℝ)^8357 ≤ (2304384018813/6250000000000 : ℝ)^6309 := by
    have hnat : (4708333779 : ℕ)^8357*6250000000000^6309 ≤ 2304384018813^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708333779 10000000000 2304384018813 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351339389/10000000000 : ℝ), (2010550029/5000000000 : ℝ), (4708333779/10000000000 : ℝ)] ![(6642695090063/20000000000000 : ℝ), (29916380233869/100000000000000 : ℝ), (2304384018813/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351339389/10000000000 : ℝ)|^8357 ≤ (6642695090063/20000000000000 : ℝ)^6309
        have hw : |(4351339389/10000000000 : ℝ)|=(4351339389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010550029/5000000000 : ℝ)|^8357 ≤ (29916380233869/100000000000000 : ℝ)^6309
        have hw : |(2010550029/5000000000 : ℝ)|=(2010550029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4708333779/10000000000 : ℝ)|^8357 ≤ (2304384018813/6250000000000 : ℝ)^6309
        have hw : |(4708333779/10000000000 : ℝ)|=(4708333779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21400963/100000000 : ℝ)*x 0 + (1291262789/2500000000 : ℝ)*x 1 + (1100861773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21400963/100000000 : ℝ)^8357 ≤ (3243556855391/25000000000000 : ℝ)^6309 := by
    have hnat : (21400963 : ℕ)^8357*25000000000000^6309 ≤ 3243556855391^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21400963 100000000 3243556855391 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291262789/2500000000 : ℝ)^8357 ≤ (20840309835041/50000000000000 : ℝ)^6309 := by
    have hnat : (1291262789 : ℕ)^8357*50000000000000^6309 ≤ 20840309835041^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291262789 2500000000 20840309835041 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100861773/2000000000 : ℝ)^8357 ≤ (22672576450573/50000000000000 : ℝ)^6309 := by
    have hnat : (1100861773 : ℕ)^8357*50000000000000^6309 ≤ 22672576450573^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100861773 2000000000 22672576450573 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21400963/100000000 : ℝ), (1291262789/2500000000 : ℝ), (1100861773/2000000000 : ℝ)] ![(3243556855391/25000000000000 : ℝ), (20840309835041/50000000000000 : ℝ), (22672576450573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21400963/100000000 : ℝ)|^8357 ≤ (3243556855391/25000000000000 : ℝ)^6309
        have hw : |(-21400963/100000000 : ℝ)|=(21400963/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291262789/2500000000 : ℝ)|^8357 ≤ (20840309835041/50000000000000 : ℝ)^6309
        have hw : |(1291262789/2500000000 : ℝ)|=(1291262789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100861773/2000000000 : ℝ)|^8357 ≤ (22672576450573/50000000000000 : ℝ)^6309
        have hw : |(1100861773/2000000000 : ℝ)|=(1100861773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660690741/1250000000 : ℝ)*x 0 + (-494269229/2500000000 : ℝ)*x 1 + (5504308859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660690741/1250000000 : ℝ)^8357 ≤ (21486630547209/50000000000000 : ℝ)^6309 := by
    have hnat : (660690741 : ℕ)^8357*50000000000000^6309 ≤ 21486630547209^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660690741 1250000000 21486630547209 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494269229/2500000000 : ℝ)^8357 ≤ (11681586054733/100000000000000 : ℝ)^6309 := by
    have hnat : (494269229 : ℕ)^8357*100000000000000^6309 ≤ 11681586054733^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494269229 2500000000 11681586054733 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504308859/10000000000 : ℝ)^8357 ≤ (5668144104459/12500000000000 : ℝ)^6309 := by
    have hnat : (5504308859 : ℕ)^8357*12500000000000^6309 ≤ 5668144104459^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504308859 10000000000 5668144104459 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660690741/1250000000 : ℝ), (-494269229/2500000000 : ℝ), (5504308859/10000000000 : ℝ)] ![(21486630547209/50000000000000 : ℝ), (11681586054733/100000000000000 : ℝ), (5668144104459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660690741/1250000000 : ℝ)|^8357 ≤ (21486630547209/50000000000000 : ℝ)^6309
        have hw : |(660690741/1250000000 : ℝ)|=(660690741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494269229/2500000000 : ℝ)|^8357 ≤ (11681586054733/100000000000000 : ℝ)^6309
        have hw : |(-494269229/2500000000 : ℝ)|=(494269229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504308859/10000000000 : ℝ)|^8357 ≤ (5668144104459/12500000000000 : ℝ)^6309
        have hw : |(5504308859/10000000000 : ℝ)|=(5504308859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285526049/10000000000 : ℝ)*x 0 + (2752154427/5000000000 : ℝ)*x 1 + (-494269189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285526049/10000000000 : ℝ)^8357 ≤ (42973262397541/100000000000000 : ℝ)^6309 := by
    have hnat : (5285526049 : ℕ)^8357*100000000000000^6309 ≤ 42973262397541^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285526049 10000000000 42973262397541 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752154427/5000000000 : ℝ)^8357 ≤ (4534515278111/10000000000000 : ℝ)^6309 := by
    have hnat : (2752154427 : ℕ)^8357*10000000000000^6309 ≤ 4534515278111^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752154427 5000000000 4534515278111 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494269189/2500000000 : ℝ)^8357 ≤ (11681584802491/100000000000000 : ℝ)^6309 := by
    have hnat : (494269189 : ℕ)^8357*100000000000000^6309 ≤ 11681584802491^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494269189 2500000000 11681584802491 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285526049/10000000000 : ℝ), (2752154427/5000000000 : ℝ), (-494269189/2500000000 : ℝ)] ![(42973262397541/100000000000000 : ℝ), (4534515278111/10000000000000 : ℝ), (11681584802491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285526049/10000000000 : ℝ)|^8357 ≤ (42973262397541/100000000000000 : ℝ)^6309
        have hw : |(5285526049/10000000000 : ℝ)|=(5285526049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752154427/5000000000 : ℝ)|^8357 ≤ (4534515278111/10000000000000 : ℝ)^6309
        have hw : |(2752154427/5000000000 : ℝ)|=(2752154427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494269189/2500000000 : ℝ)|^8357 ≤ (11681584802491/100000000000000 : ℝ)^6309
        have hw : |(-494269189/2500000000 : ℝ)|=(494269189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s2_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175766463/5000000000 : ℝ)*x 0 + (36747411/78125000 : ℝ)*x 1 + (805162029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175766463/5000000000 : ℝ)^8357 ≤ (33215432259053/100000000000000 : ℝ)^6309 := by
    have hnat : (2175766463 : ℕ)^8357*100000000000000^6309 ≤ 33215432259053^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175766463 5000000000 33215432259053 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36747411/78125000 : ℝ)^8357 ≤ (36821761036007/100000000000000 : ℝ)^6309 := by
    have hnat : (36747411 : ℕ)^8357*100000000000000^6309 ≤ 36821761036007^6309*78125000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36747411 78125000 36821761036007 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805162029/2000000000 : ℝ)^8357 ≤ (29962806687011/100000000000000 : ℝ)^6309 := by
    have hnat : (805162029 : ℕ)^8357*100000000000000^6309 ≤ 29962806687011^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805162029 2000000000 29962806687011 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175766463/5000000000 : ℝ), (36747411/78125000 : ℝ), (805162029/2000000000 : ℝ)] ![(33215432259053/100000000000000 : ℝ), (36821761036007/100000000000000 : ℝ), (29962806687011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175766463/5000000000 : ℝ)|^8357 ≤ (33215432259053/100000000000000 : ℝ)^6309
        have hw : |(2175766463/5000000000 : ℝ)|=(2175766463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36747411/78125000 : ℝ)|^8357 ≤ (36821761036007/100000000000000 : ℝ)^6309
        have hw : |(36747411/78125000 : ℝ)|=(36747411/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805162029/2000000000 : ℝ)|^8357 ≤ (29962806687011/100000000000000 : ℝ)^6309
        have hw : |(805162029/2000000000 : ℝ)|=(805162029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8219/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1443/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10169/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1443/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1443/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10169/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1443/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1443/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10169/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1443/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1443/25000 : ℝ) ^ (2089/512 : ℝ) ≤ (883313003994011/100000000000000000000 : ℝ) := by
    have hpowers : (1443/25000 : ℝ)^2089 ≤ (883313003994011/100000000000000000000 : ℝ)^512 := by
      have hnat : (1443 : ℕ)^2089*100000000000000000000^512 ≤ 883313003994011^512*25000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1443 25000 883313003994011 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1443/25000 : ℝ)) (X := (883313003994011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10169/50000 : ℝ) ^ (2089/512 : ℝ) ≤ (3012129147634267/2000000000000000000 : ℝ) := by
    have hpowers : (10169/50000 : ℝ)^2089 ≤ (3012129147634267/2000000000000000000 : ℝ)^512 := by
      have hnat : (10169 : ℕ)^2089*2000000000000000000^512 ≤ 3012129147634267^512*50000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10169 50000 3012129147634267 2000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10169/50000 : ℝ)) (X := (3012129147634267/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000883313003994011/50000000000000000000 : ℝ) ≤ (10000043298539239/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50000883313003994011/50000000000000000000 : ℝ)^512 ≤ (10000043298539239/10000000000000000 : ℝ)^2089 := by
      have hnat : (50000883313003994011 : ℕ)^512*10000000000000000^2089 ≤ 10000043298539239^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000883313003994011 50000000000000000000 10000043298539239 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043298539239/10000000000000000 : ℝ)) (X := (50000883313003994011/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100151489770385707361/100000000000000000000 : ℝ) ≤ (5001855396148027/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (100151489770385707361/100000000000000000000 : ℝ)^512 ≤ (5001855396148027/5000000000000000 : ℝ)^2089 := by
      have hnat : (100151489770385707361 : ℕ)^512*5000000000000000^2089 ≤ 5001855396148027^2089*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100151489770385707361 100000000000000000000 5001855396148027 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001855396148027/5000000000000000 : ℝ)) (X := (100151489770385707361/100000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1003012129147634267/1000000000000000000 : ℝ) ≤ (10007378286052869/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (1003012129147634267/1000000000000000000 : ℝ)^512 ≤ (10007378286052869/10000000000000000 : ℝ)^2089 := by
      have hnat : (1003012129147634267 : ℕ)^512*10000000000000000^2089 ≤ 10007378286052869^2089*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1003012129147634267 1000000000000000000 10007378286052869 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007378286052869/10000000000000000 : ℝ)) (X := (1003012129147634267/1000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(883313003994011/100000000000000000000 : ℝ) ≤ ((72809146569296941457/72830000000000000000 : ℝ)+2*(733498751363/291320000000000 : ℝ)*(1443/25000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (72809146569296941457/72830000000000000000 : ℝ)+2*(733498751363/291320000000000 : ℝ)*(1443/25000 : ℝ)=(10000043298539239/10000000000000000 : ℝ) by norm_num, show 1+2*(883313003994011/100000000000000000000 : ℝ)=(50000883313003994011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3012129147634267/2000000000000000000 : ℝ)+(883313003994011/100000000000000000000 : ℝ) ≤ ((72809146569296941457/72830000000000000000 : ℝ)+(733498751363/291320000000000 : ℝ)*((10169/50000 : ℝ)+(1443/25000 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (72809146569296941457/72830000000000000000 : ℝ)+(733498751363/291320000000000 : ℝ)*((10169/50000 : ℝ)+(1443/25000 : ℝ))=(5001855396148027/5000000000000000 : ℝ) by norm_num, show 1+(3012129147634267/2000000000000000000 : ℝ)+(883313003994011/100000000000000000000 : ℝ)=(100151489770385707361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3012129147634267/2000000000000000000 : ℝ) ≤ ((72809146569296941457/72830000000000000000 : ℝ)+2*(733498751363/291320000000000 : ℝ)*(10169/50000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (72809146569296941457/72830000000000000000 : ℝ)+2*(733498751363/291320000000000 : ℝ)*(10169/50000 : ℝ)=(10007378286052869/10000000000000000 : ℝ) by norm_num, show 1+2*(3012129147634267/2000000000000000000 : ℝ)=(1003012129147634267/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72809146569296941457/72830000000000000000 : ℝ)*(X 1 0+X 2 0)+(733498751363/291320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (1443/25000 : ℝ)) (hi := (10169/50000 : ℝ)) (c := (72809146569296941457/72830000000000000000 : ℝ)) (alpha := (733498751363/291320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72809146569296941457/72830000000000000000 : ℝ)*(X 0 1+X 2 1)+(733498751363/291320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (1443/25000 : ℝ)) (hi := (10169/50000 : ℝ)) (c := (72809146569296941457/72830000000000000000 : ℝ)) (alpha := (733498751363/291320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72809146569296941457/72830000000000000000 : ℝ)*(X 0 2+X 1 2)+(733498751363/291320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (1443/25000 : ℝ)) (hi := (10169/50000 : ℝ)) (c := (72809146569296941457/72830000000000000000 : ℝ)) (alpha := (733498751363/291320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070000119/5000000000 : ℝ)*X 0 0+(1376666883/2500000000 : ℝ)*X 0 1+(5162715101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343230763/2500000000 : ℝ)*X 1 0+(-2318669153/10000000000 : ℝ)*X 1 1+(2581358869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074584689/2000000000 : ℝ)*X 2 0+(2581358509/5000000000 : ℝ)*X 2 1+(-231866957/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351339389/10000000000 : ℝ)*X 0 0+(2010550029/5000000000 : ℝ)*X 0 1+(4708333779/10000000000 : ℝ)*X 0 2+(4351339389/10000000000 : ℝ)*X 1 0+(2010550029/5000000000 : ℝ)*X 1 1+(4708333779/10000000000 : ℝ)*X 1 2+(4351339389/10000000000 : ℝ)*X 2 0+(2010550029/5000000000 : ℝ)*X 2 1+(4708333779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21400963/100000000 : ℝ)*X 0 0+(1291262789/2500000000 : ℝ)*X 0 1+(1100861773/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660690741/1250000000 : ℝ)*X 1 0+(-494269229/2500000000 : ℝ)*X 1 1+(5504308859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285526049/10000000000 : ℝ)*X 2 0+(2752154427/5000000000 : ℝ)*X 2 1+(-494269189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175766463/5000000000 : ℝ)*X 0 0+(36747411/78125000 : ℝ)*X 0 1+(805162029/2000000000 : ℝ)*X 0 2+(2175766463/5000000000 : ℝ)*X 1 0+(36747411/78125000 : ℝ)*X 1 1+(805162029/2000000000 : ℝ)*X 1 2+(2175766463/5000000000 : ℝ)*X 2 0+(36747411/78125000 : ℝ)*X 2 1+(805162029/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1694250530481272316896537091/364150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6878171/25000000000000 : ℝ)*(base19) + (101333117/50000000000000 : ℝ)*(base23) + (111203679/100000000000000 : ℝ)*(upper2) + (6312143/2500000000000 : ℝ)*(upper3) + (26271271/20000000000000 : ℝ)*(upper4) + (436252947809321/20000000000000 : ℝ)*(major0) + (436252947809321/20000000000000 : ℝ)*(major1) + (436252947809321/20000000000000 : ℝ)*(major2) + (1453698865978279/50000000000000 : ℝ)*(sp0) + (290741314699149/10000000000000 : ℝ)*(sp1) + (145370648591897/5000000000000 : ℝ)*(sp2) + (727555655435789/50000000000000 : ℝ)*(sp3) + (482579613/3125000000000 : ℝ)*(sp4) + (967526043/20000000000000 : ℝ)*(sp7) + (1455116148501793/100000000000000 : ℝ)*(f.failure) + (1453706587252087/50000000000000 : ℝ)*(f.sum) + (29098659036967/14566000000000000000000000000 : ℝ)*base65 + (6004525110726929303/1456600000000000000000000000000000 : ℝ)*base68 + (14604439266774329303/1456600000000000000000000000000000 : ℝ)*base70 + (15179519187952529303/1456600000000000000000000000000000 : ℝ)*base72 + (38395103437531/14566000000000000000000000000 : ℝ)*base73 + (5226923368059529303/1456600000000000000000000000000000 : ℝ)*base76 + (2795033787364529303/1456600000000000000000000000000000 : ℝ)*base78 + (991314985484270697/1456600000000000000000000000000000 : ℝ)*base79 + (25212351553927/14566000000000000000000000000 : ℝ)*base82 + (864911/312500000000000000000 : ℝ)*base90 + (864911/312500000000000000000 : ℝ)*base92 + (864911/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61681630162652667947769/7283000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238301481/12500000000000 : ℝ)*(base19) + (31976999/1562500000000 : ℝ)*(base23) + (225073717/100000000000000 : ℝ)*(upper3) + (840783/5000000000000 : ℝ)*(lower4) + (183329379/100000000000000 : ℝ)*(upper5) + (13821394192517/625000000000 : ℝ)*(major0) + (13821394192517/625000000000 : ℝ)*(major1) + (13821394192517/625000000000 : ℝ)*(major2) + (4612397413/25000000000000 : ℝ)*(sp1) + (5229592291/25000000000000 : ℝ)*(sp2) + (1473805582269211/50000000000000 : ℝ)*(sp4) + (1473795404268461/50000000000000 : ℝ)*(sp5) + (2947588199641321/100000000000000 : ℝ)*(sp6) + (14752346947583/1000000000000 : ℝ)*(sp7) + (14752346947583/1000000000000 : ℝ)*(f.failure) + (1473805582269211/50000000000000 : ℝ)*(f.sum) + (363826714951/91037500000000000000000000 : ℝ)*base65 + (181163144656377269/45518750000000000000000000000000 : ℝ)*base67 + (58816361820710231/45518750000000000000000000000000 : ℝ)*base70 + (34174220744477269/45518750000000000000000000000000 : ℝ)*base71 + (10726123804161/1820750000000000000000000000 : ℝ)*base73 + (420559701025410231/45518750000000000000000000000000 : ℝ)*base76 + (5661476402316481/45518750000000000000000000000000 : ℝ)*base78 + (97578281475864769/45518750000000000000000000000000 : ℝ)*base79 + (380606932677/113796875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (21241/3125000000000000000 : ℝ)*base90 + (21241/3125000000000000000 : ℝ)*base92 + (21241/3125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1164_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10169/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1164_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1164_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1164_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1164_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

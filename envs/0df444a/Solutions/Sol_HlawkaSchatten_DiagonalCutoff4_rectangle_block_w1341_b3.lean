-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:11.790263+00:00
-- url     : https://prove2.me/submissions/101ed425-e974-4bfe-9711-e0bb5ba548e4

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
theorem support_rectangle_w1341_s9_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069800309/2000000000 : ℝ)*x 0 + (-2130466347/10000000000 : ℝ)*x 1 + (5244635331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069800309/2000000000 : ℝ)^4301 ≤ (1374716526023/3125000000000 : ℝ)^3277 := by
    have hnat : (1069800309 : ℕ)^4301*3125000000000^3277 ≤ 1374716526023^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069800309 2000000000 1374716526023 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130466347/10000000000 : ℝ)^4301 ≤ (13141224146349/100000000000000 : ℝ)^3277 := by
    have hnat : (2130466347 : ℕ)^4301*100000000000000^3277 ≤ 13141224146349^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130466347 10000000000 13141224146349 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244635331/10000000000 : ℝ)^4301 ≤ (42867847006989/100000000000000 : ℝ)^3277 := by
    have hnat : (5244635331 : ℕ)^4301*100000000000000^3277 ≤ 42867847006989^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244635331 10000000000 42867847006989 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069800309/2000000000 : ℝ), (-2130466347/10000000000 : ℝ), (5244635331/10000000000 : ℝ)] ![(1374716526023/3125000000000 : ℝ), (13141224146349/100000000000000 : ℝ), (42867847006989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069800309/2000000000 : ℝ)|^4301 ≤ (1374716526023/3125000000000 : ℝ)^3277
        have hw : |(1069800309/2000000000 : ℝ)|=(1069800309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130466347/10000000000 : ℝ)|^4301 ≤ (13141224146349/100000000000000 : ℝ)^3277
        have hw : |(-2130466347/10000000000 : ℝ)|=(2130466347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244635331/10000000000 : ℝ)|^4301 ≤ (42867847006989/100000000000000 : ℝ)^3277
        have hw : |(5244635331/10000000000 : ℝ)|=(5244635331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s9_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022424331/5000000000 : ℝ)*x 0 + (5245236579/10000000000 : ℝ)*x 1 + (5412095701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022424331/5000000000 : ℝ)^4301 ≤ (6226241178721/50000000000000 : ℝ)^3277 := by
    have hnat : (1022424331 : ℕ)^4301*50000000000000^3277 ≤ 6226241178721^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022424331 5000000000 6226241178721 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245236579/10000000000 : ℝ)^4301 ≤ (2679643573227/6250000000000 : ℝ)^3277 := by
    have hnat : (5245236579 : ℕ)^4301*6250000000000^3277 ≤ 2679643573227^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245236579 10000000000 2679643573227 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412095701/10000000000 : ℝ)^4301 ≤ (44673220450337/100000000000000 : ℝ)^3277 := by
    have hnat : (5412095701 : ℕ)^4301*100000000000000^3277 ≤ 44673220450337^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412095701 10000000000 44673220450337 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022424331/5000000000 : ℝ), (5245236579/10000000000 : ℝ), (5412095701/10000000000 : ℝ)] ![(6226241178721/50000000000000 : ℝ), (2679643573227/6250000000000 : ℝ), (44673220450337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022424331/5000000000 : ℝ)|^4301 ≤ (6226241178721/50000000000000 : ℝ)^3277
        have hw : |(-1022424331/5000000000 : ℝ)|=(1022424331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245236579/10000000000 : ℝ)|^4301 ≤ (2679643573227/6250000000000 : ℝ)^3277
        have hw : |(5245236579/10000000000 : ℝ)|=(5245236579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412095701/10000000000 : ℝ)|^4301 ≤ (44673220450337/100000000000000 : ℝ)^3277
        have hw : |(5412095701/10000000000 : ℝ)|=(5412095701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s9_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305716783/10000000000 : ℝ)*x 0 + (-24537573/125000000 : ℝ)*x 1 + (5412095801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305716783/10000000000 : ℝ)^4301 ≤ (10881075962353/25000000000000 : ℝ)^3277 := by
    have hnat : (5305716783 : ℕ)^4301*25000000000000^3277 ≤ 10881075962353^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305716783 10000000000 10881075962353 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24537573/125000000 : ℝ)^4301 ≤ (5901237302619/50000000000000 : ℝ)^3277 := by
    have hnat : (24537573 : ℕ)^4301*50000000000000^3277 ≤ 5901237302619^3277*125000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24537573 125000000 5901237302619 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412095801/10000000000 : ℝ)^4301 ≤ (22336610766851/50000000000000 : ℝ)^3277 := by
    have hnat : (5412095801 : ℕ)^4301*50000000000000^3277 ≤ 22336610766851^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412095801 10000000000 22336610766851 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305716783/10000000000 : ℝ), (-24537573/125000000 : ℝ), (5412095801/10000000000 : ℝ)] ![(10881075962353/25000000000000 : ℝ), (5901237302619/50000000000000 : ℝ), (22336610766851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305716783/10000000000 : ℝ)|^4301 ≤ (10881075962353/25000000000000 : ℝ)^3277
        have hw : |(5305716783/10000000000 : ℝ)|=(5305716783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24537573/125000000 : ℝ)|^4301 ≤ (5901237302619/50000000000000 : ℝ)^3277
        have hw : |(-24537573/125000000 : ℝ)|=(24537573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412095801/10000000000 : ℝ)|^4301 ≤ (22336610766851/50000000000000 : ℝ)^3277
        have hw : |(5412095801/10000000000 : ℝ)|=(5412095801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s9_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305716699/10000000000 : ℝ)*x 0 + (5412095817/10000000000 : ℝ)*x 1 + (-490751483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305716699/10000000000 : ℝ)^4301 ≤ (43524302945013/100000000000000 : ℝ)^3277 := by
    have hnat : (5305716699 : ℕ)^4301*100000000000000^3277 ≤ 43524302945013^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305716699 10000000000 43524302945013 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412095817/10000000000 : ℝ)^4301 ≤ (279207635669/625000000000 : ℝ)^3277 := by
    have hnat : (5412095817 : ℕ)^4301*625000000000^3277 ≤ 279207635669^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412095817 10000000000 279207635669 625000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490751483/2500000000 : ℝ)^4301 ≤ (11802475331231/100000000000000 : ℝ)^3277 := by
    have hnat : (490751483 : ℕ)^4301*100000000000000^3277 ≤ 11802475331231^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490751483 2500000000 11802475331231 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305716699/10000000000 : ℝ), (5412095817/10000000000 : ℝ), (-490751483/2500000000 : ℝ)] ![(43524302945013/100000000000000 : ℝ), (279207635669/625000000000 : ℝ), (11802475331231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305716699/10000000000 : ℝ)|^4301 ≤ (43524302945013/100000000000000 : ℝ)^3277
        have hw : |(5305716699/10000000000 : ℝ)|=(5305716699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412095817/10000000000 : ℝ)|^4301 ≤ (279207635669/625000000000 : ℝ)^3277
        have hw : |(5412095817/10000000000 : ℝ)|=(5412095817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490751483/2500000000 : ℝ)|^4301 ≤ (11802475331231/100000000000000 : ℝ)^3277
        have hw : |(-490751483/2500000000 : ℝ)|=(490751483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s9_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326909867/10000000000 : ℝ)*x 0 + (2252457903/5000000000 : ℝ)*x 1 + (1038887207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326909867/10000000000 : ℝ)^4301 ≤ (8325884346537/25000000000000 : ℝ)^3277 := by
    have hnat : (4326909867 : ℕ)^4301*25000000000000^3277 ≤ 8325884346537^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326909867 10000000000 8325884346537 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252457903/5000000000 : ℝ)^4301 ≤ (35113196815699/100000000000000 : ℝ)^3277 := by
    have hnat : (2252457903 : ℕ)^4301*100000000000000^3277 ≤ 35113196815699^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252457903 5000000000 35113196815699 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038887207/2500000000 : ℝ)^4301 ≤ (15791632892581/50000000000000 : ℝ)^3277 := by
    have hnat : (1038887207 : ℕ)^4301*50000000000000^3277 ≤ 15791632892581^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038887207 2500000000 15791632892581 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326909867/10000000000 : ℝ), (2252457903/5000000000 : ℝ), (1038887207/2500000000 : ℝ)] ![(8325884346537/25000000000000 : ℝ), (35113196815699/100000000000000 : ℝ), (15791632892581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326909867/10000000000 : ℝ)|^4301 ≤ (8325884346537/25000000000000 : ℝ)^3277
        have hw : |(4326909867/10000000000 : ℝ)|=(4326909867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252457903/5000000000 : ℝ)|^4301 ≤ (35113196815699/100000000000000 : ℝ)^3277
        have hw : |(2252457903/5000000000 : ℝ)|=(2252457903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038887207/2500000000 : ℝ)|^4301 ≤ (15791632892581/50000000000000 : ℝ)^3277
        have hw : |(1038887207/2500000000 : ℝ)|=(1038887207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2787/25000 : ℝ) ^ (1075/256 : ℝ) ≤ (2494087112183817/25000000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^1075 ≤ (2494087112183817/25000000000000000000 : ℝ)^256 := by
      have hnat : (2787 : ℕ)^1075*25000000000000000000^256 ≤ 2494087112183817^256*25000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 2494087112183817 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (2494087112183817/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (1075/256 : ℝ) ≤ (7981188395310401/25000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^1075 ≤ (7981188395310401/25000000000000000000 : ℝ)^256 := by
      have hnat : (7353 : ℕ)^1075*25000000000000000000^256 ≤ 7981188395310401^256*50000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 7981188395310401 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (7981188395310401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502494087112183817/12500000000000000000 : ℝ) ≤ (10000475116485737/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12502494087112183817/12500000000000000000 : ℝ)^256 ≤ (10000475116485737/10000000000000000 : ℝ)^1075 := by
      have hnat : (12502494087112183817 : ℕ)^256*10000000000000000^1075 ≤ 10000475116485737^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502494087112183817 12500000000000000000 10000475116485737 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475116485737/10000000000000000 : ℝ)) (X := (12502494087112183817/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505237637753747109/12500000000000000000 : ℝ) ≤ (10000997671666289/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12505237637753747109/12500000000000000000 : ℝ)^256 ≤ (10000997671666289/10000000000000000 : ℝ)^1075 := by
      have hnat : (12505237637753747109 : ℕ)^256*10000000000000000^1075 ≤ 10000997671666289^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505237637753747109 12500000000000000000 10000997671666289 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000997671666289/10000000000000000 : ℝ)) (X := (12505237637753747109/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507981188395310401/12500000000000000000 : ℝ) ≤ (10001520226846841/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12507981188395310401/12500000000000000000 : ℝ)^256 ≤ (10001520226846841/10000000000000000 : ℝ)^1075 := by
      have hnat : (12507981188395310401 : ℕ)^256*10000000000000000^1075 ≤ 10001520226846841^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507981188395310401 12500000000000000000 10001520226846841 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001520226846841/10000000000000000 : ℝ)) (X := (12507981188395310401/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2494087112183817/25000000000000000000 : ℝ) ≤ ((5928339929025110809/5930000000000000000 : ℝ)+2*(21773132523/14825000000000 : ℝ)*(2787/25000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (5928339929025110809/5930000000000000000 : ℝ)+2*(21773132523/14825000000000 : ℝ)*(2787/25000 : ℝ)=(10000475116485737/10000000000000000 : ℝ) by norm_num, show 1+2*(2494087112183817/25000000000000000000 : ℝ)=(12502494087112183817/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7981188395310401/25000000000000000000 : ℝ)+(2494087112183817/25000000000000000000 : ℝ) ≤ ((5928339929025110809/5930000000000000000 : ℝ)+(21773132523/14825000000000 : ℝ)*((7353/50000 : ℝ)+(2787/25000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (5928339929025110809/5930000000000000000 : ℝ)+(21773132523/14825000000000 : ℝ)*((7353/50000 : ℝ)+(2787/25000 : ℝ))=(10000997671666289/10000000000000000 : ℝ) by norm_num, show 1+(7981188395310401/25000000000000000000 : ℝ)+(2494087112183817/25000000000000000000 : ℝ)=(12505237637753747109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7981188395310401/25000000000000000000 : ℝ) ≤ ((5928339929025110809/5930000000000000000 : ℝ)+2*(21773132523/14825000000000 : ℝ)*(7353/50000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (5928339929025110809/5930000000000000000 : ℝ)+2*(21773132523/14825000000000 : ℝ)*(7353/50000 : ℝ)=(10001520226846841/10000000000000000 : ℝ) by norm_num, show 1+2*(7981188395310401/25000000000000000000 : ℝ)=(12507981188395310401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5928339929025110809/5930000000000000000 : ℝ)*(X 1 0+X 2 0)+(21773132523/14825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (5928339929025110809/5930000000000000000 : ℝ)) (alpha := (21773132523/14825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5928339929025110809/5930000000000000000 : ℝ)*(X 0 1+X 2 1)+(21773132523/14825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (5928339929025110809/5930000000000000000 : ℝ)) (alpha := (21773132523/14825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5928339929025110809/5930000000000000000 : ℝ)*(X 0 2+X 1 2)+(21773132523/14825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (5928339929025110809/5930000000000000000 : ℝ)) (alpha := (21773132523/14825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1069800309/2000000000 : ℝ)*X 1 0+(-2130466347/10000000000 : ℝ)*X 1 1+(5244635331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1022424331/5000000000 : ℝ)*X 0 0+(5245236579/10000000000 : ℝ)*X 0 1+(5412095701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305716783/10000000000 : ℝ)*X 1 0+(-24537573/125000000 : ℝ)*X 1 1+(5412095801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305716699/10000000000 : ℝ)*X 2 0+(5412095817/10000000000 : ℝ)*X 2 1+(-490751483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4326909867/10000000000 : ℝ)*X 0 0+(2252457903/5000000000 : ℝ)*X 0 1+(1038887207/2500000000 : ℝ)*X 0 2+(4326909867/10000000000 : ℝ)*X 1 0+(2252457903/5000000000 : ℝ)*X 1 1+(1038887207/2500000000 : ℝ)*X 1 2+(4326909867/10000000000 : ℝ)*X 2 0+(2252457903/5000000000 : ℝ)*X 2 1+(1038887207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85307686136789245439131239/37062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472698327/100000000000000 : ℝ)*(base19) + (396712819/100000000000000 : ℝ)*(base23) + (160455217/100000000000000 : ℝ)*(lower1) + (31180981/50000000000000 : ℝ)*(upper3) + (119897/500000000000 : ℝ)*(lower4) + (74048591/100000000000000 : ℝ)*(upper5) + (1106922924880257/25000000000000 : ℝ)*(major0) + (1106922924880257/25000000000000 : ℝ)*(major1) + (1106922924880257/25000000000000 : ℝ)*(major2) + (1611812459/50000000000000 : ℝ)*(sp0) + (1498267240686891/25000000000000 : ℝ)*(sp1) + (2996532633212159/50000000000000 : ℝ)*(sp2) + (1198613713206949/20000000000000 : ℝ)*(sp3) + (572462871914063/20000000000000 : ℝ)*(sp4) + (572462871914063/20000000000000 : ℝ)*(f.failure) + (1498267240686891/25000000000000 : ℝ)*(f.sum) + (12119077080629/2965000000000000000000000000 : ℝ)*base66 + (630264680773702087/148250000000000000000000000000000 : ℝ)*base68 + (2323164155182202087/148250000000000000000000000000000 : ℝ)*base70 + (26766055038452087/148250000000000000000000000000000 : ℝ)*base72 + (160475780573/370625000000000000000000000 : ℝ)*base74 + (1773785859611202087/148250000000000000000000000000000 : ℝ)*base76 + (941858016350797913/148250000000000000000000000000000 : ℝ)*base77 + (727400765432952087/148250000000000000000000000000000 : ℝ)*base80 + (4170077249203/370625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4336367/1000000000000000000000 : ℝ)*base89 + (4336367/1000000000000000000000 : ℝ)*base91 + (4336367/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1341_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_box_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-75100453/400000000 : ℝ)*x 0 + (5389979229/10000000000 : ℝ)*x 1 + (1077995873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75100453/400000000 : ℝ)^4301 ≤ (5566227796781/50000000000000 : ℝ)^3277 := by
    have hnat : (75100453 : ℕ)^4301*50000000000000^3277 ≤ 5566227796781^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75100453 400000000 5566227796781 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389979229/10000000000 : ℝ)^4301 ≤ (22216885730043/50000000000000 : ℝ)^3277 := by
    have hnat : (5389979229 : ℕ)^4301*50000000000000^3277 ≤ 22216885730043^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389979229 10000000000 22216885730043 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077995873/2000000000 : ℝ)^4301 ≤ (22216886465789/50000000000000 : ℝ)^3277 := by
    have hnat : (1077995873 : ℕ)^4301*50000000000000^3277 ≤ 22216886465789^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077995873 2000000000 22216886465789 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75100453/400000000 : ℝ), (5389979229/10000000000 : ℝ), (1077995873/2000000000 : ℝ)] ![(5566227796781/50000000000000 : ℝ), (22216885730043/50000000000000 : ℝ), (22216886465789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75100453/400000000 : ℝ)|^4301 ≤ (5566227796781/50000000000000 : ℝ)^3277
        have hw : |(-75100453/400000000 : ℝ)|=(75100453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389979229/10000000000 : ℝ)|^4301 ≤ (22216885730043/50000000000000 : ℝ)^3277
        have hw : |(5389979229/10000000000 : ℝ)|=(5389979229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077995873/2000000000 : ℝ)|^4301 ≤ (22216886465789/50000000000000 : ℝ)^3277
        have hw : |(1077995873/2000000000 : ℝ)|=(1077995873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642576097/5000000000 : ℝ)*x 0 + (-1010561391/5000000000 : ℝ)*x 1 + (2694989919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642576097/5000000000 : ℝ)^4301 ≤ (43303026228993/100000000000000 : ℝ)^3277 := by
    have hnat : (2642576097 : ℕ)^4301*100000000000000^3277 ≤ 43303026228993^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642576097 5000000000 43303026228993 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010561391/5000000000 : ℝ)^4301 ≤ (12263195712151/100000000000000 : ℝ)^3277 := by
    have hnat : (1010561391 : ℕ)^4301*100000000000000^3277 ≤ 12263195712151^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010561391 5000000000 12263195712151 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694989919/5000000000 : ℝ)^4301 ≤ (22216889024671/50000000000000 : ℝ)^3277 := by
    have hnat : (2694989919 : ℕ)^4301*50000000000000^3277 ≤ 22216889024671^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694989919 5000000000 22216889024671 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642576097/5000000000 : ℝ), (-1010561391/5000000000 : ℝ), (2694989919/5000000000 : ℝ)] ![(43303026228993/100000000000000 : ℝ), (12263195712151/100000000000000 : ℝ), (22216889024671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642576097/5000000000 : ℝ)|^4301 ≤ (43303026228993/100000000000000 : ℝ)^3277
        have hw : |(2642576097/5000000000 : ℝ)|=(2642576097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010561391/5000000000 : ℝ)|^4301 ≤ (12263195712151/100000000000000 : ℝ)^3277
        have hw : |(-1010561391/5000000000 : ℝ)|=(1010561391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694989919/5000000000 : ℝ)|^4301 ≤ (22216889024671/50000000000000 : ℝ)^3277
        have hw : |(2694989919/5000000000 : ℝ)|=(2694989919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321288083/2500000000 : ℝ)*x 0 + (1347494851/2500000000 : ℝ)*x 1 + (-126320199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321288083/2500000000 : ℝ)^4301 ≤ (4330302771299/10000000000000 : ℝ)^3277 := by
    have hnat : (1321288083 : ℕ)^4301*10000000000000^3277 ≤ 4330302771299^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321288083 2500000000 4330302771299 10000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347494851/2500000000 : ℝ)^4301 ≤ (888675467071/2000000000000 : ℝ)^3277 := by
    have hnat : (1347494851 : ℕ)^4301*2000000000000^3277 ≤ 888675467071^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347494851 2500000000 888675467071 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126320199/625000000 : ℝ)^4301 ≤ (6131599456739/50000000000000 : ℝ)^3277 := by
    have hnat : (126320199 : ℕ)^4301*50000000000000^3277 ≤ 6131599456739^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126320199 625000000 6131599456739 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321288083/2500000000 : ℝ), (1347494851/2500000000 : ℝ), (-126320199/625000000 : ℝ)] ![(4330302771299/10000000000000 : ℝ), (888675467071/2000000000000 : ℝ), (6131599456739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321288083/2500000000 : ℝ)|^4301 ≤ (4330302771299/10000000000000 : ℝ)^3277
        have hw : |(1321288083/2500000000 : ℝ)|=(1321288083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347494851/2500000000 : ℝ)|^4301 ≤ (888675467071/2000000000000 : ℝ)^3277
        have hw : |(1347494851/2500000000 : ℝ)|=(1347494851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126320199/625000000 : ℝ)|^4301 ≤ (6131599456739/50000000000000 : ℝ)^3277
        have hw : |(-126320199/625000000 : ℝ)|=(126320199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2237545011/5000000000 : ℝ)*x 0 + (4256671793/10000000000 : ℝ)*x 1 + (4256672013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237545011/5000000000 : ℝ)^4301 ≤ (34808394403213/100000000000000 : ℝ)^3277 := by
    have hnat : (2237545011 : ℕ)^4301*100000000000000^3277 ≤ 34808394403213^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237545011 5000000000 34808394403213 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4256671793/10000000000 : ℝ)^4301 ≤ (32595801680239/100000000000000 : ℝ)^3277 := by
    have hnat : (4256671793 : ℕ)^4301*100000000000000^3277 ≤ 32595801680239^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256671793 10000000000 32595801680239 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4256672013/10000000000 : ℝ)^4301 ≤ (32595803891333/100000000000000 : ℝ)^3277 := by
    have hnat : (4256672013 : ℕ)^4301*100000000000000^3277 ≤ 32595803891333^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256672013 10000000000 32595803891333 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237545011/5000000000 : ℝ), (4256671793/10000000000 : ℝ), (4256672013/10000000000 : ℝ)] ![(34808394403213/100000000000000 : ℝ), (32595801680239/100000000000000 : ℝ), (32595803891333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237545011/5000000000 : ℝ)|^4301 ≤ (34808394403213/100000000000000 : ℝ)^3277
        have hw : |(2237545011/5000000000 : ℝ)|=(2237545011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4256671793/10000000000 : ℝ)|^4301 ≤ (32595801680239/100000000000000 : ℝ)^3277
        have hw : |(4256671793/10000000000 : ℝ)|=(4256671793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4256672013/10000000000 : ℝ)|^4301 ≤ (32595803891333/100000000000000 : ℝ)^3277
        have hw : |(4256672013/10000000000 : ℝ)|=(4256672013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107458253/5000000000 : ℝ)*x 0 + (5264907493/10000000000 : ℝ)*x 1 + (329056661/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107458253/5000000000 : ℝ)^4301 ≤ (13829103278489/100000000000000 : ℝ)^3277 := by
    have hnat : (1107458253 : ℕ)^4301*100000000000000^3277 ≤ 13829103278489^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107458253 5000000000 13829103278489 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264907493/10000000000 : ℝ)^4301 ≤ (43085453280881/100000000000000 : ℝ)^3277 := by
    have hnat : (5264907493 : ℕ)^4301*100000000000000^3277 ≤ 43085453280881^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264907493 10000000000 43085453280881 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329056661/625000000 : ℝ)^4301 ≤ (10771360857913/25000000000000 : ℝ)^3277 := by
    have hnat : (329056661 : ℕ)^4301*25000000000000^3277 ≤ 10771360857913^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329056661 625000000 10771360857913 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107458253/5000000000 : ℝ), (5264907493/10000000000 : ℝ), (329056661/625000000 : ℝ)] ![(13829103278489/100000000000000 : ℝ), (43085453280881/100000000000000 : ℝ), (10771360857913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107458253/5000000000 : ℝ)|^4301 ≤ (13829103278489/100000000000000 : ℝ)^3277
        have hw : |(-1107458253/5000000000 : ℝ)|=(1107458253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264907493/10000000000 : ℝ)|^4301 ≤ (43085453280881/100000000000000 : ℝ)^3277
        have hw : |(5264907493/10000000000 : ℝ)|=(5264907493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329056661/625000000 : ℝ)|^4301 ≤ (10771360857913/25000000000000 : ℝ)^3277
        have hw : |(329056661/625000000 : ℝ)|=(329056661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074601089/2000000000 : ℝ)*x 0 + (-517825857/2500000000 : ℝ)*x 1 + (5264906283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074601089/2000000000 : ℝ)^4301 ≤ (8850041800121/20000000000000 : ℝ)^3277 := by
    have hnat : (1074601089 : ℕ)^4301*20000000000000^3277 ≤ 8850041800121^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074601089 2000000000 8850041800121 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517825857/2500000000 : ℝ)^4301 ≤ (12664350700509/100000000000000 : ℝ)^3277 := by
    have hnat : (517825857 : ℕ)^4301*100000000000000^3277 ≤ 12664350700509^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517825857 2500000000 12664350700509 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264906283/10000000000 : ℝ)^4301 ≤ (344683522277/800000000000 : ℝ)^3277 := by
    have hnat : (5264906283 : ℕ)^4301*800000000000^3277 ≤ 344683522277^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264906283 10000000000 344683522277 800000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074601089/2000000000 : ℝ), (-517825857/2500000000 : ℝ), (5264906283/10000000000 : ℝ)] ![(8850041800121/20000000000000 : ℝ), (12664350700509/100000000000000 : ℝ), (344683522277/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074601089/2000000000 : ℝ)|^4301 ≤ (8850041800121/20000000000000 : ℝ)^3277
        have hw : |(1074601089/2000000000 : ℝ)|=(1074601089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517825857/2500000000 : ℝ)|^4301 ≤ (12664350700509/100000000000000 : ℝ)^3277
        have hw : |(-517825857/2500000000 : ℝ)|=(517825857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264906283/10000000000 : ℝ)|^4301 ≤ (344683522277/800000000000 : ℝ)^3277
        have hw : |(5264906283/10000000000 : ℝ)|=(5264906283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373004771/10000000000 : ℝ)*x 0 + (1316226649/2500000000 : ℝ)*x 1 + (-2071303917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373004771/10000000000 : ℝ)^4301 ≤ (44250201715247/100000000000000 : ℝ)^3277 := by
    have hnat : (5373004771 : ℕ)^4301*100000000000000^3277 ≤ 44250201715247^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373004771 10000000000 44250201715247 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316226649/2500000000 : ℝ)^4301 ≤ (21542721823233/50000000000000 : ℝ)^3277 := by
    have hnat : (1316226649 : ℕ)^4301*50000000000000^3277 ≤ 21542721823233^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316226649 2500000000 21542721823233 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071303917/10000000000 : ℝ)^4301 ≤ (12664354624619/100000000000000 : ℝ)^3277 := by
    have hnat : (2071303917 : ℕ)^4301*100000000000000^3277 ≤ 12664354624619^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071303917 10000000000 12664354624619 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373004771/10000000000 : ℝ), (1316226649/2500000000 : ℝ), (-2071303917/10000000000 : ℝ)] ![(44250201715247/100000000000000 : ℝ), (21542721823233/50000000000000 : ℝ), (12664354624619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373004771/10000000000 : ℝ)|^4301 ≤ (44250201715247/100000000000000 : ℝ)^3277
        have hw : |(5373004771/10000000000 : ℝ)|=(5373004771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316226649/2500000000 : ℝ)|^4301 ≤ (21542721823233/50000000000000 : ℝ)^3277
        have hw : |(1316226649/2500000000 : ℝ)|=(1316226649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071303917/10000000000 : ℝ)|^4301 ≤ (12664354624619/100000000000000 : ℝ)^3277
        have hw : |(-2071303917/10000000000 : ℝ)|=(2071303917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65277389/156250000 : ℝ)*x 0 + (176211457/400000000 : ℝ)*x 1 + (2202643627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65277389/156250000 : ℝ)^4301 ≤ (15902470251203/50000000000000 : ℝ)^3277 := by
    have hnat : (65277389 : ℕ)^4301*50000000000000^3277 ≤ 15902470251203^3277*156250000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65277389 156250000 15902470251203 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176211457/400000000 : ℝ)^4301 ≤ (1704876276419/5000000000000 : ℝ)^3277 := by
    have hnat : (176211457 : ℕ)^4301*5000000000000^3277 ≤ 1704876276419^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176211457 400000000 1704876276419 5000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202643627/5000000000 : ℝ)^4301 ≤ (8524383487503/25000000000000 : ℝ)^3277 := by
    have hnat : (2202643627 : ℕ)^4301*25000000000000^3277 ≤ 8524383487503^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202643627 5000000000 8524383487503 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65277389/156250000 : ℝ), (176211457/400000000 : ℝ), (2202643627/5000000000 : ℝ)] ![(15902470251203/50000000000000 : ℝ), (1704876276419/5000000000000 : ℝ), (8524383487503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65277389/156250000 : ℝ)|^4301 ≤ (15902470251203/50000000000000 : ℝ)^3277
        have hw : |(65277389/156250000 : ℝ)|=(65277389/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176211457/400000000 : ℝ)|^4301 ≤ (1704876276419/5000000000000 : ℝ)^3277
        have hw : |(176211457/400000000 : ℝ)|=(176211457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2202643627/5000000000 : ℝ)|^4301 ≤ (8524383487503/25000000000000 : ℝ)^3277
        have hw : |(2202643627/5000000000 : ℝ)|=(2202643627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_8 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-428812901/2000000000 : ℝ)*x 0 + (323675481/625000000 : ℝ)*x 1 + (2701999651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428812901/2000000000 : ℝ)^4301 ≤ (828213769399/6250000000000 : ℝ)^3277 := by
    have hnat : (428812901 : ℕ)^4301*6250000000000^3277 ≤ 828213769399^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428812901 2000000000 828213769399 6250000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323675481/625000000 : ℝ)^4301 ≤ (5270381532889/12500000000000 : ℝ)^3277 := by
    have hnat : (323675481 : ℕ)^4301*12500000000000^3277 ≤ 5270381532889^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323675481 625000000 5270381532889 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701999651/5000000000 : ℝ)^4301 ≤ (44585527407047/100000000000000 : ℝ)^3277 := by
    have hnat : (2701999651 : ℕ)^4301*100000000000000^3277 ≤ 44585527407047^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701999651 5000000000 44585527407047 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428812901/2000000000 : ℝ), (323675481/625000000 : ℝ), (2701999651/5000000000 : ℝ)] ![(828213769399/6250000000000 : ℝ), (5270381532889/12500000000000 : ℝ), (44585527407047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428812901/2000000000 : ℝ)|^4301 ≤ (828213769399/6250000000000 : ℝ)^3277
        have hw : |(-428812901/2000000000 : ℝ)|=(428812901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323675481/625000000 : ℝ)|^4301 ≤ (5270381532889/12500000000000 : ℝ)^3277
        have hw : |(323675481/625000000 : ℝ)|=(323675481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701999651/5000000000 : ℝ)|^4301 ≤ (44585527407047/100000000000000 : ℝ)^3277
        have hw : |(2701999651/5000000000 : ℝ)|=(2701999651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_9 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659412461/1250000000 : ℝ)*x 0 + (-1007682823/5000000000 : ℝ)*x 1 + (1350999737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659412461/1250000000 : ℝ)^4301 ≤ (43197107223701/100000000000000 : ℝ)^3277 := by
    have hnat : (659412461 : ℕ)^4301*100000000000000^3277 ≤ 43197107223701^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659412461 1250000000 43197107223701 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007682823/5000000000 : ℝ)^4301 ≤ (3054342294829/25000000000000 : ℝ)^3277 := by
    have hnat : (1007682823 : ℕ)^4301*25000000000000^3277 ≤ 3054342294829^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007682823 5000000000 3054342294829 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350999737/2500000000 : ℝ)^4301 ≤ (1393297611679/3125000000000 : ℝ)^3277 := by
    have hnat : (1350999737 : ℕ)^4301*3125000000000^3277 ≤ 1393297611679^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350999737 2500000000 1393297611679 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659412461/1250000000 : ℝ), (-1007682823/5000000000 : ℝ), (1350999737/2500000000 : ℝ)] ![(43197107223701/100000000000000 : ℝ), (3054342294829/25000000000000 : ℝ), (1393297611679/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659412461/1250000000 : ℝ)|^4301 ≤ (43197107223701/100000000000000 : ℝ)^3277
        have hw : |(659412461/1250000000 : ℝ)|=(659412461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007682823/5000000000 : ℝ)|^4301 ≤ (3054342294829/25000000000000 : ℝ)^3277
        have hw : |(-1007682823/5000000000 : ℝ)|=(1007682823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350999737/2500000000 : ℝ)|^4301 ≤ (1393297611679/3125000000000 : ℝ)^3277
        have hw : |(1350999737/2500000000 : ℝ)|=(1350999737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_10 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055059967/2000000000 : ℝ)*x 0 + (1350999653/2500000000 : ℝ)*x 1 + (-1007682953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055059967/2000000000 : ℝ)^4301 ≤ (21598554401779/50000000000000 : ℝ)^3277 := by
    have hnat : (1055059967 : ℕ)^4301*50000000000000^3277 ≤ 21598554401779^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055059967 2000000000 21598554401779 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350999653/2500000000 : ℝ)^4301 ≤ (1783420797413/4000000000000 : ℝ)^3277 := by
    have hnat : (1350999653 : ℕ)^4301*4000000000000^3277 ≤ 1783420797413^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350999653 2500000000 1783420797413 4000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007682953/5000000000 : ℝ)^4301 ≤ (12217371247981/100000000000000 : ℝ)^3277 := by
    have hnat : (1007682953 : ℕ)^4301*100000000000000^3277 ≤ 12217371247981^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007682953 5000000000 12217371247981 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055059967/2000000000 : ℝ), (1350999653/2500000000 : ℝ), (-1007682953/5000000000 : ℝ)] ![(21598554401779/50000000000000 : ℝ), (1783420797413/4000000000000 : ℝ), (12217371247981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055059967/2000000000 : ℝ)|^4301 ≤ (21598554401779/50000000000000 : ℝ)^3277
        have hw : |(1055059967/2000000000 : ℝ)|=(1055059967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350999653/2500000000 : ℝ)|^4301 ≤ (1783420797413/4000000000000 : ℝ)^3277
        have hw : |(1350999653/2500000000 : ℝ)|=(1350999653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007682953/5000000000 : ℝ)|^4301 ≤ (12217371247981/100000000000000 : ℝ)^3277
        have hw : |(-1007682953/5000000000 : ℝ)|=(1007682953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_11 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (563482517/1250000000 : ℝ)*x 0 + (16562499/39062500 : ℝ)*x 1 + (2119999539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563482517/1250000000 : ℝ)^4301 ≤ (8785830115103/25000000000000 : ℝ)^3277 := by
    have hnat : (563482517 : ℕ)^4301*25000000000000^3277 ≤ 8785830115103^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563482517 1250000000 8785830115103 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16562499/39062500 : ℝ)^4301 ≤ (32428343103517/100000000000000 : ℝ)^3277 := by
    have hnat : (16562499 : ℕ)^4301*100000000000000^3277 ≤ 32428343103517^3277*39062500^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16562499 39062500 32428343103517 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119999539/5000000000 : ℝ)^4301 ≤ (4053542052267/12500000000000 : ℝ)^3277 := by
    have hnat : (2119999539 : ℕ)^4301*12500000000000^3277 ≤ 4053542052267^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119999539 5000000000 4053542052267 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(563482517/1250000000 : ℝ), (16562499/39062500 : ℝ), (2119999539/5000000000 : ℝ)] ![(8785830115103/25000000000000 : ℝ), (32428343103517/100000000000000 : ℝ), (4053542052267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(563482517/1250000000 : ℝ)|^4301 ≤ (8785830115103/25000000000000 : ℝ)^3277
        have hw : |(563482517/1250000000 : ℝ)|=(563482517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16562499/39062500 : ℝ)|^4301 ≤ (32428343103517/100000000000000 : ℝ)^3277
        have hw : |(16562499/39062500 : ℝ)|=(16562499/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119999539/5000000000 : ℝ)|^4301 ≤ (4053542052267/12500000000000 : ℝ)^3277
        have hw : |(2119999539/5000000000 : ℝ)|=(2119999539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_12 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1948702631/10000000000 : ℝ)*x 0 + (218954831/400000000 : ℝ)*x 1 + (5253838743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1948702631/10000000000 : ℝ)^4301 ≤ (11689733459179/100000000000000 : ℝ)^3277 := by
    have hnat : (1948702631 : ℕ)^4301*100000000000000^3277 ≤ 11689733459179^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948702631 10000000000 11689733459179 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218954831/400000000 : ℝ)^4301 ≤ (11335915096003/25000000000000 : ℝ)^3277 := by
    have hnat : (218954831 : ℕ)^4301*25000000000000^3277 ≤ 11335915096003^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218954831 400000000 11335915096003 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253838743/10000000000 : ℝ)^4301 ≤ (21483303067803/50000000000000 : ℝ)^3277 := by
    have hnat : (5253838743 : ℕ)^4301*50000000000000^3277 ≤ 21483303067803^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253838743 10000000000 21483303067803 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1948702631/10000000000 : ℝ), (218954831/400000000 : ℝ), (5253838743/10000000000 : ℝ)] ![(11689733459179/100000000000000 : ℝ), (11335915096003/25000000000000 : ℝ), (21483303067803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1948702631/10000000000 : ℝ)|^4301 ≤ (11689733459179/100000000000000 : ℝ)^3277
        have hw : |(-1948702631/10000000000 : ℝ)|=(1948702631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218954831/400000000 : ℝ)|^4301 ≤ (11335915096003/25000000000000 : ℝ)^3277
        have hw : |(218954831/400000000 : ℝ)|=(218954831/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253838743/10000000000 : ℝ)|^4301 ≤ (21483303067803/50000000000000 : ℝ)^3277
        have hw : |(5253838743/10000000000 : ℝ)|=(5253838743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_13 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380776677/10000000000 : ℝ)*x 0 + (-2075640371/10000000000 : ℝ)*x 1 + (5253838793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380776677/10000000000 : ℝ)^4301 ≤ (22167114146403/50000000000000 : ℝ)^3277 := by
    have hnat : (5380776677 : ℕ)^4301*50000000000000^3277 ≤ 22167114146403^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380776677 10000000000 22167114146403 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075640371/10000000000 : ℝ)^4301 ≤ (12699165019457/100000000000000 : ℝ)^3277 := by
    have hnat : (2075640371 : ℕ)^4301*100000000000000^3277 ≤ 12699165019457^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075640371 10000000000 12699165019457 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253838793/10000000000 : ℝ)^4301 ≤ (1342706458509/3125000000000 : ℝ)^3277 := by
    have hnat : (5253838793 : ℕ)^4301*3125000000000^3277 ≤ 1342706458509^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253838793 10000000000 1342706458509 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380776677/10000000000 : ℝ), (-2075640371/10000000000 : ℝ), (5253838793/10000000000 : ℝ)] ![(22167114146403/50000000000000 : ℝ), (12699165019457/100000000000000 : ℝ), (1342706458509/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380776677/10000000000 : ℝ)|^4301 ≤ (22167114146403/50000000000000 : ℝ)^3277
        have hw : |(5380776677/10000000000 : ℝ)|=(5380776677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075640371/10000000000 : ℝ)|^4301 ≤ (12699165019457/100000000000000 : ℝ)^3277
        have hw : |(-2075640371/10000000000 : ℝ)|=(2075640371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253838793/10000000000 : ℝ)|^4301 ≤ (1342706458509/3125000000000 : ℝ)^3277
        have hw : |(5253838793/10000000000 : ℝ)|=(5253838793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_14 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380776553/10000000000 : ℝ)*x 0 + (2626919401/5000000000 : ℝ)*x 1 + (-1037820263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380776553/10000000000 : ℝ)^4301 ≤ (11083556737967/25000000000000 : ℝ)^3277 := by
    have hnat : (5380776553 : ℕ)^4301*25000000000000^3277 ≤ 11083556737967^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380776553 10000000000 11083556737967 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626919401/5000000000 : ℝ)^4301 ≤ (42966606768891/100000000000000 : ℝ)^3277 := by
    have hnat : (2626919401 : ℕ)^4301*100000000000000^3277 ≤ 42966606768891^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626919401 5000000000 42966606768891 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037820263/5000000000 : ℝ)^4301 ≤ (12699166264109/100000000000000 : ℝ)^3277 := by
    have hnat : (1037820263 : ℕ)^4301*100000000000000^3277 ≤ 12699166264109^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037820263 5000000000 12699166264109 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380776553/10000000000 : ℝ), (2626919401/5000000000 : ℝ), (-1037820263/5000000000 : ℝ)] ![(11083556737967/25000000000000 : ℝ), (42966606768891/100000000000000 : ℝ), (12699166264109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380776553/10000000000 : ℝ)|^4301 ≤ (11083556737967/25000000000000 : ℝ)^3277
        have hw : |(5380776553/10000000000 : ℝ)|=(5380776553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626919401/5000000000 : ℝ)|^4301 ≤ (42966606768891/100000000000000 : ℝ)^3277
        have hw : |(2626919401/5000000000 : ℝ)|=(2626919401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037820263/5000000000 : ℝ)|^4301 ≤ (12699166264109/100000000000000 : ℝ)^3277
        have hw : |(-1037820263/5000000000 : ℝ)|=(1037820263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_box_15 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150992647/10000000000 : ℝ)*x 0 + (2209213899/5000000000 : ℝ)*x 1 + (1104606927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150992647/10000000000 : ℝ)^4301 ≤ (31537824752321/100000000000000 : ℝ)^3277 := by
    have hnat : (4150992647 : ℕ)^4301*100000000000000^3277 ≤ 31537824752321^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150992647 10000000000 31537824752321 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209213899/5000000000 : ℝ)^4301 ≤ (684621761471/2000000000000 : ℝ)^3277 := by
    have hnat : (2209213899 : ℕ)^4301*2000000000000^3277 ≤ 684621761471^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209213899 5000000000 684621761471 2000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104606927/2500000000 : ℝ)^4301 ≤ (4278885894801/12500000000000 : ℝ)^3277 := by
    have hnat : (1104606927 : ℕ)^4301*12500000000000^3277 ≤ 4278885894801^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104606927 2500000000 4278885894801 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150992647/10000000000 : ℝ), (2209213899/5000000000 : ℝ), (1104606927/2500000000 : ℝ)] ![(31537824752321/100000000000000 : ℝ), (684621761471/2000000000000 : ℝ), (4278885894801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150992647/10000000000 : ℝ)|^4301 ≤ (31537824752321/100000000000000 : ℝ)^3277
        have hw : |(4150992647/10000000000 : ℝ)|=(4150992647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209213899/5000000000 : ℝ)|^4301 ≤ (684621761471/2000000000000 : ℝ)^3277
        have hw : |(2209213899/5000000000 : ℝ)|=(2209213899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104606927/2500000000 : ℝ)|^4301 ≤ (4278885894801/12500000000000 : ℝ)^3277
        have hw : |(1104606927/2500000000 : ℝ)|=(1104606927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12571/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58939/100000 : ℝ) ∧ (79949/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21087/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2787/25000 : ℝ) ^ (1075/256 : ℝ) ≤ (2494087112183817/25000000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^1075 ≤ (2494087112183817/25000000000000000000 : ℝ)^256 := by
      have hnat : (2787 : ℕ)^1075*25000000000000000000^256 ≤ 2494087112183817^256*25000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 2494087112183817 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (2494087112183817/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (1075/256 : ℝ) ≤ (31915638632063707/100000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^1075 ≤ (31915638632063707/100000000000000000000 : ℝ)^256 := by
      have hnat : (2941 : ℕ)^1075*100000000000000000000^256 ≤ 31915638632063707^256*20000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 31915638632063707 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (31915638632063707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502494087112183817/12500000000000000000 : ℝ) ≤ (10000475116485737/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12502494087112183817/12500000000000000000 : ℝ)^256 ≤ (10000475116485737/10000000000000000 : ℝ)^1075 := by
      have hnat : (12502494087112183817 : ℕ)^256*10000000000000000^1075 ≤ 10000475116485737^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502494087112183817 12500000000000000000 10000475116485737 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475116485737/10000000000000000 : ℝ)) (X := (12502494087112183817/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001675679483231959/4000000000000000000 : ℝ) ≤ (10000997454672573/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (4001675679483231959/4000000000000000000 : ℝ)^256 ≤ (10000997454672573/10000000000000000 : ℝ)^1075 := by
      have hnat : (4001675679483231959 : ℕ)^256*10000000000000000^1075 ≤ 10000997454672573^1075*4000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001675679483231959 4000000000000000000 10000997454672573 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000997454672573/10000000000000000 : ℝ)) (X := (4001675679483231959/4000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031915638632063707/50000000000000000000 : ℝ) ≤ (10001519792859409/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50031915638632063707/50000000000000000000 : ℝ)^256 ≤ (10001519792859409/10000000000000000 : ℝ)^1075 := by
      have hnat : (50031915638632063707 : ℕ)^256*10000000000000000^1075 ≤ 10001519792859409^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031915638632063707 50000000000000000000 10001519792859409 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001519792859409/10000000000000000 : ℝ)) (X := (50031915638632063707/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2494087112183817/25000000000000000000 : ℝ) ≤ ((35560043937126071053/35570000000000000000 : ℝ)+2*(130584546709/88925000000000 : ℝ)*(2787/25000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (35560043937126071053/35570000000000000000 : ℝ)+2*(130584546709/88925000000000 : ℝ)*(2787/25000 : ℝ)=(10000475116485737/10000000000000000 : ℝ) by norm_num, show 1+2*(2494087112183817/25000000000000000000 : ℝ)=(12502494087112183817/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31915638632063707/100000000000000000000 : ℝ)+(2494087112183817/25000000000000000000 : ℝ) ≤ ((35560043937126071053/35570000000000000000 : ℝ)+(130584546709/88925000000000 : ℝ)*((2941/20000 : ℝ)+(2787/25000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (35560043937126071053/35570000000000000000 : ℝ)+(130584546709/88925000000000 : ℝ)*((2941/20000 : ℝ)+(2787/25000 : ℝ))=(10000997454672573/10000000000000000 : ℝ) by norm_num, show 1+(31915638632063707/100000000000000000000 : ℝ)+(2494087112183817/25000000000000000000 : ℝ)=(4001675679483231959/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31915638632063707/100000000000000000000 : ℝ) ≤ ((35560043937126071053/35570000000000000000 : ℝ)+2*(130584546709/88925000000000 : ℝ)*(2941/20000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (35560043937126071053/35570000000000000000 : ℝ)+2*(130584546709/88925000000000 : ℝ)*(2941/20000 : ℝ)=(10001519792859409/10000000000000000 : ℝ) by norm_num, show 1+2*(31915638632063707/100000000000000000000 : ℝ)=(50031915638632063707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35560043937126071053/35570000000000000000 : ℝ)*(X 1 0+X 2 0)+(130584546709/88925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (35560043937126071053/35570000000000000000 : ℝ)) (alpha := (130584546709/88925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35560043937126071053/35570000000000000000 : ℝ)*(X 0 1+X 2 1)+(130584546709/88925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (35560043937126071053/35570000000000000000 : ℝ)) (alpha := (130584546709/88925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35560043937126071053/35570000000000000000 : ℝ)*(X 0 2+X 1 2)+(130584546709/88925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (35560043937126071053/35570000000000000000 : ℝ)) (alpha := (130584546709/88925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-75100453/400000000 : ℝ)*X 0 0+(5389979229/10000000000 : ℝ)*X 0 1+(1077995873/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642576097/5000000000 : ℝ)*X 1 0+(-1010561391/5000000000 : ℝ)*X 1 1+(2694989919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321288083/2500000000 : ℝ)*X 2 0+(1347494851/2500000000 : ℝ)*X 2 1+(-126320199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2237545011/5000000000 : ℝ)*X 0 0+(4256671793/10000000000 : ℝ)*X 0 1+(4256672013/10000000000 : ℝ)*X 0 2+(2237545011/5000000000 : ℝ)*X 1 0+(4256671793/10000000000 : ℝ)*X 1 1+(4256672013/10000000000 : ℝ)*X 1 2+(2237545011/5000000000 : ℝ)*X 2 0+(4256671793/10000000000 : ℝ)*X 2 1+(4256672013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107458253/5000000000 : ℝ)*X 0 0+(5264907493/10000000000 : ℝ)*X 0 1+(329056661/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1074601089/2000000000 : ℝ)*X 1 0+(-517825857/2500000000 : ℝ)*X 1 1+(5264906283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373004771/10000000000 : ℝ)*X 2 0+(1316226649/2500000000 : ℝ)*X 2 1+(-2071303917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65277389/156250000 : ℝ)*X 0 0+(176211457/400000000 : ℝ)*X 0 1+(2202643627/5000000000 : ℝ)*X 0 2+(65277389/156250000 : ℝ)*X 1 0+(176211457/400000000 : ℝ)*X 1 1+(2202643627/5000000000 : ℝ)*X 1 2+(65277389/156250000 : ℝ)*X 2 0+(176211457/400000000 : ℝ)*X 2 1+(2202643627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-428812901/2000000000 : ℝ)*X 0 0+(323675481/625000000 : ℝ)*X 0 1+(2701999651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659412461/1250000000 : ℝ)*X 1 0+(-1007682823/5000000000 : ℝ)*X 1 1+(1350999737/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055059967/2000000000 : ℝ)*X 2 0+(1350999653/2500000000 : ℝ)*X 2 1+(-1007682953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((563482517/1250000000 : ℝ)*X 0 0+(16562499/39062500 : ℝ)*X 0 1+(2119999539/5000000000 : ℝ)*X 0 2+(563482517/1250000000 : ℝ)*X 1 0+(16562499/39062500 : ℝ)*X 1 1+(2119999539/5000000000 : ℝ)*X 1 2+(563482517/1250000000 : ℝ)*X 2 0+(16562499/39062500 : ℝ)*X 2 1+(2119999539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1948702631/10000000000 : ℝ)*X 0 0+(218954831/400000000 : ℝ)*X 0 1+(5253838743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380776677/10000000000 : ℝ)*X 1 0+(-2075640371/10000000000 : ℝ)*X 1 1+(5253838793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380776553/10000000000 : ℝ)*X 2 0+(2626919401/5000000000 : ℝ)*X 2 1+(-1037820263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4150992647/10000000000 : ℝ)*X 0 0+(2209213899/5000000000 : ℝ)*X 0 1+(1104606927/2500000000 : ℝ)*X 0 2+(4150992647/10000000000 : ℝ)*X 1 0+(2209213899/5000000000 : ℝ)*X 1 1+(1104606927/2500000000 : ℝ)*X 1 2+(4150992647/10000000000 : ℝ)*X 2 0+(2209213899/5000000000 : ℝ)*X 2 1+(1104606927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12571/20000 : ℝ) ≤ (-139728578277959878897435096169919/222312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347133/10000000000000 : ℝ)*(lower3) + (315869797/100000000000000 : ℝ)*(lower4) + (13798133/100000000000000 : ℝ)*(lower5) + (364955373213547/12500000000000 : ℝ)*(major0) + (364955373213547/12500000000000 : ℝ)*(major1) + (364955373213547/12500000000000 : ℝ)*(major2) + (3397477843/20000000000000 : ℝ)*(sp1) + (22462896327/100000000000000 : ℝ)*(sp2) + (3992689899/50000000000000 : ℝ)*(sp3) + (1986402291274181/50000000000000 : ℝ)*(sp4) + (1986397375597779/50000000000000 : ℝ)*(sp5) + (1986394637844223/50000000000000 : ℝ)*(sp6) + (943708511470661/50000000000000 : ℝ)*(sp7) + (1789009103/25000000000000 : ℝ)*(sp8) + (11796406302007/625000000000 : ℝ)*(f.failure) + (1986405869292387/50000000000000 : ℝ)*(f.sum) + (5148666267481/4446250000000000000000000000 : ℝ)*base66 + (3239517818684104991/444625000000000000000000000000000 : ℝ)*base67 + (3907424060520104991/444625000000000000000000000000000 : ℝ)*base69 + (1609767020841354991/444625000000000000000000000000000 : ℝ)*base71 + (6994152620493/8892500000000000000000000000 : ℝ)*base73 + (2698877666590604991/444625000000000000000000000000000 : ℝ)*base75 + (2764520655670104991/444625000000000000000000000000000 : ℝ)*base77 + (4549767355403854991/444625000000000000000000000000000 : ℝ)*base79 + (16997259412479/4446250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (169737/31250000000000000000 : ℝ)*base90 + (169737/31250000000000000000 : ℝ)*base92 + (169737/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58939/100000 : ℝ) ≤ (262070049896969565218262122503257/444625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2974531/100000000000000 : ℝ)*(lower0) + (12193839/100000000000000 : ℝ)*(upper1) + (24096247/20000000000000 : ℝ)*(upper2) + (3597577/100000000000000 : ℝ)*(upper3) + (747074264118859/25000000000000 : ℝ)*(major0) + (747074264118859/25000000000000 : ℝ)*(major1) + (747074264118859/25000000000000 : ℝ)*(major2) + (4025134483758223/100000000000000 : ℝ)*(sp0) + (503139761924659/12500000000000 : ℝ)*(sp1) + (4025138131994863/100000000000000 : ℝ)*(sp2) + (965903472495231/50000000000000 : ℝ)*(sp3) + (21800525121/100000000000000 : ℝ)*(sp5) + (1763927531/100000000000000 : ℝ)*(sp6) + (5412164171/100000000000000 : ℝ)*(sp12) + (965903472495231/50000000000000 : ℝ)*(f.failure) + (2012569947961197/50000000000000 : ℝ)*(f.sum) + (29439207263521/4446250000000000000000000000 : ℝ)*base66 + (5426759702282188527/889250000000000000000000000000000 : ℝ)*base67 + (4828921821714188527/889250000000000000000000000000000 : ℝ)*base69 + (1402923176736438527/889250000000000000000000000000000 : ℝ)*base71 + (88409733998203/8892500000000000000000000000 : ℝ)*base73 + (1061087999922438527/889250000000000000000000000000000 : ℝ)*base75 + (9092248092904438527/889250000000000000000000000000000 : ℝ)*base77 + (20664286512894188527/889250000000000000000000000000000 : ℝ)*base79 + (89289028688799/17785000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3940321/2500000000000000000000 : ℝ)*base90 + (3940321/2500000000000000000000 : ℝ)*base92 + (3940321/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79949/100000 : ℝ) ≤ (71096547646616346781499866838889/88925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60505727/50000000000000 : ℝ)*(upper1) + (34457891/100000000000000 : ℝ)*(upper2) + (78263721/100000000000000 : ℝ)*(lower5) + (165023596741843/5000000000000 : ℝ)*(major0) + (165023596741843/5000000000000 : ℝ)*(major1) + (165023596741843/5000000000000 : ℝ)*(major2) + (54996372029/50000000000000 : ℝ)*(sp1) + (4381908583/50000000000000 : ℝ)*(sp2) + (27856754873/100000000000000 : ℝ)*(sp3) + (6843945681/50000000000000 : ℝ)*(sp4) + (444066507709589/10000000000000 : ℝ)*(sp8) + (2220284386121597/50000000000000 : ℝ)*(sp9) + (4440670001170087/100000000000000 : ℝ)*(sp10) + (426717373856087/20000000000000 : ℝ)*(sp11) + (533403681508827/25000000000000 : ℝ)*(f.failure) + (1110169691246813/25000000000000 : ℝ)*(f.sum) + (1884187137677/444625000000000000000000000 : ℝ)*base66 + (568809159386220679/177850000000000000000000000000000 : ℝ)*base67 + (1650079760788620679/177850000000000000000000000000000 : ℝ)*base69 + (1690144115834470679/177850000000000000000000000000000 : ℝ)*base71 + (12478140961701/3557000000000000000000000000 : ℝ)*base74 + (1334218654500220679/177850000000000000000000000000000 : ℝ)*base75 + (751615431965420679/177850000000000000000000000000000 : ℝ)*base77 + (558169567340520679/177850000000000000000000000000000 : ℝ)*base79 + (3310025621549/3557000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4363643/1250000000000000000000 : ℝ)*base89 + (4363643/1250000000000000000000 : ℝ)*base91 + (4363643/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21087/25000 : ℝ) ≤ (-3000171563014020115977290703/3557000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15271537/25000000000000 : ℝ)*(lower0) + (4763509/50000000000000 : ℝ)*(upper3) + (22710521/25000000000000 : ℝ)*(lower4) + (667386375098209/20000000000000 : ℝ)*(major0) + (667386375098209/20000000000000 : ℝ)*(major1) + (667386375098209/20000000000000 : ℝ)*(major2) + (189047357/12500000000000 : ℝ)*(sp0) + (6679624167/100000000000000 : ℝ)*(sp5) + (10210663111/20000000000000 : ℝ)*(sp6) + (31509799203/100000000000000 : ℝ)*(sp7) + (284049556143993/6250000000000 : ℝ)*(sp12) + (4544787731058577/100000000000000 : ℝ)*(sp13) + (4544743357367189/100000000000000 : ℝ)*(sp14) + (539288254277209/25000000000000 : ℝ)*(sp15) + (2157184526908039/100000000000000 : ℝ)*(f.failure) + (568099301335343/12500000000000 : ℝ)*(f.sum) + (1296751089/347363281250000000000000 : ℝ)*base65 + (1710857743011644077/711400000000000000000000000000000 : ℝ)*base67 + (3738825770375844077/711400000000000000000000000000000 : ℝ)*base69 + (2026384204605844077/711400000000000000000000000000000 : ℝ)*base71 + (104828010511/55578125000000000000000000 : ℝ)*base73 + (7679627695641355923/711400000000000000000000000000000 : ℝ)*base76 + (306463203043355923/711400000000000000000000000000000 : ℝ)*base78 + (784671660515955923/711400000000000000000000000000000 : ℝ)*base80 + (24956864225467/3557000000000000000000000000 : ℝ)*base81 + (5411751/5000000000000000000000 : ℝ)*base89 + (5411751/5000000000000000000000 : ℝ)*base91 + (5411751/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1341_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (79949/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21087/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1341_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1341_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (79949/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21087/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1341_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1341_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (79949/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21087/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

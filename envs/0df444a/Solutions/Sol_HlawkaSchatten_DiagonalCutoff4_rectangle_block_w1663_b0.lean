-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1663_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:57.726234+00:00
-- url     : https://prove2.me/submissions/967dfa1e-431a-4bf0-9122-b66e3a5f708e

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
theorem support_rectangle_w1663_s0_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1470115409/10000000000 : ℝ)*x 0 + (2884711177/5000000000 : ℝ)*x 1 + (308140579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1470115409/10000000000 : ℝ)^4971 ≤ (55874177611/625000000000 : ℝ)^3947 := by
    have hnat : (1470115409 : ℕ)^4971*625000000000^3947 ≤ 55874177611^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470115409 10000000000 55874177611 625000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2884711177/5000000000 : ℝ)^4971 ≤ (50022004526461/100000000000000 : ℝ)^3947 := by
    have hnat : (2884711177 : ℕ)^4971*100000000000000^3947 ≤ 50022004526461^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2884711177 5000000000 50022004526461 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308140579/625000000 : ℝ)^4971 ≤ (20519063521581/50000000000000 : ℝ)^3947 := by
    have hnat : (308140579 : ℕ)^4971*50000000000000^3947 ≤ 20519063521581^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308140579 625000000 20519063521581 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1470115409/10000000000 : ℝ), (2884711177/5000000000 : ℝ), (308140579/625000000 : ℝ)] ![(55874177611/625000000000 : ℝ), (50022004526461/100000000000000 : ℝ), (20519063521581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1470115409/10000000000 : ℝ)|^4971 ≤ (55874177611/625000000000 : ℝ)^3947
        have hw : |(-1470115409/10000000000 : ℝ)|=(1470115409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2884711177/5000000000 : ℝ)|^4971 ≤ (50022004526461/100000000000000 : ℝ)^3947
        have hw : |(2884711177/5000000000 : ℝ)|=(2884711177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(308140579/625000000 : ℝ)|^4971 ≤ (20519063521581/50000000000000 : ℝ)^3947
        have hw : |(308140579/625000000 : ℝ)|=(308140579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5432416909/10000000000 : ℝ)*x 0 + (-482388887/2500000000 : ℝ)*x 1 + (4930250019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5432416909/10000000000 : ℝ)^4971 ≤ (46370347459607/100000000000000 : ℝ)^3947 := by
    have hnat : (5432416909 : ℕ)^4971*100000000000000^3947 ≤ 46370347459607^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432416909 10000000000 46370347459607 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482388887/2500000000 : ℝ)^4971 ≤ (6295758789327/50000000000000 : ℝ)^3947 := by
    have hnat : (482388887 : ℕ)^4971*50000000000000^3947 ≤ 6295758789327^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482388887 2500000000 6295758789327 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4930250019/10000000000 : ℝ)^4971 ≤ (10259533739501/25000000000000 : ℝ)^3947 := by
    have hnat : (4930250019 : ℕ)^4971*25000000000000^3947 ≤ 10259533739501^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4930250019 10000000000 10259533739501 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5432416909/10000000000 : ℝ), (-482388887/2500000000 : ℝ), (4930250019/10000000000 : ℝ)] ![(46370347459607/100000000000000 : ℝ), (6295758789327/50000000000000 : ℝ), (10259533739501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5432416909/10000000000 : ℝ)|^4971 ≤ (46370347459607/100000000000000 : ℝ)^3947
        have hw : |(5432416909/10000000000 : ℝ)|=(5432416909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482388887/2500000000 : ℝ)|^4971 ≤ (6295758789327/50000000000000 : ℝ)^3947
        have hw : |(-482388887/2500000000 : ℝ)|=(482388887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4930250019/10000000000 : ℝ)|^4971 ≤ (10259533739501/25000000000000 : ℝ)^3947
        have hw : |(4930250019/10000000000 : ℝ)|=(4930250019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086483709/2000000000 : ℝ)*x 0 + (2465124469/5000000000 : ℝ)*x 1 + (-964777393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086483709/2000000000 : ℝ)^4971 ≤ (724536953863/1562500000000 : ℝ)^3947 := by
    have hnat : (1086483709 : ℕ)^4971*1562500000000^3947 ≤ 724536953863^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086483709 2000000000 724536953863 1562500000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2465124469/5000000000 : ℝ)^4971 ≤ (10259530906407/25000000000000 : ℝ)^3947 := by
    have hnat : (2465124469 : ℕ)^4971*25000000000000^3947 ≤ 10259530906407^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465124469 5000000000 10259530906407 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964777393/5000000000 : ℝ)^4971 ≤ (12591511316087/100000000000000 : ℝ)^3947 := by
    have hnat : (964777393 : ℕ)^4971*100000000000000^3947 ≤ 12591511316087^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964777393 5000000000 12591511316087 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086483709/2000000000 : ℝ), (2465124469/5000000000 : ℝ), (-964777393/5000000000 : ℝ)] ![(724536953863/1562500000000 : ℝ), (10259530906407/25000000000000 : ℝ), (12591511316087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086483709/2000000000 : ℝ)|^4971 ≤ (724536953863/1562500000000 : ℝ)^3947
        have hw : |(1086483709/2000000000 : ℝ)|=(1086483709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2465124469/5000000000 : ℝ)|^4971 ≤ (10259530906407/25000000000000 : ℝ)^3947
        have hw : |(2465124469/5000000000 : ℝ)|=(2465124469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964777393/5000000000 : ℝ)|^4971 ≤ (12591511316087/100000000000000 : ℝ)^3947
        have hw : |(-964777393/5000000000 : ℝ)|=(964777393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042286121/5000000000 : ℝ)*x 0 + (385749953/1250000000 : ℝ)*x 1 + (2646374543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042286121/5000000000 : ℝ)^4971 ≤ (16189498980683/50000000000000 : ℝ)^3947 := by
    have hnat : (2042286121 : ℕ)^4971*50000000000000^3947 ≤ 16189498980683^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042286121 5000000000 16189498980683 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385749953/1250000000 : ℝ)^4971 ≤ (4549419459703/20000000000000 : ℝ)^3947 := by
    have hnat : (385749953 : ℕ)^4971*20000000000000^3947 ≤ 4549419459703^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385749953 1250000000 4549419459703 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2646374543/5000000000 : ℝ)^4971 ≤ (701154761257/1562500000000 : ℝ)^3947 := by
    have hnat : (2646374543 : ℕ)^4971*1562500000000^3947 ≤ 701154761257^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646374543 5000000000 701154761257 1562500000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042286121/5000000000 : ℝ), (385749953/1250000000 : ℝ), (2646374543/5000000000 : ℝ)] ![(16189498980683/50000000000000 : ℝ), (4549419459703/20000000000000 : ℝ), (701154761257/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042286121/5000000000 : ℝ)|^4971 ≤ (16189498980683/50000000000000 : ℝ)^3947
        have hw : |(2042286121/5000000000 : ℝ)|=(2042286121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(385749953/1250000000 : ℝ)|^4971 ≤ (4549419459703/20000000000000 : ℝ)^3947
        have hw : |(385749953/1250000000 : ℝ)|=(385749953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2646374543/5000000000 : ℝ)|^4971 ≤ (701154761257/1562500000000 : ℝ)^3947
        have hw : |(2646374543/5000000000 : ℝ)|=(2646374543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1472269617/10000000000 : ℝ)*x 0 + (309432417/625000000 : ℝ)*x 1 + (5748046609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472269617/10000000000 : ℝ)^4971 ≤ (2239092508487/25000000000000 : ℝ)^3947 := by
    have hnat : (1472269617 : ℕ)^4971*25000000000000^3947 ≤ 2239092508487^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472269617 10000000000 2239092508487 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309432417/625000000 : ℝ)^4971 ≤ (41254927005849/100000000000000 : ℝ)^3947 := by
    have hnat : (309432417 : ℕ)^4971*100000000000000^3947 ≤ 41254927005849^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309432417 625000000 41254927005849 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5748046609/10000000000 : ℝ)^4971 ≤ (49788702942313/100000000000000 : ℝ)^3947 := by
    have hnat : (5748046609 : ℕ)^4971*100000000000000^3947 ≤ 49788702942313^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5748046609 10000000000 49788702942313 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1472269617/10000000000 : ℝ), (309432417/625000000 : ℝ), (5748046609/10000000000 : ℝ)] ![(2239092508487/25000000000000 : ℝ), (41254927005849/100000000000000 : ℝ), (49788702942313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1472269617/10000000000 : ℝ)|^4971 ≤ (2239092508487/25000000000000 : ℝ)^3947
        have hw : |(-1472269617/10000000000 : ℝ)|=(1472269617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309432417/625000000 : ℝ)|^4971 ≤ (41254927005849/100000000000000 : ℝ)^3947
        have hw : |(309432417/625000000 : ℝ)|=(309432417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5748046609/10000000000 : ℝ)|^4971 ≤ (49788702942313/100000000000000 : ℝ)^3947
        have hw : |(5748046609/10000000000 : ℝ)|=(5748046609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601765657/5000000000 : ℝ)*x 0 + (-222351783/2000000000 : ℝ)*x 1 + (5748046937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601765657/5000000000 : ℝ)^4971 ≤ (1372604087119/3125000000000 : ℝ)^3947 := by
    have hnat : (2601765657 : ℕ)^4971*3125000000000^3947 ≤ 1372604087119^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601765657 5000000000 1372604087119 3125000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222351783/2000000000 : ℝ)^4971 ≤ (392997667781/6250000000000 : ℝ)^3947 := by
    have hnat : (222351783 : ℕ)^4971*6250000000000^3947 ≤ 392997667781^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222351783 2000000000 392997667781 6250000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5748046937/10000000000 : ℝ)^4971 ≤ (49788706520483/100000000000000 : ℝ)^3947 := by
    have hnat : (5748046937 : ℕ)^4971*100000000000000^3947 ≤ 49788706520483^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5748046937 10000000000 49788706520483 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601765657/5000000000 : ℝ), (-222351783/2000000000 : ℝ), (5748046937/10000000000 : ℝ)] ![(1372604087119/3125000000000 : ℝ), (392997667781/6250000000000 : ℝ), (49788706520483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601765657/5000000000 : ℝ)|^4971 ≤ (1372604087119/3125000000000 : ℝ)^3947
        have hw : |(2601765657/5000000000 : ℝ)|=(2601765657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222351783/2000000000 : ℝ)|^4971 ≤ (392997667781/6250000000000 : ℝ)^3947
        have hw : |(-222351783/2000000000 : ℝ)|=(222351783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5748046937/10000000000 : ℝ)|^4971 ≤ (49788706520483/100000000000000 : ℝ)^3947
        have hw : |(5748046937/10000000000 : ℝ)|=(5748046937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601765683/5000000000 : ℝ)*x 0 + (574804693/1000000000 : ℝ)*x 1 + (-555879423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601765683/5000000000 : ℝ)^4971 ≤ (2196166567031/5000000000000 : ℝ)^3947 := by
    have hnat : (2601765683 : ℕ)^4971*5000000000000^3947 ≤ 2196166567031^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601765683 5000000000 2196166567031 5000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574804693/1000000000 : ℝ)^4971 ≤ (1244717661103/2500000000000 : ℝ)^3947 := by
    have hnat : (574804693 : ℕ)^4971*2500000000000^3947 ≤ 1244717661103^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574804693 1000000000 1244717661103 2500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555879423/5000000000 : ℝ)^4971 ≤ (3143981096497/50000000000000 : ℝ)^3947 := by
    have hnat : (555879423 : ℕ)^4971*50000000000000^3947 ≤ 3143981096497^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555879423 5000000000 3143981096497 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601765683/5000000000 : ℝ), (574804693/1000000000 : ℝ), (-555879423/5000000000 : ℝ)] ![(2196166567031/5000000000000 : ℝ), (1244717661103/2500000000000 : ℝ), (3143981096497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601765683/5000000000 : ℝ)|^4971 ≤ (2196166567031/5000000000000 : ℝ)^3947
        have hw : |(2601765683/5000000000 : ℝ)|=(2601765683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574804693/1000000000 : ℝ)|^4971 ≤ (1244717661103/2500000000000 : ℝ)^3947
        have hw : |(574804693/1000000000 : ℝ)|=(574804693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555879423/5000000000 : ℝ)|^4971 ≤ (3143981096497/50000000000000 : ℝ)^3947
        have hw : |(-555879423/5000000000 : ℝ)|=(555879423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s0_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4090235239/10000000000 : ℝ)*x 0 + (5238395861/10000000000 : ℝ)*x 1 + (125688439/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4090235239/10000000000 : ℝ)^4971 ≤ (32435546041377/100000000000000 : ℝ)^3947 := by
    have hnat : (4090235239 : ℕ)^4971*100000000000000^3947 ≤ 32435546041377^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090235239 10000000000 32435546041377 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238395861/10000000000 : ℝ)^4971 ≤ (44294297066087/100000000000000 : ℝ)^3947 := by
    have hnat : (5238395861 : ℕ)^4971*100000000000000^3947 ≤ 44294297066087^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238395861 10000000000 44294297066087 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125688439/400000000 : ℝ)^4971 ≤ (4654031375427/20000000000000 : ℝ)^3947 := by
    have hnat : (125688439 : ℕ)^4971*20000000000000^3947 ≤ 4654031375427^3947*400000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125688439 400000000 4654031375427 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4090235239/10000000000 : ℝ), (5238395861/10000000000 : ℝ), (125688439/400000000 : ℝ)] ![(32435546041377/100000000000000 : ℝ), (44294297066087/100000000000000 : ℝ), (4654031375427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4090235239/10000000000 : ℝ)|^4971 ≤ (32435546041377/100000000000000 : ℝ)^3947
        have hw : |(4090235239/10000000000 : ℝ)|=(4090235239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238395861/10000000000 : ℝ)|^4971 ≤ (44294297066087/100000000000000 : ℝ)^3947
        have hw : |(5238395861/10000000000 : ℝ)|=(5238395861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125688439/400000000 : ℝ)|^4971 ≤ (4654031375427/20000000000000 : ℝ)^3947
        have hw : |(125688439/400000000 : ℝ)|=(125688439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5091/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5771/25000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4967/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4967 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4967*1^1024 ≤ 0^1024*1^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4967/1024 : ℝ) ≤ (587121243218003413/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4967 ≤ (587121243218003413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4967*50000000000000000000^1024 ≤ 587121243218003413^1024*5^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 587121243218003413 50000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (587121243218003413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4967 := by
      have hnat : (1 : ℕ)^1024*1^4967 ≤ 1^4967*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50587121243218003413/50000000000000000000 : ℝ) ≤ (5012048108286261/5000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50587121243218003413/50000000000000000000 : ℝ)^1024 ≤ (5012048108286261/5000000000000000 : ℝ)^4967 := by
      have hnat : (50587121243218003413 : ℕ)^1024*5000000000000000^4967 ≤ 5012048108286261^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50587121243218003413 50000000000000000000 5012048108286261 5000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012048108286261/5000000000000000 : ℝ)) (X := (50587121243218003413/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25587121243218003413/25000000000000000000 : ℝ) ≤ (2512048108286261/2500000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (25587121243218003413/25000000000000000000 : ℝ)^1024 ≤ (2512048108286261/2500000000000000 : ℝ)^4967 := by
      have hnat : (25587121243218003413 : ℕ)^1024*2500000000000000^4967 ≤ 2512048108286261^4967*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25587121243218003413 25000000000000000000 2512048108286261 2500000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512048108286261/2500000000000000 : ℝ)) (X := (25587121243218003413/25000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12048108286261/2000000000000000 : ℝ)*(0 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12048108286261/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(587121243218003413/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12048108286261/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12048108286261/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5012048108286261/5000000000000000 : ℝ) by norm_num, show 1+(587121243218003413/50000000000000000000 : ℝ)+(0 : ℝ)=(50587121243218003413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(587121243218003413/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12048108286261/2000000000000000 : ℝ)*(2/5 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12048108286261/2000000000000000 : ℝ)*(2/5 : ℝ)=(2512048108286261/2500000000000000 : ℝ) by norm_num, show 1+2*(587121243218003413/50000000000000000000 : ℝ)=(25587121243218003413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12048108286261/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12048108286261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12048108286261/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12048108286261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12048108286261/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12048108286261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1470115409/10000000000 : ℝ)*X 0 0+(2884711177/5000000000 : ℝ)*X 0 1+(308140579/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5432416909/10000000000 : ℝ)*X 1 0+(-482388887/2500000000 : ℝ)*X 1 1+(4930250019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1086483709/2000000000 : ℝ)*X 2 0+(2465124469/5000000000 : ℝ)*X 2 1+(-964777393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2042286121/5000000000 : ℝ)*X 0 0+(385749953/1250000000 : ℝ)*X 0 1+(2646374543/5000000000 : ℝ)*X 0 2+(2042286121/5000000000 : ℝ)*X 1 0+(385749953/1250000000 : ℝ)*X 1 1+(2646374543/5000000000 : ℝ)*X 1 2+(2042286121/5000000000 : ℝ)*X 2 0+(385749953/1250000000 : ℝ)*X 2 1+(2646374543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1472269617/10000000000 : ℝ)*X 0 0+(309432417/625000000 : ℝ)*X 0 1+(5748046609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2601765657/5000000000 : ℝ)*X 1 0+(-222351783/2000000000 : ℝ)*X 1 1+(5748046937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2601765683/5000000000 : ℝ)*X 2 0+(574804693/1000000000 : ℝ)*X 2 1+(-555879423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4090235239/10000000000 : ℝ)*X 0 0+(5238395861/10000000000 : ℝ)*X 0 1+(125688439/400000000 : ℝ)*X 0 2+(4090235239/10000000000 : ℝ)*X 1 0+(5238395861/10000000000 : ℝ)*X 1 1+(125688439/400000000 : ℝ)*X 1 2+(4090235239/10000000000 : ℝ)*X 2 0+(5238395861/10000000000 : ℝ)*X 2 1+(125688439/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135918313070498966974893/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69320923/50000000000000 : ℝ)*(base1) + (931476633/100000000000000 : ℝ)*(base19) + (624893799/50000000000000 : ℝ)*(base23) + (5070331/12500000000000 : ℝ)*(base24) + (220079079/100000000000000 : ℝ)*(upper5) + (822408835856171/100000000000000 : ℝ)*(major0) + (822408835856171/100000000000000 : ℝ)*(major1) + (822408835856171/100000000000000 : ℝ)*(major2) + (595826266604467/50000000000000 : ℝ)*(sp0) + (148957187736657/12500000000000 : ℝ)*(sp1) + (595828571509821/50000000000000 : ℝ)*(sp2) + (56644655834691/12500000000000 : ℝ)*(sp3) + (6038802801/100000000000000 : ℝ)*(sp4) + (1671798657/100000000000000 : ℝ)*(sp7) + (453159057118031/100000000000000 : ℝ)*(f.failure) + (1191658433369889/100000000000000 : ℝ)*(f.sum) + (194723566233369/100000000000000000000000000000 : ℝ)*base66 + (419628320033369/200000000000000000000000000000 : ℝ)*base68 + (1002339782233369/200000000000000000000000000000 : ℝ)*base70 + (1078708009233369/200000000000000000000000000000 : ℝ)*base72 + (67153105266631/100000000000000000000000000000 : ℝ)*base73 + (1564438878033369/200000000000000000000000000000 : ℝ)*base76 + (497227046433369/200000000000000000000000000000 : ℝ)*base78 + (202574177633369/200000000000000000000000000000 : ℝ)*base80 + (419693845733369/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25431971/5000000000000000000000 : ℝ)*base89 + (25431971/5000000000000000000000 : ℝ)*base91 + (25431971/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357999987852665086849413/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196833361/20000000000000 : ℝ)*(base19) + (253935441/25000000000000 : ℝ)*(base23) + (774841/100000000000000 : ℝ)*(base39) + (195514329/100000000000000 : ℝ)*(upper3) + (61384601/50000000000000 : ℝ)*(upper5) + (865780377951611/100000000000000 : ℝ)*(major0) + (865780377951611/100000000000000 : ℝ)*(major1) + (86578037717677/10000000000000 : ℝ)*(major2) + (645873011/20000000000000 : ℝ)*(sp1) + (3644752353/100000000000000 : ℝ)*(sp2) + (1254503117953347/100000000000000 : ℝ)*(sp4) + (1254498904421487/100000000000000 : ℝ)*(sp5) + (1254498458234071/100000000000000 : ℝ)*(sp6) + (477057398508373/100000000000000 : ℝ)*(sp7) + (477057398508373/100000000000000 : ℝ)*(f.failure) + (313625779682047/25000000000000 : ℝ)*(f.sum) + (52442656126559/200000000000000000000000000000 : ℝ)*base66 + (25975429195697/20000000000000000000000000000 : ℝ)*base67 + (282165994516471/200000000000000000000000000000 : ℝ)*base69 + (119456085264303/20000000000000000000000000000 : ℝ)*base72 + (758544471873441/200000000000000000000000000000 : ℝ)*base73 + (644928213683529/200000000000000000000000000000 : ℝ)*base76 + (428947909483529/200000000000000000000000000000 : ℝ)*base78 + (91374665283529/200000000000000000000000000000 : ℝ)*base80 + (193249220983529/100000000000000000000000000000 : ℝ)*base82 + (19097393/5000000000000000000000 : ℝ)*base89 + (19097393/5000000000000000000000 : ℝ)*base91 + (19097393/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1663_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5091/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5771/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1663_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1663_s1_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2513173/16000000 : ℝ)*x 0 + (1371712923/2500000000 : ℝ)*x 1 + (128682787/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2513173/16000000 : ℝ)^4971 ≤ (9717200895231/100000000000000 : ℝ)^3947 := by
    have hnat : (2513173 : ℕ)^4971*100000000000000^3947 ≤ 9717200895231^3947*16000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513173 16000000 9717200895231 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371712923/2500000000 : ℝ)^4971 ≤ (11739075236979/25000000000000 : ℝ)^3947 := by
    have hnat : (1371712923 : ℕ)^4971*25000000000000^3947 ≤ 11739075236979^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371712923 2500000000 11739075236979 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128682787/250000000 : ℝ)^4971 ≤ (8665299630201/20000000000000 : ℝ)^3947 := by
    have hnat : (128682787 : ℕ)^4971*20000000000000^3947 ≤ 8665299630201^3947*250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128682787 250000000 8665299630201 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2513173/16000000 : ℝ), (1371712923/2500000000 : ℝ), (128682787/250000000 : ℝ)] ![(9717200895231/100000000000000 : ℝ), (11739075236979/25000000000000 : ℝ), (8665299630201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2513173/16000000 : ℝ)|^4971 ≤ (9717200895231/100000000000000 : ℝ)^3947
        have hw : |(-2513173/16000000 : ℝ)|=(2513173/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371712923/2500000000 : ℝ)|^4971 ≤ (11739075236979/25000000000000 : ℝ)^3947
        have hw : |(1371712923/2500000000 : ℝ)|=(1371712923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128682787/250000000 : ℝ)|^4971 ≤ (8665299630201/20000000000000 : ℝ)^3947
        have hw : |(128682787/250000000 : ℝ)|=(128682787/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357250347/10000000000 : ℝ)*x 0 + (-349393463/2000000000 : ℝ)*x 1 + (2573655739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357250347/10000000000 : ℝ)^4971 ≤ (5695466697043/12500000000000 : ℝ)^3947 := by
    have hnat : (5357250347 : ℕ)^4971*12500000000000^3947 ≤ 5695466697043^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357250347 10000000000 5695466697043 12500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349393463/2000000000 : ℝ)^4971 ≤ (2221953657503/20000000000000 : ℝ)^3947 := by
    have hnat : (349393463 : ℕ)^4971*20000000000000^3947 ≤ 2221953657503^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349393463 2000000000 2221953657503 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573655739/5000000000 : ℝ)^4971 ≤ (43326498129803/100000000000000 : ℝ)^3947 := by
    have hnat : (2573655739 : ℕ)^4971*100000000000000^3947 ≤ 43326498129803^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573655739 5000000000 43326498129803 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357250347/10000000000 : ℝ), (-349393463/2000000000 : ℝ), (2573655739/5000000000 : ℝ)] ![(5695466697043/12500000000000 : ℝ), (2221953657503/20000000000000 : ℝ), (43326498129803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357250347/10000000000 : ℝ)|^4971 ≤ (5695466697043/12500000000000 : ℝ)^3947
        have hw : |(5357250347/10000000000 : ℝ)|=(5357250347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349393463/2000000000 : ℝ)|^4971 ≤ (2221953657503/20000000000000 : ℝ)^3947
        have hw : |(-349393463/2000000000 : ℝ)|=(349393463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573655739/5000000000 : ℝ)|^4971 ≤ (43326498129803/100000000000000 : ℝ)^3947
        have hw : |(2573655739/5000000000 : ℝ)|=(2573655739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334828153/625000000 : ℝ)*x 0 + (5147311471/10000000000 : ℝ)*x 1 + (-436741797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334828153/625000000 : ℝ)^4971 ≤ (22781867329107/50000000000000 : ℝ)^3947 := by
    have hnat : (334828153 : ℕ)^4971*50000000000000^3947 ≤ 22781867329107^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334828153 625000000 22781867329107 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5147311471/10000000000 : ℝ)^4971 ≤ (8665299611119/20000000000000 : ℝ)^3947 := by
    have hnat : (5147311471 : ℕ)^4971*20000000000000^3947 ≤ 8665299611119^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147311471 10000000000 8665299611119 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436741797/2500000000 : ℝ)^4971 ≤ (11109767270329/100000000000000 : ℝ)^3947 := by
    have hnat : (436741797 : ℕ)^4971*100000000000000^3947 ≤ 11109767270329^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436741797 2500000000 11109767270329 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334828153/625000000 : ℝ), (5147311471/10000000000 : ℝ), (-436741797/2500000000 : ℝ)] ![(22781867329107/50000000000000 : ℝ), (8665299611119/20000000000000 : ℝ), (11109767270329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334828153/625000000 : ℝ)|^4971 ≤ (22781867329107/50000000000000 : ℝ)^3947
        have hw : |(334828153/625000000 : ℝ)|=(334828153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5147311471/10000000000 : ℝ)|^4971 ≤ (8665299611119/20000000000000 : ℝ)^3947
        have hw : |(5147311471/10000000000 : ℝ)|=(5147311471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436741797/2500000000 : ℝ)|^4971 ≤ (11109767270329/100000000000000 : ℝ)^3947
        have hw : |(-436741797/2500000000 : ℝ)|=(436741797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166576541/400000000 : ℝ)*x 0 + (3734970367/10000000000 : ℝ)*x 1 + (4627849081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166576541/400000000 : ℝ)^4971 ≤ (3317812444199/10000000000000 : ℝ)^3947 := by
    have hnat : (166576541 : ℕ)^4971*10000000000000^3947 ≤ 3317812444199^3947*400000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166576541 400000000 3317812444199 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3734970367/10000000000 : ℝ)^4971 ≤ (14464132605887/50000000000000 : ℝ)^3947 := by
    have hnat : (3734970367 : ℕ)^4971*50000000000000^3947 ≤ 14464132605887^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734970367 10000000000 14464132605887 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4627849081/10000000000 : ℝ)^4971 ≤ (18946805164567/50000000000000 : ℝ)^3947 := by
    have hnat : (4627849081 : ℕ)^4971*50000000000000^3947 ≤ 18946805164567^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4627849081 10000000000 18946805164567 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166576541/400000000 : ℝ), (3734970367/10000000000 : ℝ), (4627849081/10000000000 : ℝ)] ![(3317812444199/10000000000000 : ℝ), (14464132605887/50000000000000 : ℝ), (18946805164567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166576541/400000000 : ℝ)|^4971 ≤ (3317812444199/10000000000000 : ℝ)^3947
        have hw : |(166576541/400000000 : ℝ)|=(166576541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3734970367/10000000000 : ℝ)|^4971 ≤ (14464132605887/50000000000000 : ℝ)^3947
        have hw : |(3734970367/10000000000 : ℝ)|=(3734970367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4627849081/10000000000 : ℝ)|^4971 ≤ (18946805164567/50000000000000 : ℝ)^3947
        have hw : |(4627849081/10000000000 : ℝ)|=(4627849081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1570874159/10000000000 : ℝ)*x 0 + (2575344561/5000000000 : ℝ)*x 1 + (5483427053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1570874159/10000000000 : ℝ)^4971 ≤ (242957494003/2500000000000 : ℝ)^3947 := by
    have hnat : (1570874159 : ℕ)^4971*2500000000000^3947 ≤ 242957494003^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570874159 10000000000 242957494003 2500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575344561/5000000000 : ℝ)^4971 ≤ (43362307823757/100000000000000 : ℝ)^3947 := by
    have hnat : (2575344561 : ℕ)^4971*100000000000000^3947 ≤ 43362307823757^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575344561 5000000000 43362307823757 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483427053/10000000000 : ℝ)^4971 ≤ (46919392403201/100000000000000 : ℝ)^3947 := by
    have hnat : (5483427053 : ℕ)^4971*100000000000000^3947 ≤ 46919392403201^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483427053 10000000000 46919392403201 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1570874159/10000000000 : ℝ), (2575344561/5000000000 : ℝ), (5483427053/10000000000 : ℝ)] ![(242957494003/2500000000000 : ℝ), (43362307823757/100000000000000 : ℝ), (46919392403201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1570874159/10000000000 : ℝ)|^4971 ≤ (242957494003/2500000000000 : ℝ)^3947
        have hw : |(-1570874159/10000000000 : ℝ)|=(1570874159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575344561/5000000000 : ℝ)|^4971 ≤ (43362307823757/100000000000000 : ℝ)^3947
        have hw : |(2575344561/5000000000 : ℝ)|=(2575344561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483427053/10000000000 : ℝ)|^4971 ≤ (46919392403201/100000000000000 : ℝ)^3947
        have hw : |(5483427053/10000000000 : ℝ)|=(5483427053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329147051/625000000 : ℝ)*x 0 + (-1410851249/10000000000 : ℝ)*x 1 + (685428393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329147051/625000000 : ℝ)^4971 ≤ (44592228390161/100000000000000 : ℝ)^3947 := by
    have hnat : (329147051 : ℕ)^4971*100000000000000^3947 ≤ 44592228390161^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329147051 625000000 44592228390161 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410851249/10000000000 : ℝ)^4971 ≤ (2122094555207/25000000000000 : ℝ)^3947 := by
    have hnat : (1410851249 : ℕ)^4971*25000000000000^3947 ≤ 2122094555207^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410851249 10000000000 2122094555207 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685428393/1250000000 : ℝ)^4971 ≤ (46919393383861/100000000000000 : ℝ)^3947 := by
    have hnat : (685428393 : ℕ)^4971*100000000000000^3947 ≤ 46919393383861^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685428393 1250000000 46919393383861 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329147051/625000000 : ℝ), (-1410851249/10000000000 : ℝ), (685428393/1250000000 : ℝ)] ![(44592228390161/100000000000000 : ℝ), (2122094555207/25000000000000 : ℝ), (46919393383861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329147051/625000000 : ℝ)|^4971 ≤ (44592228390161/100000000000000 : ℝ)^3947
        have hw : |(329147051/625000000 : ℝ)|=(329147051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1410851249/10000000000 : ℝ)|^4971 ≤ (2122094555207/25000000000000 : ℝ)^3947
        have hw : |(-1410851249/10000000000 : ℝ)|=(1410851249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685428393/1250000000 : ℝ)|^4971 ≤ (46919393383861/100000000000000 : ℝ)^3947
        have hw : |(685428393/1250000000 : ℝ)|=(685428393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266352743/10000000000 : ℝ)*x 0 + (342714193/625000000 : ℝ)*x 1 + (-141085143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266352743/10000000000 : ℝ)^4971 ≤ (22296113805839/50000000000000 : ℝ)^3947 := by
    have hnat : (5266352743 : ℕ)^4971*50000000000000^3947 ≤ 22296113805839^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266352743 10000000000 22296113805839 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342714193/625000000 : ℝ)^4971 ≤ (23459696390189/50000000000000 : ℝ)^3947 := by
    have hnat : (342714193 : ℕ)^4971*50000000000000^3947 ≤ 23459696390189^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342714193 625000000 23459696390189 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141085143/1000000000 : ℝ)^4971 ≤ (8488379592337/100000000000000 : ℝ)^3947 := by
    have hnat : (141085143 : ℕ)^4971*100000000000000^3947 ≤ 8488379592337^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141085143 1000000000 8488379592337 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266352743/10000000000 : ℝ), (342714193/625000000 : ℝ), (-141085143/1000000000 : ℝ)] ![(22296113805839/50000000000000 : ℝ), (23459696390189/50000000000000 : ℝ), (8488379592337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266352743/10000000000 : ℝ)|^4971 ≤ (22296113805839/50000000000000 : ℝ)^3947
        have hw : |(5266352743/10000000000 : ℝ)|=(5266352743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342714193/625000000 : ℝ)|^4971 ≤ (23459696390189/50000000000000 : ℝ)^3947
        have hw : |(342714193/625000000 : ℝ)|=(342714193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141085143/1000000000 : ℝ)|^4971 ≤ (8488379592337/100000000000000 : ℝ)^3947
        have hw : |(-141085143/1000000000 : ℝ)|=(141085143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s1_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520597851/1250000000 : ℝ)*x 0 + (4618966837/10000000000 : ℝ)*x 1 + (3743975539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520597851/1250000000 : ℝ)^4971 ≤ (331818298747/1000000000000 : ℝ)^3947 := by
    have hnat : (520597851 : ℕ)^4971*1000000000000^3947 ≤ 331818298747^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520597851 1250000000 331818298747 1000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4618966837/10000000000 : ℝ)^4971 ≤ (18901017557561/50000000000000 : ℝ)^3947 := by
    have hnat : (4618966837 : ℕ)^4971*50000000000000^3947 ≤ 18901017557561^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618966837 10000000000 18901017557561 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743975539/10000000000 : ℝ)^4971 ≤ (14508067502641/50000000000000 : ℝ)^3947 := by
    have hnat : (3743975539 : ℕ)^4971*50000000000000^3947 ≤ 14508067502641^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743975539 10000000000 14508067502641 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520597851/1250000000 : ℝ), (4618966837/10000000000 : ℝ), (3743975539/10000000000 : ℝ)] ![(331818298747/1000000000000 : ℝ), (18901017557561/50000000000000 : ℝ), (14508067502641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520597851/1250000000 : ℝ)|^4971 ≤ (331818298747/1000000000000 : ℝ)^3947
        have hw : |(520597851/1250000000 : ℝ)|=(520597851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4618966837/10000000000 : ℝ)|^4971 ≤ (18901017557561/50000000000000 : ℝ)^3947
        have hw : |(4618966837/10000000000 : ℝ)|=(4618966837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743975539/10000000000 : ℝ)|^4971 ≤ (14508067502641/50000000000000 : ℝ)^3947
        have hw : |(3743975539/10000000000 : ℝ)|=(3743975539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5771/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4963/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17147/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5771/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5771/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5771/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5771/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5771/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5771/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5091/100000 : ℝ) ^ (4967/1024 : ℝ) ≤ (53362637648273/100000000000000000000 : ℝ) := by
    have hpowers : (5091/100000 : ℝ)^4967 ≤ (53362637648273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5091 : ℕ)^4967*100000000000000000000^1024 ≤ 53362637648273^1024*100000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5091 100000 53362637648273 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5091/100000 : ℝ)) (X := (53362637648273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5771/25000 : ℝ) ^ (4967/1024 : ℝ) ≤ (16319829007409101/20000000000000000000 : ℝ) := by
    have hpowers : (5771/25000 : ℝ)^4967 ≤ (16319829007409101/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5771 : ℕ)^4967*20000000000000000000^1024 ≤ 16319829007409101^1024*25000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5771 25000 16319829007409101 20000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5771/25000 : ℝ)) (X := (16319829007409101/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000053362637648273/50000000000000000000 : ℝ) ≤ (1250000275031799/1250000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50000053362637648273/50000000000000000000 : ℝ)^1024 ≤ (1250000275031799/1250000000000000 : ℝ)^4967 := by
      have hnat : (50000053362637648273 : ℕ)^1024*1250000000000000^4967 ≤ 1250000275031799^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000053362637648273 50000000000000000000 1250000275031799 1250000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000275031799/1250000000000000 : ℝ)) (X := (50000053362637648273/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50040826253837346889/50000000000000000000 : ℝ) ≤ (39069073469493/39062500000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50040826253837346889/50000000000000000000 : ℝ)^1024 ≤ (39069073469493/39062500000000 : ℝ)^4967 := by
      have hnat : (50040826253837346889 : ℕ)^1024*39062500000000^4967 ≤ 39069073469493^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040826253837346889 50000000000000000000 39069073469493 39062500000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39069073469493/39062500000000 : ℝ)) (X := (50040826253837346889/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10016319829007409101/10000000000000000000 : ℝ) ≤ (1250420427015753/1250000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (10016319829007409101/10000000000000000000 : ℝ)^1024 ≤ (1250420427015753/1250000000000000 : ℝ)^4967 := by
      have hnat : (10016319829007409101 : ℕ)^1024*1250000000000000^4967 ≤ 1250420427015753^4967*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10016319829007409101 10000000000000000000 1250420427015753 1250000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250420427015753/1250000000000000 : ℝ)) (X := (10016319829007409101/10000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53362637648273/100000000000000000000 : ℝ) ≤ ((22489115954896849593/22491250000000000000 : ℝ)+2*(210075991977/224912500000000 : ℝ)*(5091/100000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (22489115954896849593/22491250000000000000 : ℝ)+2*(210075991977/224912500000000 : ℝ)*(5091/100000 : ℝ)=(1250000275031799/1250000000000000 : ℝ) by norm_num, show 1+2*(53362637648273/100000000000000000000 : ℝ)=(50000053362637648273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16319829007409101/20000000000000000000 : ℝ)+(53362637648273/100000000000000000000 : ℝ) ≤ ((22489115954896849593/22491250000000000000 : ℝ)+(210075991977/224912500000000 : ℝ)*((5771/25000 : ℝ)+(5091/100000 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (22489115954896849593/22491250000000000000 : ℝ)+(210075991977/224912500000000 : ℝ)*((5771/25000 : ℝ)+(5091/100000 : ℝ))=(39069073469493/39062500000000 : ℝ) by norm_num, show 1+(16319829007409101/20000000000000000000 : ℝ)+(53362637648273/100000000000000000000 : ℝ)=(50040826253837346889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16319829007409101/20000000000000000000 : ℝ) ≤ ((22489115954896849593/22491250000000000000 : ℝ)+2*(210075991977/224912500000000 : ℝ)*(5771/25000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (22489115954896849593/22491250000000000000 : ℝ)+2*(210075991977/224912500000000 : ℝ)*(5771/25000 : ℝ)=(1250420427015753/1250000000000000 : ℝ) by norm_num, show 1+2*(16319829007409101/20000000000000000000 : ℝ)=(10016319829007409101/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22489115954896849593/22491250000000000000 : ℝ)*(X 1 0+X 2 0)+(210075991977/224912500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (5091/100000 : ℝ)) (hi := (5771/25000 : ℝ)) (c := (22489115954896849593/22491250000000000000 : ℝ)) (alpha := (210075991977/224912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22489115954896849593/22491250000000000000 : ℝ)*(X 0 1+X 2 1)+(210075991977/224912500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (5091/100000 : ℝ)) (hi := (5771/25000 : ℝ)) (c := (22489115954896849593/22491250000000000000 : ℝ)) (alpha := (210075991977/224912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22489115954896849593/22491250000000000000 : ℝ)*(X 0 2+X 1 2)+(210075991977/224912500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (5091/100000 : ℝ)) (hi := (5771/25000 : ℝ)) (c := (22489115954896849593/22491250000000000000 : ℝ)) (alpha := (210075991977/224912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2513173/16000000 : ℝ)*X 0 0+(1371712923/2500000000 : ℝ)*X 0 1+(128682787/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5357250347/10000000000 : ℝ)*X 1 0+(-349393463/2000000000 : ℝ)*X 1 1+(2573655739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334828153/625000000 : ℝ)*X 2 0+(5147311471/10000000000 : ℝ)*X 2 1+(-436741797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((166576541/400000000 : ℝ)*X 0 0+(3734970367/10000000000 : ℝ)*X 0 1+(4627849081/10000000000 : ℝ)*X 0 2+(166576541/400000000 : ℝ)*X 1 0+(3734970367/10000000000 : ℝ)*X 1 1+(4627849081/10000000000 : ℝ)*X 1 2+(166576541/400000000 : ℝ)*X 2 0+(3734970367/10000000000 : ℝ)*X 2 1+(4627849081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1570874159/10000000000 : ℝ)*X 0 0+(2575344561/5000000000 : ℝ)*X 0 1+(5483427053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329147051/625000000 : ℝ)*X 1 0+(-1410851249/10000000000 : ℝ)*X 1 1+(685428393/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266352743/10000000000 : ℝ)*X 2 0+(342714193/625000000 : ℝ)*X 2 1+(-141085143/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520597851/1250000000 : ℝ)*X 0 0+(4618966837/10000000000 : ℝ)*X 0 1+(3743975539/10000000000 : ℝ)*X 0 2+(520597851/1250000000 : ℝ)*X 1 0+(4618966837/10000000000 : ℝ)*X 1 1+(3743975539/10000000000 : ℝ)*X 1 2+(520597851/1250000000 : ℝ)*X 2 0+(4618966837/10000000000 : ℝ)*X 2 1+(3743975539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1086883883464149333596657187/112456250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (709672251/50000000000000 : ℝ)*(base19) + (60736789/6250000000000 : ℝ)*(base23) + (269513233/100000000000000 : ℝ)*(lower2) + (324342419/100000000000000 : ℝ)*(upper3) + (1028021/25000000000000 : ℝ)*(upper5) + (203258324743301/10000000000000 : ℝ)*(major0) + (203258324743301/10000000000000 : ℝ)*(major1) + (203258324743301/10000000000000 : ℝ)*(major2) + (1472586421661201/50000000000000 : ℝ)*(sp0) + (368147781074311/12500000000000 : ℝ)*(sp1) + (589036539230073/20000000000000 : ℝ)*(sp2) + (559988047102807/50000000000000 : ℝ)*(sp3) + (10824616587/100000000000000 : ℝ)*(sp4) + (6410556451/100000000000000 : ℝ)*(sp7) + (223996500952413/20000000000000 : ℝ)*(f.failure) + (2945183667938989/100000000000000 : ℝ)*(f.sum) + (78591674737543/17993000000000000000000000000 : ℝ)*base66 + (1074316567906461007/224912500000000000000000000000000 : ℝ)*base68 + (2373876572820248507/224912500000000000000000000000000 : ℝ)*base70 + (2138846428990248507/224912500000000000000000000000000 : ℝ)*base72 + (23200474880033/17993000000000000000000000000 : ℝ)*base74 + (5699394606103361007/224912500000000000000000000000000 : ℝ)*base76 + (2064923579349148507/224912500000000000000000000000000 : ℝ)*base78 + (2088326953446223507/224912500000000000000000000000000 : ℝ)*base80 + (116279579132347/17993000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13771033/1000000000000000000000 : ℝ)*base89 + (13771033/1000000000000000000000 : ℝ)*base91 + (13771033/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5292788669896396466771652429/562281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (313880393/20000000000000 : ℝ)*(base19) + (427992381/25000000000000 : ℝ)*(base23) + (236114041/100000000000000 : ℝ)*(upper3) + (9088987/10000000000000 : ℝ)*(lower4) + (188421469/100000000000000 : ℝ)*(upper5) + (1037058686263117/50000000000000 : ℝ)*(major0) + (1037058686263117/50000000000000 : ℝ)*(major1) + (1037058686263117/50000000000000 : ℝ)*(major2) + (3719453397/25000000000000 : ℝ)*(sp1) + (15552213083/100000000000000 : ℝ)*(sp2) + (751341507059349/25000000000000 : ℝ)*(sp4) + (1502674790510921/50000000000000 : ℝ)*(sp5) + (3005348764054789/100000000000000 : ℝ)*(sp6) + (285717100761577/25000000000000 : ℝ)*(sp7) + (285717100761577/25000000000000 : ℝ)*(f.failure) + (751341507059349/25000000000000 : ℝ)*(f.sum) + (37729555499611/22491250000000000000000000000 : ℝ)*base65 + (7937285019924488619/1124562500000000000000000000000000 : ℝ)*base68 + (17555263118471738619/1124562500000000000000000000000000 : ℝ)*base70 + (6229188010296488619/1124562500000000000000000000000000 : ℝ)*base72 + (149499945329537/44982500000000000000000000000 : ℝ)*base73 + (1365800834329988619/1124562500000000000000000000000000 : ℝ)*base76 + (5618691483851426119/1124562500000000000000000000000000 : ℝ)*base78 + (10040321718768801119/1124562500000000000000000000000000 : ℝ)*base80 + (63964968141613/44982500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2114443/1250000000000000000000 : ℝ)*base90 + (2114443/1250000000000000000000 : ℝ)*base92 + (2114443/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1663_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5771/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17147/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1663_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1663_s2_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1578875859/10000000000 : ℝ)*x 0 + (2723282803/5000000000 : ℝ)*x 1 + (1295553107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1578875859/10000000000 : ℝ)^4971 ≤ (4890343394729/50000000000000 : ℝ)^3947 := by
    have hnat : (1578875859 : ℕ)^4971*50000000000000^3947 ≤ 4890343394729^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578875859 10000000000 4890343394729 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723282803/5000000000 : ℝ)^4971 ≤ (23261251356007/50000000000000 : ℝ)^3947 := by
    have hnat : (2723282803 : ℕ)^4971*50000000000000^3947 ≤ 23261251356007^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723282803 5000000000 23261251356007 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295553107/2500000000 : ℝ)^4971 ≤ (43696810485311/100000000000000 : ℝ)^3947 := by
    have hnat : (1295553107 : ℕ)^4971*100000000000000^3947 ≤ 43696810485311^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295553107 2500000000 43696810485311 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1578875859/10000000000 : ℝ), (2723282803/5000000000 : ℝ), (1295553107/2500000000 : ℝ)] ![(4890343394729/50000000000000 : ℝ), (23261251356007/50000000000000 : ℝ), (43696810485311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1578875859/10000000000 : ℝ)|^4971 ≤ (4890343394729/50000000000000 : ℝ)^3947
        have hw : |(-1578875859/10000000000 : ℝ)|=(1578875859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723282803/5000000000 : ℝ)|^4971 ≤ (23261251356007/50000000000000 : ℝ)^3947
        have hw : |(2723282803/5000000000 : ℝ)|=(2723282803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295553107/2500000000 : ℝ)|^4971 ≤ (43696810485311/100000000000000 : ℝ)^3947
        have hw : |(1295553107/2500000000 : ℝ)|=(1295553107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069308611/2000000000 : ℝ)*x 0 + (-1714971767/10000000000 : ℝ)*x 1 + (518221259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069308611/2000000000 : ℝ)^4971 ≤ (22724535594649/50000000000000 : ℝ)^3947 := by
    have hnat : (1069308611 : ℕ)^4971*50000000000000^3947 ≤ 22724535594649^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069308611 2000000000 22724535594649 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714971767/10000000000 : ℝ)^4971 ≤ (542705829567/5000000000000 : ℝ)^3947 := by
    have hnat : (1714971767 : ℕ)^4971*5000000000000^3947 ≤ 542705829567^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714971767 10000000000 542705829567 5000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518221259/1000000000 : ℝ)^4971 ≤ (43696812205699/100000000000000 : ℝ)^3947 := by
    have hnat : (518221259 : ℕ)^4971*100000000000000^3947 ≤ 43696812205699^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518221259 1000000000 43696812205699 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069308611/2000000000 : ℝ), (-1714971767/10000000000 : ℝ), (518221259/1000000000 : ℝ)] ![(22724535594649/50000000000000 : ℝ), (542705829567/5000000000000 : ℝ), (43696812205699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069308611/2000000000 : ℝ)|^4971 ≤ (22724535594649/50000000000000 : ℝ)^3947
        have hw : |(1069308611/2000000000 : ℝ)|=(1069308611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714971767/10000000000 : ℝ)|^4971 ≤ (542705829567/5000000000000 : ℝ)^3947
        have hw : |(-1714971767/10000000000 : ℝ)|=(1714971767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518221259/1000000000 : ℝ)|^4971 ≤ (43696812205699/100000000000000 : ℝ)^3947
        have hw : |(518221259/1000000000 : ℝ)|=(518221259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106930863/200000000 : ℝ)*x 0 + (5182212431/10000000000 : ℝ)*x 1 + (-1714971851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106930863/200000000 : ℝ)^4971 ≤ (11362268051593/25000000000000 : ℝ)^3947 := by
    have hnat : (106930863 : ℕ)^4971*25000000000000^3947 ≤ 11362268051593^3947*200000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106930863 200000000 11362268051593 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182212431/10000000000 : ℝ)^4971 ≤ (4369681051717/10000000000000 : ℝ)^3947 := by
    have hnat : (5182212431 : ℕ)^4971*10000000000000^3947 ≤ 4369681051717^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182212431 10000000000 4369681051717 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714971851/10000000000 : ℝ)^4971 ≤ (5427058630453/50000000000000 : ℝ)^3947 := by
    have hnat : (1714971851 : ℕ)^4971*50000000000000^3947 ≤ 5427058630453^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714971851 10000000000 5427058630453 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106930863/200000000 : ℝ), (5182212431/10000000000 : ℝ), (-1714971851/10000000000 : ℝ)] ![(11362268051593/25000000000000 : ℝ), (4369681051717/10000000000000 : ℝ), (5427058630453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106930863/200000000 : ℝ)|^4971 ≤ (11362268051593/25000000000000 : ℝ)^3947
        have hw : |(106930863/200000000 : ℝ)|=(106930863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182212431/10000000000 : ℝ)|^4971 ≤ (4369681051717/10000000000000 : ℝ)^3947
        have hw : |(5182212431/10000000000 : ℝ)|=(5182212431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714971851/10000000000 : ℝ)|^4971 ≤ (5427058630453/50000000000000 : ℝ)^3947
        have hw : |(-1714971851/10000000000 : ℝ)|=(1714971851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170501261/10000000000 : ℝ)*x 0 + (3833227407/10000000000 : ℝ)*x 1 + (4528388691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170501261/10000000000 : ℝ)^4971 ≤ (6647844087569/20000000000000 : ℝ)^3947 := by
    have hnat : (4170501261 : ℕ)^4971*20000000000000^3947 ≤ 6647844087569^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170501261 10000000000 6647844087569 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3833227407/10000000000 : ℝ)^4971 ≤ (14944989219719/50000000000000 : ℝ)^3947 := by
    have hnat : (3833227407 : ℕ)^4971*50000000000000^3947 ≤ 14944989219719^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3833227407 10000000000 14944989219719 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528388691/10000000000 : ℝ)^4971 ≤ (460885013747/1250000000000 : ℝ)^3947 := by
    have hnat : (4528388691 : ℕ)^4971*1250000000000^3947 ≤ 460885013747^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528388691 10000000000 460885013747 1250000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170501261/10000000000 : ℝ), (3833227407/10000000000 : ℝ), (4528388691/10000000000 : ℝ)] ![(6647844087569/20000000000000 : ℝ), (14944989219719/50000000000000 : ℝ), (460885013747/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170501261/10000000000 : ℝ)|^4971 ≤ (6647844087569/20000000000000 : ℝ)^3947
        have hw : |(4170501261/10000000000 : ℝ)|=(4170501261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3833227407/10000000000 : ℝ)|^4971 ≤ (14944989219719/50000000000000 : ℝ)^3947
        have hw : |(3833227407/10000000000 : ℝ)|=(3833227407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528388691/10000000000 : ℝ)|^4971 ≤ (460885013747/1250000000000 : ℝ)^3947
        have hw : |(4528388691/10000000000 : ℝ)|=(4528388691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-394735609/2500000000 : ℝ)*x 0 + (518426509/1000000000 : ℝ)*x 1 + (5444490777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394735609/2500000000 : ℝ)^4971 ≤ (4890603108277/50000000000000 : ℝ)^3947 := by
    have hnat : (394735609 : ℕ)^4971*50000000000000^3947 ≤ 4890603108277^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394735609 2500000000 4890603108277 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518426509/1000000000 : ℝ)^4971 ≤ (2732413137839/6250000000000 : ℝ)^3947 := by
    have hnat : (518426509 : ℕ)^4971*6250000000000^3947 ≤ 2732413137839^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518426509 1000000000 2732413137839 6250000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444490777/10000000000 : ℝ)^4971 ≤ (46500183553661/100000000000000 : ℝ)^3947 := by
    have hnat : (5444490777 : ℕ)^4971*100000000000000^3947 ≤ 46500183553661^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444490777 10000000000 46500183553661 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394735609/2500000000 : ℝ), (518426509/1000000000 : ℝ), (5444490777/10000000000 : ℝ)] ![(4890603108277/50000000000000 : ℝ), (2732413137839/6250000000000 : ℝ), (46500183553661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394735609/2500000000 : ℝ)|^4971 ≤ (4890603108277/50000000000000 : ℝ)^3947
        have hw : |(-394735609/2500000000 : ℝ)|=(394735609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518426509/1000000000 : ℝ)|^4971 ≤ (2732413137839/6250000000000 : ℝ)^3947
        have hw : |(518426509/1000000000 : ℝ)|=(518426509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444490777/10000000000 : ℝ)|^4971 ≤ (46500183553661/100000000000000 : ℝ)^3947
        have hw : |(5444490777/10000000000 : ℝ)|=(5444490777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275816279/10000000000 : ℝ)*x 0 + (-72634671/500000000 : ℝ)*x 1 + (2722245429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275816279/10000000000 : ℝ)^4971 ≤ (44693171603937/100000000000000 : ℝ)^3947 := by
    have hnat : (5275816279 : ℕ)^4971*100000000000000^3947 ≤ 44693171603937^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275816279 10000000000 44693171603937 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72634671/500000000 : ℝ)^4971 ≤ (8806643959577/100000000000000 : ℝ)^3947 := by
    have hnat : (72634671 : ℕ)^4971*100000000000000^3947 ≤ 8806643959577^3947*500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72634671 500000000 8806643959577 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722245429/5000000000 : ℝ)^4971 ≤ (46500184424943/100000000000000 : ℝ)^3947 := by
    have hnat : (2722245429 : ℕ)^4971*100000000000000^3947 ≤ 46500184424943^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722245429 5000000000 46500184424943 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275816279/10000000000 : ℝ), (-72634671/500000000 : ℝ), (2722245429/5000000000 : ℝ)] ![(44693171603937/100000000000000 : ℝ), (8806643959577/100000000000000 : ℝ), (46500184424943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275816279/10000000000 : ℝ)|^4971 ≤ (44693171603937/100000000000000 : ℝ)^3947
        have hw : |(5275816279/10000000000 : ℝ)|=(5275816279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72634671/500000000 : ℝ)|^4971 ≤ (8806643959577/100000000000000 : ℝ)^3947
        have hw : |(-72634671/500000000 : ℝ)|=(72634671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722245429/5000000000 : ℝ)|^4971 ≤ (46500184424943/100000000000000 : ℝ)^3947
        have hw : |(2722245429/5000000000 : ℝ)|=(2722245429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42206529/80000000 : ℝ)*x 0 + (1361122759/2500000000 : ℝ)*x 1 + (-181586673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42206529/80000000 : ℝ)^4971 ≤ (22346584980447/50000000000000 : ℝ)^3947 := by
    have hnat : (42206529 : ℕ)^4971*50000000000000^3947 ≤ 22346584980447^3947*80000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42206529 80000000 22346584980447 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361122759/2500000000 : ℝ)^4971 ≤ (23250093169807/50000000000000 : ℝ)^3947 := by
    have hnat : (1361122759 : ℕ)^4971*50000000000000^3947 ≤ 23250093169807^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361122759 2500000000 23250093169807 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181586673/1250000000 : ℝ)^4971 ≤ (1761328736943/20000000000000 : ℝ)^3947 := by
    have hnat : (181586673 : ℕ)^4971*20000000000000^3947 ≤ 1761328736943^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181586673 1250000000 1761328736943 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42206529/80000000 : ℝ), (1361122759/2500000000 : ℝ), (-181586673/1250000000 : ℝ)] ![(22346584980447/50000000000000 : ℝ), (23250093169807/50000000000000 : ℝ), (1761328736943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42206529/80000000 : ℝ)|^4971 ≤ (22346584980447/50000000000000 : ℝ)^3947
        have hw : |(42206529/80000000 : ℝ)|=(42206529/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361122759/2500000000 : ℝ)|^4971 ≤ (23250093169807/50000000000000 : ℝ)^3947
        have hw : |(1361122759/2500000000 : ℝ)|=(1361122759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181586673/1250000000 : ℝ)|^4971 ≤ (1761328736943/20000000000000 : ℝ)^3947
        have hw : |(-181586673/1250000000 : ℝ)|=(181586673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s2_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521334493/1250000000 : ℝ)*x 0 + (4522990979/10000000000 : ℝ)*x 1 + (959670799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521334493/1250000000 : ℝ)^4971 ≤ (332409738831/1000000000000 : ℝ)^3947 := by
    have hnat : (521334493 : ℕ)^4971*1000000000000^3947 ≤ 332409738831^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521334493 1250000000 332409738831 1000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522990979/10000000000 : ℝ)^4971 ≤ (9203864673127/25000000000000 : ℝ)^3947 := by
    have hnat : (4522990979 : ℕ)^4971*25000000000000^3947 ≤ 9203864673127^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522990979 10000000000 9203864673127 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959670799/2500000000 : ℝ)^4971 ≤ (14971783702063/50000000000000 : ℝ)^3947 := by
    have hnat : (959670799 : ℕ)^4971*50000000000000^3947 ≤ 14971783702063^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959670799 2500000000 14971783702063 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521334493/1250000000 : ℝ), (4522990979/10000000000 : ℝ), (959670799/2500000000 : ℝ)] ![(332409738831/1000000000000 : ℝ), (9203864673127/25000000000000 : ℝ), (14971783702063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521334493/1250000000 : ℝ)|^4971 ≤ (332409738831/1000000000000 : ℝ)^3947
        have hw : |(521334493/1250000000 : ℝ)|=(521334493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522990979/10000000000 : ℝ)|^4971 ≤ (9203864673127/25000000000000 : ℝ)^3947
        have hw : |(4522990979/10000000000 : ℝ)|=(4522990979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959670799/2500000000 : ℝ)|^4971 ≤ (14971783702063/50000000000000 : ℝ)^3947
        have hw : |(959670799/2500000000 : ℝ)|=(959670799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17147/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (267/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1019/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17147/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4963/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17147/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4963/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17147/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4963/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17147/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4963/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17147/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4963/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17147/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4963/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4963/50000 : ℝ) ^ (4967/1024 : ℝ) ≤ (1360715669845821/100000000000000000000 : ℝ) := by
    have hpowers : (4963/50000 : ℝ)^4967 ≤ (1360715669845821/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4963 : ℕ)^4967*100000000000000000000^1024 ≤ 1360715669845821^1024*50000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4963 50000 1360715669845821 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4963/50000 : ℝ)) (X := (1360715669845821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17147/100000 : ℝ) ^ (4967/1024 : ℝ) ≤ (19291402360826573/100000000000000000000 : ℝ) := by
    have hpowers : (17147/100000 : ℝ)^4967 ≤ (19291402360826573/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17147 : ℕ)^4967*100000000000000000000^1024 ≤ 19291402360826573^1024*100000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17147 100000 19291402360826573 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17147/100000 : ℝ)) (X := (19291402360826573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001360715669845821/50000000000000000000 : ℝ) ≤ (10000056104602179/10000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50001360715669845821/50000000000000000000 : ℝ)^1024 ≤ (10000056104602179/10000000000000000 : ℝ)^4967 := by
      have hnat : (50001360715669845821 : ℕ)^1024*10000000000000000^4967 ≤ 10000056104602179^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001360715669845821 50000000000000000000 10000056104602179 10000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000056104602179/10000000000000000 : ℝ)) (X := (50001360715669845821/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010326059015336197/50000000000000000000 : ℝ) ≤ (10000425730532431/10000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50010326059015336197/50000000000000000000 : ℝ)^1024 ≤ (10000425730532431/10000000000000000 : ℝ)^4967 := by
      have hnat : (50010326059015336197 : ℕ)^1024*10000000000000000^4967 ≤ 10000425730532431^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010326059015336197 50000000000000000000 10000425730532431 10000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000425730532431/10000000000000000 : ℝ)) (X := (50010326059015336197/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019291402360826573/50000000000000000000 : ℝ) ≤ (10000795356462683/10000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50019291402360826573/50000000000000000000 : ℝ)^1024 ≤ (10000795356462683/10000000000000000 : ℝ)^4967 := by
      have hnat : (50019291402360826573 : ℕ)^1024*10000000000000000^4967 ≤ 10000795356462683^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019291402360826573 50000000000000000000 10000795356462683 10000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000795356462683/10000000000000000 : ℝ)) (X := (50019291402360826573/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1360715669845821/100000000000000000000 : ℝ) ≤ ((14440613463472994371/14442000000000000000 : ℝ)+2*(92406482563/180525000000000 : ℝ)*(4963/50000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (14440613463472994371/14442000000000000000 : ℝ)+2*(92406482563/180525000000000 : ℝ)*(4963/50000 : ℝ)=(10000056104602179/10000000000000000 : ℝ) by norm_num, show 1+2*(1360715669845821/100000000000000000000 : ℝ)=(50001360715669845821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19291402360826573/100000000000000000000 : ℝ)+(1360715669845821/100000000000000000000 : ℝ) ≤ ((14440613463472994371/14442000000000000000 : ℝ)+(92406482563/180525000000000 : ℝ)*((17147/100000 : ℝ)+(4963/50000 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (14440613463472994371/14442000000000000000 : ℝ)+(92406482563/180525000000000 : ℝ)*((17147/100000 : ℝ)+(4963/50000 : ℝ))=(10000425730532431/10000000000000000 : ℝ) by norm_num, show 1+(19291402360826573/100000000000000000000 : ℝ)+(1360715669845821/100000000000000000000 : ℝ)=(50010326059015336197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19291402360826573/100000000000000000000 : ℝ) ≤ ((14440613463472994371/14442000000000000000 : ℝ)+2*(92406482563/180525000000000 : ℝ)*(17147/100000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (14440613463472994371/14442000000000000000 : ℝ)+2*(92406482563/180525000000000 : ℝ)*(17147/100000 : ℝ)=(10000795356462683/10000000000000000 : ℝ) by norm_num, show 1+2*(19291402360826573/100000000000000000000 : ℝ)=(50019291402360826573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14440613463472994371/14442000000000000000 : ℝ)*(X 1 0+X 2 0)+(92406482563/180525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (17147/100000 : ℝ)) (c := (14440613463472994371/14442000000000000000 : ℝ)) (alpha := (92406482563/180525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14440613463472994371/14442000000000000000 : ℝ)*(X 0 1+X 2 1)+(92406482563/180525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (17147/100000 : ℝ)) (c := (14440613463472994371/14442000000000000000 : ℝ)) (alpha := (92406482563/180525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14440613463472994371/14442000000000000000 : ℝ)*(X 0 2+X 1 2)+(92406482563/180525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (17147/100000 : ℝ)) (c := (14440613463472994371/14442000000000000000 : ℝ)) (alpha := (92406482563/180525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1578875859/10000000000 : ℝ)*X 0 0+(2723282803/5000000000 : ℝ)*X 0 1+(1295553107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069308611/2000000000 : ℝ)*X 1 0+(-1714971767/10000000000 : ℝ)*X 1 1+(518221259/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106930863/200000000 : ℝ)*X 2 0+(5182212431/10000000000 : ℝ)*X 2 1+(-1714971851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4170501261/10000000000 : ℝ)*X 0 0+(3833227407/10000000000 : ℝ)*X 0 1+(4528388691/10000000000 : ℝ)*X 0 2+(4170501261/10000000000 : ℝ)*X 1 0+(3833227407/10000000000 : ℝ)*X 1 1+(4528388691/10000000000 : ℝ)*X 1 2+(4170501261/10000000000 : ℝ)*X 2 0+(3833227407/10000000000 : ℝ)*X 2 1+(4528388691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-394735609/2500000000 : ℝ)*X 0 0+(518426509/1000000000 : ℝ)*X 0 1+(5444490777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275816279/10000000000 : ℝ)*X 1 0+(-72634671/500000000 : ℝ)*X 1 1+(2722245429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42206529/80000000 : ℝ)*X 2 0+(1361122759/2500000000 : ℝ)*X 2 1+(-181586673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((521334493/1250000000 : ℝ)*X 0 0+(4522990979/10000000000 : ℝ)*X 0 1+(959670799/2500000000 : ℝ)*X 0 2+(521334493/1250000000 : ℝ)*X 1 0+(4522990979/10000000000 : ℝ)*X 1 1+(959670799/2500000000 : ℝ)*X 1 2+(521334493/1250000000 : ℝ)*X 2 0+(4522990979/10000000000 : ℝ)*X 2 1+(959670799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (444471172148355995983705629/60175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221464141/20000000000000 : ℝ)*(base19) + (560605831/50000000000000 : ℝ)*(base23) + (14255097/50000000000000 : ℝ)*(lower2) + (210712203/100000000000000 : ℝ)*(upper3) + (5706657/5000000000000 : ℝ)*(upper5) + (1305343860549999/50000000000000 : ℝ)*(major0) + (1305343860549999/50000000000000 : ℝ)*(major1) + (1305343860549999/50000000000000 : ℝ)*(major2) + (756566839321051/20000000000000 : ℝ)*(sp0) + (118213991633103/3125000000000 : ℝ)*(sp1) + (189142385918417/5000000000000 : ℝ)*(sp2) + (287704038801437/20000000000000 : ℝ)*(sp3) + (14642974747/100000000000000 : ℝ)*(sp4) + (1232480497/20000000000000 : ℝ)*(sp7) + (143852635640967/10000000000000 : ℝ)*(f.failure) + (1891424419790001/50000000000000 : ℝ)*(f.sum) + (3418253779937/3008750000000000000000000000 : ℝ)*base66 + (2470095073213661457/240700000000000000000000000000000 : ℝ)*base68 + (2330118535782461457/240700000000000000000000000000000 : ℝ)*base70 + (2408458190188161457/240700000000000000000000000000000 : ℝ)*base72 + (22612152184449/6017500000000000000000000000 : ℝ)*base74 + (770285431420838543/240700000000000000000000000000000 : ℝ)*base75 + (2147510920192161457/240700000000000000000000000000000 : ℝ)*base78 + (2498808845359661457/240700000000000000000000000000000 : ℝ)*base80 + (49791388014593/12035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6503547/500000000000000000000 : ℝ)*base89 + (6503547/500000000000000000000 : ℝ)*base91 + (6503547/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25991536874528625114082863/4150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1022060223/100000000000000 : ℝ)*(base19) + (996735573/100000000000000 : ℝ)*(base23) + (8733577/25000000000000 : ℝ)*(upper2) + (43665769/25000000000000 : ℝ)*(upper3) + (150895383/100000000000000 : ℝ)*(upper5) + (1326036871303221/50000000000000 : ℝ)*(major0) + (1326036871303221/50000000000000 : ℝ)*(major1) + (1326036871303221/50000000000000 : ℝ)*(major2) + (2455897013/20000000000000 : ℝ)*(sp1) + (1727293613/12500000000000 : ℝ)*(sp2) + (76856332579017/2000000000000 : ℝ)*(sp4) + (1921401663702781/50000000000000 : ℝ)*(sp5) + (3842801813866373/100000000000000 : ℝ)*(sp6) + (365332661873663/25000000000000 : ℝ)*(sp7) + (365332661873663/25000000000000 : ℝ)*(f.failure) + (76856332579017/2000000000000 : ℝ)*(f.sum) + (958587280439/376093750000000000000000000 : ℝ)*base65 + (2148408058781402997/240700000000000000000000000000000 : ℝ)*base67 + (4475806779417602997/240700000000000000000000000000000 : ℝ)*base69 + (1554120227424302997/240700000000000000000000000000000 : ℝ)*base71 + (44599269620673/12035000000000000000000000000 : ℝ)*base73 + (4062763149310402997/240700000000000000000000000000000 : ℝ)*base75 + (3438041854547902997/240700000000000000000000000000000 : ℝ)*base77 + (2263094014215002997/240700000000000000000000000000000 : ℝ)*base79 + (8021612403771/1504375000000000000000000000 : ℝ)*base81 + (22332717/1250000000000000000000 : ℝ)*base90 + (22332717/1250000000000000000000 : ℝ)*base92 + (22332717/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1663_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17147/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1663_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1663_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1663_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1663_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1663_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1663_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

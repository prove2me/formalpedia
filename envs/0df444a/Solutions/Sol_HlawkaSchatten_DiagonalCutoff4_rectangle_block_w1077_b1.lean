-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:14:54.106248+00:00
-- url     : https://prove2.me/submissions/b492ddf0-27f4-4182-aad1-b4ca920bb4b6

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
theorem support_rectangle_w1077_s3_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10968849/50000000 : ℝ)*x 0 + (108725169/200000000 : ℝ)*x 1 + (5225563797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10968849/50000000 : ℝ)^4135 ≤ (6657498148567/50000000000000 : ℝ)^3111 := by
    have hnat : (10968849 : ℕ)^4135*50000000000000^3111 ≤ 6657498148567^3111*50000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10968849 50000000 6657498148567 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108725169/200000000 : ℝ)^4135 ≤ (44480831926041/100000000000000 : ℝ)^3111 := by
    have hnat : (108725169 : ℕ)^4135*100000000000000^3111 ≤ 44480831926041^3111*200000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108725169 200000000 44480831926041 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225563797/10000000000 : ℝ)^4135 ≤ (21102085879073/50000000000000 : ℝ)^3111 := by
    have hnat : (5225563797 : ℕ)^4135*50000000000000^3111 ≤ 21102085879073^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225563797 10000000000 21102085879073 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10968849/50000000 : ℝ), (108725169/200000000 : ℝ), (5225563797/10000000000 : ℝ)] ![(6657498148567/50000000000000 : ℝ), (44480831926041/100000000000000 : ℝ), (21102085879073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10968849/50000000 : ℝ)|^4135 ≤ (6657498148567/50000000000000 : ℝ)^3111
        have hw : |(-10968849/50000000 : ℝ)|=(10968849/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108725169/200000000 : ℝ)|^4135 ≤ (44480831926041/100000000000000 : ℝ)^3111
        have hw : |(108725169/200000000 : ℝ)|=(108725169/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225563797/10000000000 : ℝ)|^4135 ≤ (21102085879073/50000000000000 : ℝ)^3111
        have hw : |(5225563797/10000000000 : ℝ)|=(5225563797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677704243/5000000000 : ℝ)*x 0 + (-575408171/2500000000 : ℝ)*x 1 + (5225563831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677704243/5000000000 : ℝ)^4135 ≤ (43603709392623/100000000000000 : ℝ)^3111 := by
    have hnat : (2677704243 : ℕ)^4135*100000000000000^3111 ≤ 43603709392623^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677704243 5000000000 43603709392623 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575408171/2500000000 : ℝ)^4135 ≤ (7096059238577/50000000000000 : ℝ)^3111 := by
    have hnat : (575408171 : ℕ)^4135*50000000000000^3111 ≤ 7096059238577^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575408171 2500000000 7096059238577 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225563831/10000000000 : ℝ)^4135 ≤ (42204172123133/100000000000000 : ℝ)^3111 := by
    have hnat : (5225563831 : ℕ)^4135*100000000000000^3111 ≤ 42204172123133^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225563831 10000000000 42204172123133 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677704243/5000000000 : ℝ), (-575408171/2500000000 : ℝ), (5225563831/10000000000 : ℝ)] ![(43603709392623/100000000000000 : ℝ), (7096059238577/50000000000000 : ℝ), (42204172123133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677704243/5000000000 : ℝ)|^4135 ≤ (43603709392623/100000000000000 : ℝ)^3111
        have hw : |(2677704243/5000000000 : ℝ)|=(2677704243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-575408171/2500000000 : ℝ)|^4135 ≤ (7096059238577/50000000000000 : ℝ)^3111
        have hw : |(-575408171/2500000000 : ℝ)|=(575408171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225563831/10000000000 : ℝ)|^4135 ≤ (42204172123133/100000000000000 : ℝ)^3111
        have hw : |(5225563831/10000000000 : ℝ)|=(5225563831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355408439/10000000000 : ℝ)*x 0 + (5225564231/10000000000 : ℝ)*x 1 + (-2301632221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355408439/10000000000 : ℝ)^4135 ≤ (4360370888399/10000000000000 : ℝ)^3111 := by
    have hnat : (5355408439 : ℕ)^4135*10000000000000^3111 ≤ 4360370888399^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355408439 10000000000 4360370888399 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225564231/10000000000 : ℝ)^4135 ≤ (4220417641709/10000000000000 : ℝ)^3111 := by
    have hnat : (5225564231 : ℕ)^4135*10000000000000^3111 ≤ 4220417641709^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225564231 10000000000 4220417641709 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2301632221/10000000000 : ℝ)^4135 ≤ (14192114682539/100000000000000 : ℝ)^3111 := by
    have hnat : (2301632221 : ℕ)^4135*100000000000000^3111 ≤ 14192114682539^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301632221 10000000000 14192114682539 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355408439/10000000000 : ℝ), (5225564231/10000000000 : ℝ), (-2301632221/10000000000 : ℝ)] ![(4360370888399/10000000000000 : ℝ), (4220417641709/10000000000000 : ℝ), (14192114682539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355408439/10000000000 : ℝ)|^4135 ≤ (4360370888399/10000000000000 : ℝ)^3111
        have hw : |(5355408439/10000000000 : ℝ)|=(5355408439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225564231/10000000000 : ℝ)|^4135 ≤ (4220417641709/10000000000000 : ℝ)^3111
        have hw : |(5225564231/10000000000 : ℝ)|=(5225564231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2301632221/10000000000 : ℝ)|^4135 ≤ (14192114682539/100000000000000 : ℝ)^3111
        have hw : |(-2301632221/10000000000 : ℝ)|=(2301632221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874239277/2000000000 : ℝ)*x 0 + (2084610257/5000000000 : ℝ)*x 1 + (916610673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874239277/2000000000 : ℝ)^4135 ≤ (33289115465361/100000000000000 : ℝ)^3111 := by
    have hnat : (874239277 : ℕ)^4135*100000000000000^3111 ≤ 33289115465361^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874239277 2000000000 33289115465361 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084610257/5000000000 : ℝ)^4135 ≤ (31260374210857/100000000000000 : ℝ)^3111 := by
    have hnat : (2084610257 : ℕ)^4135*100000000000000^3111 ≤ 31260374210857^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084610257 5000000000 31260374210857 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916610673/2000000000 : ℝ)^4135 ≤ (2215656894313/6250000000000 : ℝ)^3111 := by
    have hnat : (916610673 : ℕ)^4135*6250000000000^3111 ≤ 2215656894313^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916610673 2000000000 2215656894313 6250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874239277/2000000000 : ℝ), (2084610257/5000000000 : ℝ), (916610673/2000000000 : ℝ)] ![(33289115465361/100000000000000 : ℝ), (31260374210857/100000000000000 : ℝ), (2215656894313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874239277/2000000000 : ℝ)|^4135 ≤ (33289115465361/100000000000000 : ℝ)^3111
        have hw : |(874239277/2000000000 : ℝ)|=(874239277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084610257/5000000000 : ℝ)|^4135 ≤ (31260374210857/100000000000000 : ℝ)^3111
        have hw : |(2084610257/5000000000 : ℝ)|=(2084610257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916610673/2000000000 : ℝ)|^4135 ≤ (2215656894313/6250000000000 : ℝ)^3111
        have hw : |(916610673/2000000000 : ℝ)|=(916610673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438758371/2000000000 : ℝ)*x 0 + (5226420407/10000000000 : ℝ)*x 1 + (1358849127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438758371/2000000000 : ℝ)^4135 ≤ (13315174220621/100000000000000 : ℝ)^3111 := by
    have hnat : (438758371 : ℕ)^4135*100000000000000^3111 ≤ 13315174220621^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438758371 2000000000 13315174220621 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226420407/10000000000 : ℝ)^4135 ≤ (8442673524627/20000000000000 : ℝ)^3111 := by
    have hnat : (5226420407 : ℕ)^4135*20000000000000^3111 ≤ 8442673524627^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226420407 10000000000 8442673524627 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358849127/2500000000 : ℝ)^4135 ≤ (5558932267549/12500000000000 : ℝ)^3111 := by
    have hnat : (1358849127 : ℕ)^4135*12500000000000^3111 ≤ 5558932267549^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358849127 2500000000 5558932267549 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438758371/2000000000 : ℝ), (5226420407/10000000000 : ℝ), (1358849127/2500000000 : ℝ)] ![(13315174220621/100000000000000 : ℝ), (8442673524627/20000000000000 : ℝ), (5558932267549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438758371/2000000000 : ℝ)|^4135 ≤ (13315174220621/100000000000000 : ℝ)^3111
        have hw : |(-438758371/2000000000 : ℝ)|=(438758371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226420407/10000000000 : ℝ)|^4135 ≤ (8442673524627/20000000000000 : ℝ)^3111
        have hw : |(5226420407/10000000000 : ℝ)|=(5226420407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358849127/2500000000 : ℝ)|^4135 ≤ (5558932267549/12500000000000 : ℝ)^3111
        have hw : |(1358849127/2500000000 : ℝ)|=(1358849127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662786207/1250000000 : ℝ)*x 0 + (-2091800263/10000000000 : ℝ)*x 1 + (5435396533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662786207/1250000000 : ℝ)^4135 ≤ (21514899733639/50000000000000 : ℝ)^3111 := by
    have hnat : (662786207 : ℕ)^4135*50000000000000^3111 ≤ 21514899733639^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662786207 1250000000 21514899733639 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091800263/10000000000 : ℝ)^4135 ≤ (12498742110419/100000000000000 : ℝ)^3111 := by
    have hnat : (2091800263 : ℕ)^4135*100000000000000^3111 ≤ 12498742110419^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091800263 10000000000 12498742110419 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435396533/10000000000 : ℝ)^4135 ≤ (8894291682453/20000000000000 : ℝ)^3111 := by
    have hnat : (5435396533 : ℕ)^4135*20000000000000^3111 ≤ 8894291682453^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435396533 10000000000 8894291682453 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662786207/1250000000 : ℝ), (-2091800263/10000000000 : ℝ), (5435396533/10000000000 : ℝ)] ![(21514899733639/50000000000000 : ℝ), (12498742110419/100000000000000 : ℝ), (8894291682453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662786207/1250000000 : ℝ)|^4135 ≤ (21514899733639/50000000000000 : ℝ)^3111
        have hw : |(662786207/1250000000 : ℝ)|=(662786207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091800263/10000000000 : ℝ)|^4135 ≤ (12498742110419/100000000000000 : ℝ)^3111
        have hw : |(-2091800263/10000000000 : ℝ)|=(2091800263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435396533/10000000000 : ℝ)|^4135 ≤ (8894291682453/20000000000000 : ℝ)^3111
        have hw : |(5435396533/10000000000 : ℝ)|=(5435396533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302289919/10000000000 : ℝ)*x 0 + (5435396767/10000000000 : ℝ)*x 1 + (-418359917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302289919/10000000000 : ℝ)^4135 ≤ (43029802304133/100000000000000 : ℝ)^3111 := by
    have hnat : (5302289919 : ℕ)^4135*100000000000000^3111 ≤ 43029802304133^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302289919 10000000000 43029802304133 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435396767/10000000000 : ℝ)^4135 ≤ (22235730478497/50000000000000 : ℝ)^3111 := by
    have hnat : (5435396767 : ℕ)^4135*50000000000000^3111 ≤ 22235730478497^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435396767 10000000000 22235730478497 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418359917/2000000000 : ℝ)^4135 ≤ (6249368362923/50000000000000 : ℝ)^3111 := by
    have hnat : (418359917 : ℕ)^4135*50000000000000^3111 ≤ 6249368362923^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418359917 2000000000 6249368362923 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302289919/10000000000 : ℝ), (5435396767/10000000000 : ℝ), (-418359917/2000000000 : ℝ)] ![(43029802304133/100000000000000 : ℝ), (22235730478497/50000000000000 : ℝ), (6249368362923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302289919/10000000000 : ℝ)|^4135 ≤ (43029802304133/100000000000000 : ℝ)^3111
        have hw : |(5302289919/10000000000 : ℝ)|=(5302289919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435396767/10000000000 : ℝ)|^4135 ≤ (22235730478497/50000000000000 : ℝ)^3111
        have hw : |(5435396767/10000000000 : ℝ)|=(5435396767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418359917/2000000000 : ℝ)|^4135 ≤ (6249368362923/50000000000000 : ℝ)^3111
        have hw : |(-418359917/2000000000 : ℝ)|=(418359917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s3_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371238391/10000000000 : ℝ)*x 0 + (2290685769/5000000000 : ℝ)*x 1 + (130341021/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371238391/10000000000 : ℝ)^4135 ≤ (832238516541/2500000000000 : ℝ)^3111 := by
    have hnat : (4371238391 : ℕ)^4135*2500000000000^3111 ≤ 832238516541^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371238391 10000000000 832238516541 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2290685769/5000000000 : ℝ)^4135 ≤ (7086644036521/20000000000000 : ℝ)^3111 := by
    have hnat : (2290685769 : ℕ)^4135*20000000000000^3111 ≤ 7086644036521^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290685769 5000000000 7086644036521 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130341021/312500000 : ℝ)^4135 ≤ (6255447829599/20000000000000 : ℝ)^3111 := by
    have hnat : (130341021 : ℕ)^4135*20000000000000^3111 ≤ 6255447829599^3111*312500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130341021 312500000 6255447829599 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371238391/10000000000 : ℝ), (2290685769/5000000000 : ℝ), (130341021/312500000 : ℝ)] ![(832238516541/2500000000000 : ℝ), (7086644036521/20000000000000 : ℝ), (6255447829599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371238391/10000000000 : ℝ)|^4135 ≤ (832238516541/2500000000000 : ℝ)^3111
        have hw : |(4371238391/10000000000 : ℝ)|=(4371238391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2290685769/5000000000 : ℝ)|^4135 ≤ (7086644036521/20000000000000 : ℝ)^3111
        have hw : |(2290685769/5000000000 : ℝ)|=(2290685769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130341021/312500000 : ℝ)|^4135 ≤ (6255447829599/20000000000000 : ℝ)^3111
        have hw : |(130341021/312500000 : ℝ)|=(130341021/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (326/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1489/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3341/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3341/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3341/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3341/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3341/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3341/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4383/50000 : ℝ) ^ (8269/2048 : ℝ) ≤ (1077674666758287/20000000000000000000 : ℝ) := by
    have hpowers : (4383/50000 : ℝ)^8269 ≤ (1077674666758287/20000000000000000000 : ℝ)^2048 := by
      have hnat : (4383 : ℕ)^8269*20000000000000000000^2048 ≤ 1077674666758287^2048*50000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4383 50000 1077674666758287 20000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4383/50000 : ℝ)) (X := (1077674666758287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3341/20000 : ℝ) ^ (8269/2048 : ℝ) ≤ (18201483137645009/25000000000000000000 : ℝ) := by
    have hpowers : (3341/20000 : ℝ)^8269 ≤ (18201483137645009/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3341 : ℕ)^8269*25000000000000000000^2048 ≤ 18201483137645009^2048*20000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3341 20000 18201483137645009 25000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3341/20000 : ℝ)) (X := (18201483137645009/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001077674666758287/10000000000000000000 : ℝ) ≤ (5000133449525463/5000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (10001077674666758287/10000000000000000000 : ℝ)^2048 ≤ (5000133449525463/5000000000000000 : ℝ)^8269 := by
      have hnat : (10001077674666758287 : ℕ)^2048*5000000000000000^8269 ≤ 5000133449525463^8269*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001077674666758287 10000000000000000000 5000133449525463 5000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000133449525463/5000000000000000 : ℝ)) (X := (10001077674666758287/10000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078194305884371471/100000000000000000000 : ℝ) ≤ (500096804242347/500000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (100078194305884371471/100000000000000000000 : ℝ)^2048 ≤ (500096804242347/500000000000000 : ℝ)^8269 := by
      have hnat : (100078194305884371471 : ℕ)^2048*500000000000000^8269 ≤ 500096804242347^8269*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078194305884371471 100000000000000000000 500096804242347 500000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500096804242347/500000000000000 : ℝ)) (X := (100078194305884371471/100000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518201483137645009/12500000000000000000 : ℝ) ≤ (5001802635321477/5000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (12518201483137645009/12500000000000000000 : ℝ)^2048 ≤ (5001802635321477/5000000000000000 : ℝ)^8269 := by
      have hnat : (12518201483137645009 : ℕ)^2048*5000000000000000^8269 ≤ 5001802635321477^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518201483137645009 12500000000000000000 5001802635321477 5000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001802635321477/5000000000000000 : ℝ)) (X := (12518201483137645009/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1077674666758287/20000000000000000000 : ℝ) ≤ ((39681427373094792033/39695000000000000000 : ℝ)+2*(834592898007/396950000000000 : ℝ)*(4383/50000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (39681427373094792033/39695000000000000000 : ℝ)+2*(834592898007/396950000000000 : ℝ)*(4383/50000 : ℝ)=(5000133449525463/5000000000000000 : ℝ) by norm_num, show 1+2*(1077674666758287/20000000000000000000 : ℝ)=(10001077674666758287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18201483137645009/25000000000000000000 : ℝ)+(1077674666758287/20000000000000000000 : ℝ) ≤ ((39681427373094792033/39695000000000000000 : ℝ)+(834592898007/396950000000000 : ℝ)*((3341/20000 : ℝ)+(4383/50000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (39681427373094792033/39695000000000000000 : ℝ)+(834592898007/396950000000000 : ℝ)*((3341/20000 : ℝ)+(4383/50000 : ℝ))=(500096804242347/500000000000000 : ℝ) by norm_num, show 1+(18201483137645009/25000000000000000000 : ℝ)+(1077674666758287/20000000000000000000 : ℝ)=(100078194305884371471/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18201483137645009/25000000000000000000 : ℝ) ≤ ((39681427373094792033/39695000000000000000 : ℝ)+2*(834592898007/396950000000000 : ℝ)*(3341/20000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (39681427373094792033/39695000000000000000 : ℝ)+2*(834592898007/396950000000000 : ℝ)*(3341/20000 : ℝ)=(5001802635321477/5000000000000000 : ℝ) by norm_num, show 1+2*(18201483137645009/25000000000000000000 : ℝ)=(12518201483137645009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39681427373094792033/39695000000000000000 : ℝ)*(X 1 0+X 2 0)+(834592898007/396950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (3341/20000 : ℝ)) (c := (39681427373094792033/39695000000000000000 : ℝ)) (alpha := (834592898007/396950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39681427373094792033/39695000000000000000 : ℝ)*(X 0 1+X 2 1)+(834592898007/396950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (3341/20000 : ℝ)) (c := (39681427373094792033/39695000000000000000 : ℝ)) (alpha := (834592898007/396950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39681427373094792033/39695000000000000000 : ℝ)*(X 0 2+X 1 2)+(834592898007/396950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (3341/20000 : ℝ)) (c := (39681427373094792033/39695000000000000000 : ℝ)) (alpha := (834592898007/396950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10968849/50000000 : ℝ)*X 0 0+(108725169/200000000 : ℝ)*X 0 1+(5225563797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677704243/5000000000 : ℝ)*X 1 0+(-575408171/2500000000 : ℝ)*X 1 1+(5225563831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355408439/10000000000 : ℝ)*X 2 0+(5225564231/10000000000 : ℝ)*X 2 1+(-2301632221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874239277/2000000000 : ℝ)*X 0 0+(2084610257/5000000000 : ℝ)*X 0 1+(916610673/2000000000 : ℝ)*X 0 2+(874239277/2000000000 : ℝ)*X 1 0+(2084610257/5000000000 : ℝ)*X 1 1+(916610673/2000000000 : ℝ)*X 1 2+(874239277/2000000000 : ℝ)*X 2 0+(2084610257/5000000000 : ℝ)*X 2 1+(916610673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438758371/2000000000 : ℝ)*X 0 0+(5226420407/10000000000 : ℝ)*X 0 1+(1358849127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662786207/1250000000 : ℝ)*X 1 0+(-2091800263/10000000000 : ℝ)*X 1 1+(5435396533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302289919/10000000000 : ℝ)*X 2 0+(5435396767/10000000000 : ℝ)*X 2 1+(-418359917/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371238391/10000000000 : ℝ)*X 0 0+(2290685769/5000000000 : ℝ)*X 0 1+(130341021/312500000 : ℝ)*X 0 2+(4371238391/10000000000 : ℝ)*X 1 0+(2290685769/5000000000 : ℝ)*X 1 1+(130341021/312500000 : ℝ)*X 1 2+(4371238391/10000000000 : ℝ)*X 2 0+(2290685769/5000000000 : ℝ)*X 2 1+(130341021/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16156374963791607567765646779/1984750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2111741433/100000000000000 : ℝ)*(base19) + (825963003/50000000000000 : ℝ)*(base23) + (55985603/25000000000000 : ℝ)*(lower2) + (50972483/50000000000000 : ℝ)*(upper3) + (113321061/50000000000000 : ℝ)*(upper5) + (3581376829827107/100000000000000 : ℝ)*(major0) + (3581376829827107/100000000000000 : ℝ)*(major1) + (3581376829827107/100000000000000 : ℝ)*(major2) + (2373120600322869/50000000000000 : ℝ)*(sp0) + (4746283049155631/100000000000000 : ℝ)*(sp1) + (2373141754485529/50000000000000 : ℝ)*(sp2) + (24164514516387/1000000000000 : ℝ)*(sp3) + (21980125663/50000000000000 : ℝ)*(sp4) + (16775776539/100000000000000 : ℝ)*(sp7) + (1208234113707619/50000000000000 : ℝ)*(f.failure) + (949257032179413/20000000000000 : ℝ)*(f.sum) + (14350614557793/39695000000000000000000000000 : ℝ)*base65 + (36226152696712061469/3969500000000000000000000000000000 : ℝ)*base68 + (51556798095603061469/3969500000000000000000000000000000 : ℝ)*base70 + (61323945021006561469/3969500000000000000000000000000000 : ℝ)*base72 + (6749411209803/9923750000000000000000000000 : ℝ)*base74 + (54675497563809561469/3969500000000000000000000000000000 : ℝ)*base76 + (40793190054228561469/3969500000000000000000000000000000 : ℝ)*base78 + (46486637826924061469/3969500000000000000000000000000000 : ℝ)*base80 + (72628947160513/9923750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (39789187/5000000000000000000000 : ℝ)*base89 + (39789187/5000000000000000000000 : ℝ)*base91 + (39789187/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4648814279253778737756642819/992375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240595959/25000000000000 : ℝ)*(base19) + (1640078613/100000000000000 : ℝ)*(base23) + (29967901/25000000000000 : ℝ)*(upper2) + (153194827/100000000000000 : ℝ)*(upper3) + (117063519/100000000000000 : ℝ)*(upper5) + (1805383737844573/50000000000000 : ℝ)*(major0) + (1805383737844573/50000000000000 : ℝ)*(major1) + (1805383737844573/50000000000000 : ℝ)*(major2) + (14204569593/100000000000000 : ℝ)*(sp1) + (35592699197/100000000000000 : ℝ)*(sp2) + (4785235769411323/100000000000000 : ℝ)*(sp4) + (2392610301228947/50000000000000 : ℝ)*(sp5) + (4785198536633513/100000000000000 : ℝ)*(sp6) + (1218149512907911/50000000000000 : ℝ)*(sp7) + (1218149512907911/50000000000000 : ℝ)*(f.failure) + (4785235769411323/100000000000000 : ℝ)*(f.sum) + (238398532096329/39695000000000000000000000000 : ℝ)*base65 + (18476554008843036909/1984750000000000000000000000000000 : ℝ)*base67 + (36698913376850786909/1984750000000000000000000000000000 : ℝ)*base69 + (12475284552939786909/1984750000000000000000000000000000 : ℝ)*base71 + (60759845143577/19847500000000000000000000000 : ℝ)*base73 + (36342825010916036909/1984750000000000000000000000000000 : ℝ)*base75 + (18988701608026786909/1984750000000000000000000000000000 : ℝ)*base77 + (35732751474227286909/1984750000000000000000000000000000 : ℝ)*base79 + (109832645197677/19847500000000000000000000000 : ℝ)*base81 + (92145497/5000000000000000000000 : ℝ)*base90 + (92145497/5000000000000000000000 : ℝ)*base92 + (92145497/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1077_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (326/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1489/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1077_s4_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197345607/10000000000 : ℝ)*x 0 + (337825649/625000000 : ℝ)*x 1 + (2627137501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197345607/10000000000 : ℝ)^4135 ≤ (1667981370083/12500000000000 : ℝ)^3111 := by
    have hnat : (2197345607 : ℕ)^4135*12500000000000^3111 ≤ 1667981370083^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197345607 10000000000 1667981370083 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337825649/625000000 : ℝ)^4135 ≤ (5517935899367/12500000000000 : ℝ)^3111 := by
    have hnat : (337825649 : ℕ)^4135*12500000000000^3111 ≤ 5517935899367^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337825649 625000000 5517935899367 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627137501/5000000000 : ℝ)^4135 ≤ (10628165459427/25000000000000 : ℝ)^3111 := by
    have hnat : (2627137501 : ℕ)^4135*25000000000000^3111 ≤ 10628165459427^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627137501 5000000000 10628165459427 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197345607/10000000000 : ℝ), (337825649/625000000 : ℝ), (2627137501/5000000000 : ℝ)] ![(1667981370083/12500000000000 : ℝ), (5517935899367/12500000000000 : ℝ), (10628165459427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197345607/10000000000 : ℝ)|^4135 ≤ (1667981370083/12500000000000 : ℝ)^3111
        have hw : |(-2197345607/10000000000 : ℝ)|=(2197345607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337825649/625000000 : ℝ)|^4135 ≤ (5517935899367/12500000000000 : ℝ)^3111
        have hw : |(337825649/625000000 : ℝ)|=(337825649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627137501/5000000000 : ℝ)|^4135 ≤ (10628165459427/25000000000000 : ℝ)^3111
        have hw : |(2627137501/5000000000 : ℝ)|=(2627137501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347706693/10000000000 : ℝ)*x 0 + (-284263093/1250000000 : ℝ)*x 1 + (5254275459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347706693/10000000000 : ℝ)^4135 ≤ (8704076110263/20000000000000 : ℝ)^3111 := by
    have hnat : (5347706693 : ℕ)^4135*20000000000000^3111 ≤ 8704076110263^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347706693 10000000000 8704076110263 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284263093/1250000000 : ℝ)^4135 ≤ (6983476338069/50000000000000 : ℝ)^3111 := by
    have hnat : (284263093 : ℕ)^4135*50000000000000^3111 ≤ 6983476338069^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284263093 1250000000 6983476338069 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254275459/10000000000 : ℝ)^4135 ≤ (42512666752411/100000000000000 : ℝ)^3111 := by
    have hnat : (5254275459 : ℕ)^4135*100000000000000^3111 ≤ 42512666752411^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254275459 10000000000 42512666752411 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347706693/10000000000 : ℝ), (-284263093/1250000000 : ℝ), (5254275459/10000000000 : ℝ)] ![(8704076110263/20000000000000 : ℝ), (6983476338069/50000000000000 : ℝ), (42512666752411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347706693/10000000000 : ℝ)|^4135 ≤ (8704076110263/20000000000000 : ℝ)^3111
        have hw : |(5347706693/10000000000 : ℝ)|=(5347706693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284263093/1250000000 : ℝ)|^4135 ≤ (6983476338069/50000000000000 : ℝ)^3111
        have hw : |(-284263093/1250000000 : ℝ)|=(284263093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254275459/10000000000 : ℝ)|^4135 ≤ (42512666752411/100000000000000 : ℝ)^3111
        have hw : |(5254275459/10000000000 : ℝ)|=(5254275459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347706737/10000000000 : ℝ)*x 0 + (164196103/312500000 : ℝ)*x 1 + (-1137052451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347706737/10000000000 : ℝ)^4135 ≤ (43520381027257/100000000000000 : ℝ)^3111 := by
    have hnat : (5347706737 : ℕ)^4135*100000000000000^3111 ≤ 43520381027257^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347706737 10000000000 43520381027257 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164196103/312500000 : ℝ)^4135 ≤ (5314083124933/12500000000000 : ℝ)^3111 := by
    have hnat : (164196103 : ℕ)^4135*12500000000000^3111 ≤ 5314083124933^3111*312500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164196103 312500000 5314083124933 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137052451/5000000000 : ℝ)^4135 ≤ (6983476982971/50000000000000 : ℝ)^3111 := by
    have hnat : (1137052451 : ℕ)^4135*50000000000000^3111 ≤ 6983476982971^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137052451 5000000000 6983476982971 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347706737/10000000000 : ℝ), (164196103/312500000 : ℝ), (-1137052451/5000000000 : ℝ)] ![(43520381027257/100000000000000 : ℝ), (5314083124933/12500000000000 : ℝ), (6983476982971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347706737/10000000000 : ℝ)|^4135 ≤ (43520381027257/100000000000000 : ℝ)^3111
        have hw : |(5347706737/10000000000 : ℝ)|=(5347706737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164196103/312500000 : ℝ)|^4135 ≤ (5314083124933/12500000000000 : ℝ)^3111
        have hw : |(164196103/312500000 : ℝ)|=(164196103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137052451/5000000000 : ℝ)|^4135 ≤ (6983476982971/50000000000000 : ℝ)^3111
        have hw : |(-1137052451/5000000000 : ℝ)|=(1137052451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373321291/10000000000 : ℝ)*x 0 + (4227629769/10000000000 : ℝ)*x 1 + (1131021983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373321291/10000000000 : ℝ)^4135 ≤ (33310626034561/100000000000000 : ℝ)^3111 := by
    have hnat : (4373321291 : ℕ)^4135*100000000000000^3111 ≤ 33310626034561^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373321291 10000000000 33310626034561 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227629769/10000000000 : ℝ)^4135 ≤ (796095266283/2500000000000 : ℝ)^3111 := by
    have hnat : (4227629769 : ℕ)^4135*2500000000000^3111 ≤ 796095266283^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227629769 10000000000 796095266283 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131021983/2500000000 : ℝ)^4135 ≤ (34845563297387/100000000000000 : ℝ)^3111 := by
    have hnat : (1131021983 : ℕ)^4135*100000000000000^3111 ≤ 34845563297387^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131021983 2500000000 34845563297387 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373321291/10000000000 : ℝ), (4227629769/10000000000 : ℝ), (1131021983/2500000000 : ℝ)] ![(33310626034561/100000000000000 : ℝ), (796095266283/2500000000000 : ℝ), (34845563297387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373321291/10000000000 : ℝ)|^4135 ≤ (33310626034561/100000000000000 : ℝ)^3111
        have hw : |(4373321291/10000000000 : ℝ)|=(4373321291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227629769/10000000000 : ℝ)|^4135 ≤ (796095266283/2500000000000 : ℝ)^3111
        have hw : |(4227629769/10000000000 : ℝ)|=(4227629769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131021983/2500000000 : ℝ)|^4135 ≤ (34845563297387/100000000000000 : ℝ)^3111
        have hw : |(1131021983/2500000000 : ℝ)|=(1131021983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098676539/5000000000 : ℝ)*x 0 + (5254715677/10000000000 : ℝ)*x 1 + (540476823/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098676539/5000000000 : ℝ)^4135 ≤ (6671955631719/50000000000000 : ℝ)^3111 := by
    have hnat : (1098676539 : ℕ)^4135*50000000000000^3111 ≤ 6671955631719^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098676539 5000000000 6671955631719 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254715677/10000000000 : ℝ)^4135 ≤ (42517401041771/100000000000000 : ℝ)^3111 := by
    have hnat : (5254715677 : ℕ)^4135*100000000000000^3111 ≤ 42517401041771^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254715677 10000000000 42517401041771 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540476823/1000000000 : ℝ)^4135 ≤ (1103467192027/2500000000000 : ℝ)^3111 := by
    have hnat : (540476823 : ℕ)^4135*2500000000000^3111 ≤ 1103467192027^3111*1000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540476823 1000000000 1103467192027 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098676539/5000000000 : ℝ), (5254715677/10000000000 : ℝ), (540476823/1000000000 : ℝ)] ![(6671955631719/50000000000000 : ℝ), (42517401041771/100000000000000 : ℝ), (1103467192027/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098676539/5000000000 : ℝ)|^4135 ≤ (6671955631719/50000000000000 : ℝ)^3111
        have hw : |(-1098676539/5000000000 : ℝ)|=(1098676539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254715677/10000000000 : ℝ)|^4135 ≤ (42517401041771/100000000000000 : ℝ)^3111
        have hw : |(5254715677/10000000000 : ℝ)|=(5254715677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540476823/1000000000 : ℝ)|^4135 ≤ (1103467192027/2500000000000 : ℝ)^3111
        have hw : |(540476823/1000000000 : ℝ)|=(540476823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309658533/10000000000 : ℝ)*x 0 + (-1061805561/5000000000 : ℝ)*x 1 + (2702384153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309658533/10000000000 : ℝ)^4135 ≤ (4310930218483/10000000000000 : ℝ)^3111 := by
    have hnat : (5309658533 : ℕ)^4135*10000000000000^3111 ≤ 4310930218483^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309658533 10000000000 4310930218483 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061805561/5000000000 : ℝ)^4135 ≤ (12752009294269/100000000000000 : ℝ)^3111 := by
    have hnat : (1061805561 : ℕ)^4135*100000000000000^3111 ≤ 12752009294269^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061805561 5000000000 12752009294269 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702384153/5000000000 : ℝ)^4135 ≤ (22069344253019/50000000000000 : ℝ)^3111 := by
    have hnat : (2702384153 : ℕ)^4135*50000000000000^3111 ≤ 22069344253019^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702384153 5000000000 22069344253019 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309658533/10000000000 : ℝ), (-1061805561/5000000000 : ℝ), (2702384153/5000000000 : ℝ)] ![(4310930218483/10000000000000 : ℝ), (12752009294269/100000000000000 : ℝ), (22069344253019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309658533/10000000000 : ℝ)|^4135 ≤ (4310930218483/10000000000000 : ℝ)^3111
        have hw : |(5309658533/10000000000 : ℝ)|=(5309658533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061805561/5000000000 : ℝ)|^4135 ≤ (12752009294269/100000000000000 : ℝ)^3111
        have hw : |(-1061805561/5000000000 : ℝ)|=(1061805561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702384153/5000000000 : ℝ)|^4135 ≤ (22069344253019/50000000000000 : ℝ)^3111
        have hw : |(2702384153/5000000000 : ℝ)|=(2702384153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2654829203/5000000000 : ℝ)*x 0 + (5404768191/10000000000 : ℝ)*x 1 + (-42472229/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654829203/5000000000 : ℝ)^4135 ≤ (10777325203579/25000000000000 : ℝ)^3111 := by
    have hnat : (2654829203 : ℕ)^4135*25000000000000^3111 ≤ 10777325203579^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654829203 5000000000 10777325203579 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404768191/10000000000 : ℝ)^4135 ≤ (44138687257747/100000000000000 : ℝ)^3111 := by
    have hnat : (5404768191 : ℕ)^4135*100000000000000^3111 ≤ 44138687257747^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404768191 10000000000 44138687257747 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42472229/200000000 : ℝ)^4135 ≤ (1594001489021/12500000000000 : ℝ)^3111 := by
    have hnat : (42472229 : ℕ)^4135*12500000000000^3111 ≤ 1594001489021^3111*200000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42472229 200000000 1594001489021 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654829203/5000000000 : ℝ), (5404768191/10000000000 : ℝ), (-42472229/200000000 : ℝ)] ![(10777325203579/25000000000000 : ℝ), (44138687257747/100000000000000 : ℝ), (1594001489021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654829203/5000000000 : ℝ)|^4135 ≤ (10777325203579/25000000000000 : ℝ)^3111
        have hw : |(2654829203/5000000000 : ℝ)|=(2654829203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404768191/10000000000 : ℝ)|^4135 ≤ (44138687257747/100000000000000 : ℝ)^3111
        have hw : |(5404768191/10000000000 : ℝ)|=(5404768191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42472229/200000000 : ℝ)|^4135 ≤ (1594001489021/12500000000000 : ℝ)^3111
        have hw : |(-42472229/200000000 : ℝ)|=(42472229/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s4_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17493349/40000000 : ℝ)*x 0 + (2261611299/5000000000 : ℝ)*x 1 + (4228498429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17493349/40000000 : ℝ)^4135 ≤ (33310787601631/100000000000000 : ℝ)^3111 := by
    have hnat : (17493349 : ℕ)^4135*100000000000000^3111 ≤ 33310787601631^3111*40000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17493349 40000000 33310787601631 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261611299/5000000000 : ℝ)^4135 ≤ (34836704759421/100000000000000 : ℝ)^3111 := by
    have hnat : (2261611299 : ℕ)^4135*100000000000000^3111 ≤ 34836704759421^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261611299 5000000000 34836704759421 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228498429/10000000000 : ℝ)^4135 ≤ (15926253811913/50000000000000 : ℝ)^3111 := by
    have hnat : (4228498429 : ℕ)^4135*50000000000000^3111 ≤ 15926253811913^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228498429 10000000000 15926253811913 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17493349/40000000 : ℝ), (2261611299/5000000000 : ℝ), (4228498429/10000000000 : ℝ)] ![(33310787601631/100000000000000 : ℝ), (34836704759421/100000000000000 : ℝ), (15926253811913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17493349/40000000 : ℝ)|^4135 ≤ (33310787601631/100000000000000 : ℝ)^3111
        have hw : |(17493349/40000000 : ℝ)|=(17493349/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261611299/5000000000 : ℝ)|^4135 ≤ (34836704759421/100000000000000 : ℝ)^3111
        have hw : |(2261611299/5000000000 : ℝ)|=(2261611299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228498429/10000000000 : ℝ)|^4135 ≤ (15926253811913/50000000000000 : ℝ)^3111
        have hw : |(4228498429/10000000000 : ℝ)|=(4228498429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1489/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (326/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2209/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1489/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (326/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1489/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (326/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1489/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (326/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1489/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (326/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1489/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (326/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1489/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (326/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (326/3125 : ℝ) ^ (8269/2048 : ℝ) ≤ (2719588799422723/25000000000000000000 : ℝ) := by
    have hpowers : (326/3125 : ℝ)^8269 ≤ (2719588799422723/25000000000000000000 : ℝ)^2048 := by
      have hnat : (326 : ℕ)^8269*25000000000000000000^2048 ≤ 2719588799422723^2048*3125^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        326 3125 2719588799422723 25000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (326/3125 : ℝ)) (X := (2719588799422723/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1489/10000 : ℝ) ^ (8269/2048 : ℝ) ≤ (11439882896165063/25000000000000000000 : ℝ) := by
    have hpowers : (1489/10000 : ℝ)^8269 ≤ (11439882896165063/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1489 : ℕ)^8269*25000000000000000000^2048 ≤ 11439882896165063^2048*10000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1489 10000 11439882896165063 25000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1489/10000 : ℝ)) (X := (11439882896165063/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502719588799422723/12500000000000000000 : ℝ) ≤ (10000538808764143/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (12502719588799422723/12500000000000000000 : ℝ)^2048 ≤ (10000538808764143/10000000000000000 : ℝ)^8269 := by
      have hnat : (12502719588799422723 : ℕ)^2048*10000000000000000^8269 ≤ 10000538808764143^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502719588799422723 12500000000000000000 10000538808764143 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538808764143/10000000000000000 : ℝ)) (X := (12502719588799422723/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507079735847793893/12500000000000000000 : ℝ) ≤ (1250175307908367/1250000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (12507079735847793893/12500000000000000000 : ℝ)^2048 ≤ (1250175307908367/1250000000000000 : ℝ)^8269 := by
      have hnat : (12507079735847793893 : ℕ)^2048*1250000000000000^8269 ≤ 1250175307908367^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507079735847793893 12500000000000000000 1250175307908367 1250000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250175307908367/1250000000000000 : ℝ)) (X := (12507079735847793893/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511439882896165063/12500000000000000000 : ℝ) ≤ (10002266117769729/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (12511439882896165063/12500000000000000000 : ℝ)^2048 ≤ (10002266117769729/10000000000000000 : ℝ)^8269 := by
      have hnat : (12511439882896165063 : ℕ)^2048*10000000000000000^8269 ≤ 10002266117769729^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511439882896165063 12500000000000000000 10002266117769729 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002266117769729/10000000000000000 : ℝ)) (X := (12511439882896165063/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2719588799422723/25000000000000000000 : ℝ) ≤ ((22282191360962138171/22290000000000000000 : ℝ)+2*(863654502793/445800000000000 : ℝ)*(326/3125 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (22282191360962138171/22290000000000000000 : ℝ)+2*(863654502793/445800000000000 : ℝ)*(326/3125 : ℝ)=(10000538808764143/10000000000000000 : ℝ) by norm_num, show 1+2*(2719588799422723/25000000000000000000 : ℝ)=(12502719588799422723/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11439882896165063/25000000000000000000 : ℝ)+(2719588799422723/25000000000000000000 : ℝ) ≤ ((22282191360962138171/22290000000000000000 : ℝ)+(863654502793/445800000000000 : ℝ)*((1489/10000 : ℝ)+(326/3125 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (22282191360962138171/22290000000000000000 : ℝ)+(863654502793/445800000000000 : ℝ)*((1489/10000 : ℝ)+(326/3125 : ℝ))=(1250175307908367/1250000000000000 : ℝ) by norm_num, show 1+(11439882896165063/25000000000000000000 : ℝ)+(2719588799422723/25000000000000000000 : ℝ)=(12507079735847793893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11439882896165063/25000000000000000000 : ℝ) ≤ ((22282191360962138171/22290000000000000000 : ℝ)+2*(863654502793/445800000000000 : ℝ)*(1489/10000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (22282191360962138171/22290000000000000000 : ℝ)+2*(863654502793/445800000000000 : ℝ)*(1489/10000 : ℝ)=(10002266117769729/10000000000000000 : ℝ) by norm_num, show 1+2*(11439882896165063/25000000000000000000 : ℝ)=(12511439882896165063/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22282191360962138171/22290000000000000000 : ℝ)*(X 1 0+X 2 0)+(863654502793/445800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (326/3125 : ℝ)) (hi := (1489/10000 : ℝ)) (c := (22282191360962138171/22290000000000000000 : ℝ)) (alpha := (863654502793/445800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22282191360962138171/22290000000000000000 : ℝ)*(X 0 1+X 2 1)+(863654502793/445800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (326/3125 : ℝ)) (hi := (1489/10000 : ℝ)) (c := (22282191360962138171/22290000000000000000 : ℝ)) (alpha := (863654502793/445800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22282191360962138171/22290000000000000000 : ℝ)*(X 0 2+X 1 2)+(863654502793/445800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (326/3125 : ℝ)) (hi := (1489/10000 : ℝ)) (c := (22282191360962138171/22290000000000000000 : ℝ)) (alpha := (863654502793/445800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2197345607/10000000000 : ℝ)*X 0 0+(337825649/625000000 : ℝ)*X 0 1+(2627137501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347706693/10000000000 : ℝ)*X 1 0+(-284263093/1250000000 : ℝ)*X 1 1+(5254275459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347706737/10000000000 : ℝ)*X 2 0+(164196103/312500000 : ℝ)*X 2 1+(-1137052451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373321291/10000000000 : ℝ)*X 0 0+(4227629769/10000000000 : ℝ)*X 0 1+(1131021983/2500000000 : ℝ)*X 0 2+(4373321291/10000000000 : ℝ)*X 1 0+(4227629769/10000000000 : ℝ)*X 1 1+(1131021983/2500000000 : ℝ)*X 1 2+(4373321291/10000000000 : ℝ)*X 2 0+(4227629769/10000000000 : ℝ)*X 2 1+(1131021983/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098676539/5000000000 : ℝ)*X 0 0+(5254715677/10000000000 : ℝ)*X 0 1+(540476823/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309658533/10000000000 : ℝ)*X 1 0+(-1061805561/5000000000 : ℝ)*X 1 1+(2702384153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654829203/5000000000 : ℝ)*X 2 0+(5404768191/10000000000 : ℝ)*X 2 1+(-42472229/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17493349/40000000 : ℝ)*X 0 0+(2261611299/5000000000 : ℝ)*X 0 1+(4228498429/10000000000 : ℝ)*X 0 2+(17493349/40000000 : ℝ)*X 1 0+(2261611299/5000000000 : ℝ)*X 1 1+(4228498429/10000000000 : ℝ)*X 1 2+(17493349/40000000 : ℝ)*X 2 0+(2261611299/5000000000 : ℝ)*X 2 1+(4228498429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (475314949316295955667302563/46437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1865311013/100000000000000 : ℝ)*(base19) + (351021549/25000000000000 : ℝ)*(base23) + (77091621/12500000000000 : ℝ)*(upper3) + (137900727/50000000000000 : ℝ)*(upper4) + (4335507/12500000000000 : ℝ)*(upper5) + (1249830763602053/25000000000000 : ℝ)*(major0) + (1249830763602053/25000000000000 : ℝ)*(major1) + (1249830763602053/25000000000000 : ℝ)*(major2) + (3312703206059907/50000000000000 : ℝ)*(sp0) + (3312721253496497/50000000000000 : ℝ)*(sp1) + (6625442968217811/100000000000000 : ℝ)*(sp2) + (337317295421403/10000000000000 : ℝ)*(sp3) + (296563939/781250000000 : ℝ)*(sp4) + (3555139029/12500000000000 : ℝ)*(sp7) + (3373201395326263/100000000000000 : ℝ)*(f.failure) + (6625444372304007/100000000000000 : ℝ)*(f.sum) + (25664662963469/5572500000000000000000000000 : ℝ)*base65 + (7390078538606784937/557250000000000000000000000000000 : ℝ)*base68 + (812675632204284937/557250000000000000000000000000000 : ℝ)*base70 + (6843449281150284937/557250000000000000000000000000000 : ℝ)*base72 + (3368206617773/2786250000000000000000000000 : ℝ)*base74 + (734785711424784937/557250000000000000000000000000000 : ℝ)*base76 + (2079064239921534937/557250000000000000000000000000000 : ℝ)*base78 + (3816458302497215063/557250000000000000000000000000000 : ℝ)*base79 + (15962668561747/2786250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (119258199/10000000000000000000000 : ℝ)*base89 + (119258199/10000000000000000000000 : ℝ)*base91 + (119258199/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (338856683190345115462171347/185750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9081847/781250000000 : ℝ)*(base19) + (542404087/50000000000000 : ℝ)*(base23) + (48240369/50000000000000 : ℝ)*(lower4) + (73371589/100000000000000 : ℝ)*(upper5) + (2514332766311219/50000000000000 : ℝ)*(major0) + (2514332766311219/50000000000000 : ℝ)*(major1) + (2514332766311219/50000000000000 : ℝ)*(major2) + (141073889/25000000000000 : ℝ)*(sp0) + (7885106053/20000000000000 : ℝ)*(sp1) + (25473905847/100000000000000 : ℝ)*(sp2) + (6664330746649267/100000000000000 : ℝ)*(sp4) + (3332145361469071/50000000000000 : ℝ)*(sp5) + (6664304752230801/100000000000000 : ℝ)*(sp6) + (848249923372827/25000000000000 : ℝ)*(sp7) + (848249923372827/25000000000000 : ℝ)*(f.failure) + (6664331310944823/100000000000000 : ℝ)*(f.sum) + (10588444236223/11145000000000000000000000000 : ℝ)*base66 + (15996236879782709551/1114500000000000000000000000000000 : ℝ)*base68 + (7977123183984209551/1114500000000000000000000000000000 : ℝ)*base70 + (7325161499500709551/1114500000000000000000000000000000 : ℝ)*base72 + (64846528391833/11145000000000000000000000000 : ℝ)*base74 + (25437454781176709551/1114500000000000000000000000000000 : ℝ)*base76 + (4841303339053709551/1114500000000000000000000000000000 : ℝ)*base78 + (1057026883162709551/1114500000000000000000000000000000 : ℝ)*base80 + (31041915478093/11145000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (27405371/2500000000000000000000 : ℝ)*base89 + (27405371/2500000000000000000000 : ℝ)*base91 + (27405371/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1077_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1489/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (326/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2209/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1077_s5_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2198144803/10000000000 : ℝ)*x 0 + (5396682637/10000000000 : ℝ)*x 1 + (1052455701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198144803/10000000000 : ℝ)^4135 ≤ (267006042353/2000000000000 : ℝ)^3111 := by
    have hnat : (2198144803 : ℕ)^4135*2000000000000^3111 ≤ 267006042353^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198144803 10000000000 267006042353 2000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396682637/10000000000 : ℝ)^4135 ≤ (11012735651761/25000000000000 : ℝ)^3111 := by
    have hnat : (5396682637 : ℕ)^4135*25000000000000^3111 ≤ 11012735651761^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396682637 10000000000 11012735651761 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052455701/2000000000 : ℝ)^4135 ≤ (21299377626481/50000000000000 : ℝ)^3111 := by
    have hnat : (1052455701 : ℕ)^4135*50000000000000^3111 ≤ 21299377626481^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052455701 2000000000 21299377626481 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2198144803/10000000000 : ℝ), (5396682637/10000000000 : ℝ), (1052455701/2000000000 : ℝ)] ![(267006042353/2000000000000 : ℝ), (11012735651761/25000000000000 : ℝ), (21299377626481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2198144803/10000000000 : ℝ)|^4135 ≤ (267006042353/2000000000000 : ℝ)^3111
        have hw : |(-2198144803/10000000000 : ℝ)|=(2198144803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396682637/10000000000 : ℝ)|^4135 ≤ (11012735651761/25000000000000 : ℝ)^3111
        have hw : |(5396682637/10000000000 : ℝ)|=(5396682637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052455701/2000000000 : ℝ)|^4135 ≤ (21299377626481/50000000000000 : ℝ)^3111
        have hw : |(1052455701/2000000000 : ℝ)|=(1052455701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334098817/625000000 : ℝ)*x 0 + (-1133186137/5000000000 : ℝ)*x 1 + (2631138777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334098817/625000000 : ℝ)^4135 ≤ (10874347385649/25000000000000 : ℝ)^3111 := by
    have hnat : (334098817 : ℕ)^4135*25000000000000^3111 ≤ 10874347385649^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334098817 625000000 10874347385649 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133186137/5000000000 : ℝ)^4135 ≤ (868991588563/6250000000000 : ℝ)^3111 := by
    have hnat : (1133186137 : ℕ)^4135*6250000000000^3111 ≤ 868991588563^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133186137 5000000000 868991588563 6250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631138777/5000000000 : ℝ)^4135 ≤ (1703949800821/4000000000000 : ℝ)^3111 := by
    have hnat : (2631138777 : ℕ)^4135*4000000000000^3111 ≤ 1703949800821^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631138777 5000000000 1703949800821 4000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334098817/625000000 : ℝ), (-1133186137/5000000000 : ℝ), (2631138777/5000000000 : ℝ)] ![(10874347385649/25000000000000 : ℝ), (868991588563/6250000000000 : ℝ), (1703949800821/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334098817/625000000 : ℝ)|^4135 ≤ (10874347385649/25000000000000 : ℝ)^3111
        have hw : |(334098817/625000000 : ℝ)|=(334098817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133186137/5000000000 : ℝ)|^4135 ≤ (868991588563/6250000000000 : ℝ)^3111
        have hw : |(-1133186137/5000000000 : ℝ)|=(1133186137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631138777/5000000000 : ℝ)|^4135 ≤ (1703949800821/4000000000000 : ℝ)^3111
        have hw : |(2631138777/5000000000 : ℝ)|=(2631138777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167049401/312500000 : ℝ)*x 0 + (210491137/400000000 : ℝ)*x 1 + (-2266371443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167049401/312500000 : ℝ)^4135 ≤ (43497386946893/100000000000000 : ℝ)^3111 := by
    have hnat : (167049401 : ℕ)^4135*100000000000000^3111 ≤ 43497386946893^3111*312500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167049401 312500000 43497386946893 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210491137/400000000 : ℝ)^4135 ≤ (42598754392189/100000000000000 : ℝ)^3111 := by
    have hnat : (210491137 : ℕ)^4135*100000000000000^3111 ≤ 42598754392189^3111*400000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210491137 400000000 42598754392189 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266371443/10000000000 : ℝ)^4135 ≤ (13903858640893/100000000000000 : ℝ)^3111 := by
    have hnat : (2266371443 : ℕ)^4135*100000000000000^3111 ≤ 13903858640893^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266371443 10000000000 13903858640893 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167049401/312500000 : ℝ), (210491137/400000000 : ℝ), (-2266371443/10000000000 : ℝ)] ![(43497386946893/100000000000000 : ℝ), (42598754392189/100000000000000 : ℝ), (13903858640893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167049401/312500000 : ℝ)|^4135 ≤ (43497386946893/100000000000000 : ℝ)^3111
        have hw : |(167049401/312500000 : ℝ)|=(167049401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210491137/400000000 : ℝ)|^4135 ≤ (42598754392189/100000000000000 : ℝ)^3111
        have hw : |(210491137/400000000 : ℝ)|=(210491137/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266371443/10000000000 : ℝ)|^4135 ≤ (13903858640893/100000000000000 : ℝ)^3111
        have hw : |(-2266371443/10000000000 : ℝ)|=(2266371443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874757079/2000000000 : ℝ)*x 0 + (4243803089/10000000000 : ℝ)*x 1 + (4507792837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874757079/2000000000 : ℝ)^4135 ≤ (16657662324503/50000000000000 : ℝ)^3111 := by
    have hnat : (874757079 : ℕ)^4135*50000000000000^3111 ≤ 16657662324503^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874757079 2000000000 16657662324503 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243803089/10000000000 : ℝ)^4135 ≤ (16002916679333/50000000000000 : ℝ)^3111 := by
    have hnat : (4243803089 : ℕ)^4135*50000000000000^3111 ≤ 16002916679333^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243803089 10000000000 16002916679333 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507792837/10000000000 : ℝ)^4135 ≤ (34678841983181/100000000000000 : ℝ)^3111 := by
    have hnat : (4507792837 : ℕ)^4135*100000000000000^3111 ≤ 34678841983181^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507792837 10000000000 34678841983181 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874757079/2000000000 : ℝ), (4243803089/10000000000 : ℝ), (4507792837/10000000000 : ℝ)] ![(16657662324503/50000000000000 : ℝ), (16002916679333/50000000000000 : ℝ), (34678841983181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874757079/2000000000 : ℝ)|^4135 ≤ (16657662324503/50000000000000 : ℝ)^3111
        have hw : |(874757079/2000000000 : ℝ)|=(874757079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243803089/10000000000 : ℝ)|^4135 ≤ (16002916679333/50000000000000 : ℝ)^3111
        have hw : |(4243803089/10000000000 : ℝ)|=(4243803089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507792837/10000000000 : ℝ)|^4135 ≤ (34678841983181/100000000000000 : ℝ)^3111
        have hw : |(4507792837/10000000000 : ℝ)|=(4507792837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2198150309/10000000000 : ℝ)*x 0 + (5262627751/10000000000 : ℝ)*x 1 + (2698166087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198150309/10000000000 : ℝ)^4135 ≤ (3337586641271/25000000000000 : ℝ)^3111 := by
    have hnat : (2198150309 : ℕ)^4135*25000000000000^3111 ≤ 3337586641271^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198150309 10000000000 3337586641271 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262627751/10000000000 : ℝ)^4135 ≤ (42602513062521/100000000000000 : ℝ)^3111 := by
    have hnat : (5262627751 : ℕ)^4135*100000000000000^3111 ≤ 42602513062521^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262627751 10000000000 42602513062521 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698166087/5000000000 : ℝ)^4135 ≤ (44047140350973/100000000000000 : ℝ)^3111 := by
    have hnat : (2698166087 : ℕ)^4135*100000000000000^3111 ≤ 44047140350973^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698166087 5000000000 44047140350973 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2198150309/10000000000 : ℝ), (5262627751/10000000000 : ℝ), (2698166087/5000000000 : ℝ)] ![(3337586641271/25000000000000 : ℝ), (42602513062521/100000000000000 : ℝ), (44047140350973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2198150309/10000000000 : ℝ)|^4135 ≤ (3337586641271/25000000000000 : ℝ)^3111
        have hw : |(-2198150309/10000000000 : ℝ)|=(2198150309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262627751/10000000000 : ℝ)|^4135 ≤ (42602513062521/100000000000000 : ℝ)^3111
        have hw : |(5262627751/10000000000 : ℝ)|=(5262627751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698166087/5000000000 : ℝ)|^4135 ≤ (44047140350973/100000000000000 : ℝ)^3111
        have hw : |(2698166087/5000000000 : ℝ)|=(2698166087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062339661/2000000000 : ℝ)*x 0 + (-213231747/1000000000 : ℝ)*x 1 + (2698166039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062339661/2000000000 : ℝ)^4135 ≤ (43131315679061/100000000000000 : ℝ)^3111 := by
    have hnat : (1062339661 : ℕ)^4135*100000000000000^3111 ≤ 43131315679061^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062339661 2000000000 43131315679061 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213231747/1000000000 : ℝ)^4135 ≤ (80134656203/625000000000 : ℝ)^3111 := by
    have hnat : (213231747 : ℕ)^4135*625000000000^3111 ≤ 80134656203^3111*1000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213231747 1000000000 80134656203 625000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698166039/5000000000 : ℝ)^4135 ≤ (44047139309457/100000000000000 : ℝ)^3111 := by
    have hnat : (2698166039 : ℕ)^4135*100000000000000^3111 ≤ 44047139309457^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698166039 5000000000 44047139309457 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062339661/2000000000 : ℝ), (-213231747/1000000000 : ℝ), (2698166039/5000000000 : ℝ)] ![(43131315679061/100000000000000 : ℝ), (80134656203/625000000000 : ℝ), (44047139309457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062339661/2000000000 : ℝ)|^4135 ≤ (43131315679061/100000000000000 : ℝ)^3111
        have hw : |(1062339661/2000000000 : ℝ)|=(1062339661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213231747/1000000000 : ℝ)|^4135 ≤ (80134656203/625000000000 : ℝ)^3111
        have hw : |(-213231747/1000000000 : ℝ)|=(213231747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698166039/5000000000 : ℝ)|^4135 ≤ (44047139309457/100000000000000 : ℝ)^3111
        have hw : |(2698166039/5000000000 : ℝ)|=(2698166039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311698027/10000000000 : ℝ)*x 0 + (5396332369/10000000000 : ℝ)*x 1 + (-2132317451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311698027/10000000000 : ℝ)^4135 ≤ (21565656339329/50000000000000 : ℝ)^3111 := by
    have hnat : (5311698027 : ℕ)^4135*50000000000000^3111 ≤ 21565656339329^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311698027 10000000000 21565656339329 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396332369/10000000000 : ℝ)^4135 ≤ (5505892808319/12500000000000 : ℝ)^3111 := by
    have hnat : (5396332369 : ℕ)^4135*12500000000000^3111 ≤ 5505892808319^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396332369 10000000000 5505892808319 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132317451/10000000000 : ℝ)^4135 ≤ (12821544840629/100000000000000 : ℝ)^3111 := by
    have hnat : (2132317451 : ℕ)^4135*100000000000000^3111 ≤ 12821544840629^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132317451 10000000000 12821544840629 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311698027/10000000000 : ℝ), (5396332369/10000000000 : ℝ), (-2132317451/10000000000 : ℝ)] ![(21565656339329/50000000000000 : ℝ), (5505892808319/12500000000000 : ℝ), (12821544840629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311698027/10000000000 : ℝ)|^4135 ≤ (21565656339329/50000000000000 : ℝ)^3111
        have hw : |(5311698027/10000000000 : ℝ)|=(5311698027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396332369/10000000000 : ℝ)|^4135 ≤ (5505892808319/12500000000000 : ℝ)^3111
        have hw : |(5396332369/10000000000 : ℝ)|=(5396332369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132317451/10000000000 : ℝ)|^4135 ≤ (12821544840629/100000000000000 : ℝ)^3111
        have hw : |(-2132317451/10000000000 : ℝ)|=(2132317451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s5_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093449159/2500000000 : ℝ)*x 0 + (4507106581/10000000000 : ℝ)*x 1 + (4244491723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093449159/2500000000 : ℝ)^4135 ≤ (4164429806943/12500000000000 : ℝ)^3111 := by
    have hnat : (1093449159 : ℕ)^4135*12500000000000^3111 ≤ 4164429806943^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093449159 2500000000 4164429806943 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507106581/10000000000 : ℝ)^4135 ≤ (17335912492101/50000000000000 : ℝ)^3111 := by
    have hnat : (4507106581 : ℕ)^4135*50000000000000^3111 ≤ 17335912492101^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507106581 10000000000 17335912492101 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244491723/10000000000 : ℝ)^4135 ≤ (16006368271551/50000000000000 : ℝ)^3111 := by
    have hnat : (4244491723 : ℕ)^4135*50000000000000^3111 ≤ 16006368271551^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244491723 10000000000 16006368271551 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093449159/2500000000 : ℝ), (4507106581/10000000000 : ℝ), (4244491723/10000000000 : ℝ)] ![(4164429806943/12500000000000 : ℝ), (17335912492101/50000000000000 : ℝ), (16006368271551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093449159/2500000000 : ℝ)|^4135 ≤ (4164429806943/12500000000000 : ℝ)^3111
        have hw : |(1093449159/2500000000 : ℝ)|=(1093449159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507106581/10000000000 : ℝ)|^4135 ≤ (17335912492101/50000000000000 : ℝ)^3111
        have hw : |(4507106581/10000000000 : ℝ)|=(4507106581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244491723/10000000000 : ℝ)|^4135 ≤ (16006368271551/50000000000000 : ℝ)^3111
        have hw : |(4244491723/10000000000 : ℝ)|=(4244491723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2209/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2209/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2209/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2209/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2209/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2209/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2209/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2209/20000 : ℝ) ^ (8269/2048 : ℝ) ≤ (3424744391778649/25000000000000000000 : ℝ) := by
    have hpowers : (2209/20000 : ℝ)^8269 ≤ (3424744391778649/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2209 : ℕ)^8269*25000000000000000000^2048 ≤ 3424744391778649^2048*20000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2209 20000 3424744391778649 25000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2209/20000 : ℝ)) (X := (3424744391778649/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14241/100000 : ℝ) ^ (8269/2048 : ℝ) ≤ (19112040465622349/50000000000000000000 : ℝ) := by
    have hpowers : (14241/100000 : ℝ)^8269 ≤ (19112040465622349/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14241 : ℕ)^8269*50000000000000000000^2048 ≤ 19112040465622349^2048*100000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14241 100000 19112040465622349 50000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14241/100000 : ℝ)) (X := (19112040465622349/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503424744391778649/12500000000000000000 : ℝ) ≤ (10000678500788121/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (12503424744391778649/12500000000000000000 : ℝ)^2048 ≤ (10000678500788121/10000000000000000 : ℝ)^8269 := by
      have hnat : (12503424744391778649 : ℕ)^2048*10000000000000000^8269 ≤ 10000678500788121^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503424744391778649 12500000000000000000 10000678500788121 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678500788121/10000000000000000 : ℝ)) (X := (12503424744391778649/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025961529249179647/50000000000000000000 : ℝ) ≤ (625080358613891/625000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (50025961529249179647/50000000000000000000 : ℝ)^2048 ≤ (625080358613891/625000000000000 : ℝ)^8269 := by
      have hnat : (50025961529249179647 : ℕ)^2048*625000000000000^8269 ≤ 625080358613891^8269*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025961529249179647 50000000000000000000 625080358613891 625000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625080358613891/625000000000000 : ℝ)) (X := (50025961529249179647/50000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019112040465622349/25000000000000000000 : ℝ) ≤ (10001892974856391/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (25019112040465622349/25000000000000000000 : ℝ)^2048 ≤ (10001892974856391/10000000000000000 : ℝ)^8269 := by
      have hnat : (25019112040465622349 : ℕ)^2048*10000000000000000^8269 ≤ 10001892974856391^8269*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019112040465622349 25000000000000000000 10001892974856391 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001892974856391/10000000000000000 : ℝ)) (X := (25019112040465622349/25000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3424744391778649/25000000000000000000 : ℝ) ≤ ((339880368323774389/340000000000000000 : ℝ)+2*(121447406827/63920000000000 : ℝ)*(2209/20000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (339880368323774389/340000000000000000 : ℝ)+2*(121447406827/63920000000000 : ℝ)*(2209/20000 : ℝ)=(10000678500788121/10000000000000000 : ℝ) by norm_num, show 1+2*(3424744391778649/25000000000000000000 : ℝ)=(12503424744391778649/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19112040465622349/50000000000000000000 : ℝ)+(3424744391778649/25000000000000000000 : ℝ) ≤ ((339880368323774389/340000000000000000 : ℝ)+(121447406827/63920000000000 : ℝ)*((14241/100000 : ℝ)+(2209/20000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (339880368323774389/340000000000000000 : ℝ)+(121447406827/63920000000000 : ℝ)*((14241/100000 : ℝ)+(2209/20000 : ℝ))=(625080358613891/625000000000000 : ℝ) by norm_num, show 1+(19112040465622349/50000000000000000000 : ℝ)+(3424744391778649/25000000000000000000 : ℝ)=(50025961529249179647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19112040465622349/50000000000000000000 : ℝ) ≤ ((339880368323774389/340000000000000000 : ℝ)+2*(121447406827/63920000000000 : ℝ)*(14241/100000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (339880368323774389/340000000000000000 : ℝ)+2*(121447406827/63920000000000 : ℝ)*(14241/100000 : ℝ)=(10001892974856391/10000000000000000 : ℝ) by norm_num, show 1+2*(19112040465622349/50000000000000000000 : ℝ)=(25019112040465622349/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (339880368323774389/340000000000000000 : ℝ)*(X 1 0+X 2 0)+(121447406827/63920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2209/20000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (339880368323774389/340000000000000000 : ℝ)) (alpha := (121447406827/63920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (339880368323774389/340000000000000000 : ℝ)*(X 0 1+X 2 1)+(121447406827/63920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2209/20000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (339880368323774389/340000000000000000 : ℝ)) (alpha := (121447406827/63920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (339880368323774389/340000000000000000 : ℝ)*(X 0 2+X 1 2)+(121447406827/63920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2209/20000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (339880368323774389/340000000000000000 : ℝ)) (alpha := (121447406827/63920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2198144803/10000000000 : ℝ)*X 0 0+(5396682637/10000000000 : ℝ)*X 0 1+(1052455701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334098817/625000000 : ℝ)*X 1 0+(-1133186137/5000000000 : ℝ)*X 1 1+(2631138777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167049401/312500000 : ℝ)*X 2 0+(210491137/400000000 : ℝ)*X 2 1+(-2266371443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874757079/2000000000 : ℝ)*X 0 0+(4243803089/10000000000 : ℝ)*X 0 1+(4507792837/10000000000 : ℝ)*X 0 2+(874757079/2000000000 : ℝ)*X 1 0+(4243803089/10000000000 : ℝ)*X 1 1+(4507792837/10000000000 : ℝ)*X 1 2+(874757079/2000000000 : ℝ)*X 2 0+(4243803089/10000000000 : ℝ)*X 2 1+(4507792837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2198150309/10000000000 : ℝ)*X 0 0+(5262627751/10000000000 : ℝ)*X 0 1+(2698166087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062339661/2000000000 : ℝ)*X 1 0+(-213231747/1000000000 : ℝ)*X 1 1+(2698166039/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311698027/10000000000 : ℝ)*X 2 0+(5396332369/10000000000 : ℝ)*X 2 1+(-2132317451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093449159/2500000000 : ℝ)*X 0 0+(4507106581/10000000000 : ℝ)*X 0 1+(4244491723/10000000000 : ℝ)*X 0 2+(1093449159/2500000000 : ℝ)*X 1 0+(4507106581/10000000000 : ℝ)*X 1 1+(4244491723/10000000000 : ℝ)*X 1 2+(1093449159/2500000000 : ℝ)*X 2 0+(4507106581/10000000000 : ℝ)*X 2 1+(4244491723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578950580523058644418216923/99875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1396498691/100000000000000 : ℝ)*(base19) + (216689023/20000000000000 : ℝ)*(base23) + (94017769/100000000000000 : ℝ)*(upper4) + (16595703/6250000000000 : ℝ)*(upper5) + (1403543874207027/25000000000000 : ℝ)*(major0) + (1403543874207027/25000000000000 : ℝ)*(major1) + (1403543874207027/25000000000000 : ℝ)*(major2) + (3720130690904711/50000000000000 : ℝ)*(sp0) + (1860064139459881/25000000000000 : ℝ)*(sp1) + (1488057586147819/20000000000000 : ℝ)*(sp2) + (3788046346372417/100000000000000 : ℝ)*(sp3) + (27632374787/100000000000000 : ℝ)*(sp4) + (6211969199/20000000000000 : ℝ)*(sp5) + (3859968631/25000000000000 : ℝ)*(sp7) + (1894030893123471/50000000000000 : ℝ)*(f.failure) + (7440289014184209/100000000000000 : ℝ)*(f.sum) + (387849987259/799000000000000000000000000 : ℝ)*base65 + (4310519666421469359/399500000000000000000000000000000 : ℝ)*base68 + (2461815247560969359/399500000000000000000000000000000 : ℝ)*base70 + (457829865634469359/399500000000000000000000000000000 : ℝ)*base72 + (103473342157/39950000000000000000000000 : ℝ)*base74 + (35252590331969359/399500000000000000000000000000000 : ℝ)*base76 + (1222712101015969359/399500000000000000000000000000000 : ℝ)*base78 + (294434726740530641/399500000000000000000000000000000 : ℝ)*base79 + (12825567427/31960000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (64510383/5000000000000000000000 : ℝ)*base89 + (64510383/5000000000000000000000 : ℝ)*base91 + (64510383/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135798258439559025378310101/15980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2259048641/100000000000000 : ℝ)*(base19) + (2087693127/100000000000000 : ℝ)*(base23) + (251715417/100000000000000 : ℝ)*(upper3) + (87440687/100000000000000 : ℝ)*(lower4) + (104394289/100000000000000 : ℝ)*(upper5) + (225740594623549/4000000000000 : ℝ)*(major0) + (225740594623549/4000000000000 : ℝ)*(major1) + (225740594623549/4000000000000 : ℝ)*(major2) + (26723287361/50000000000000 : ℝ)*(sp1) + (62141586629/100000000000000 : ℝ)*(sp2) + (7479171461545037/100000000000000 : ℝ)*(sp4) + (3739557877960837/50000000000000 : ℝ)*(sp5) + (7479107232265281/100000000000000 : ℝ)*(sp6) + (951964496591321/25000000000000 : ℝ)*(sp7) + (951964496591321/25000000000000 : ℝ)*(f.failure) + (7479171461545037/100000000000000 : ℝ)*(f.sum) + (9986489312861/3196000000000000000000000000 : ℝ)*base66 + (453297337568101633/63920000000000000000000000000000 : ℝ)*base68 + (328212863505781633/63920000000000000000000000000000 : ℝ)*base70 + (721291742065141633/63920000000000000000000000000000 : ℝ)*base72 + (9433623516041/3196000000000000000000000000 : ℝ)*base74 + (245943229064021633/63920000000000000000000000000000 : ℝ)*base76 + (799451287460261633/63920000000000000000000000000000 : ℝ)*base78 + (246125642962058367/63920000000000000000000000000000 : ℝ)*base79 + (6314834267409/3196000000000000000000000000 : ℝ)*base82 + (37613433/2500000000000000000000 : ℝ)*base89 + (37613433/2500000000000000000000 : ℝ)*base91 + (37613433/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1077_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2209/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1077_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1077_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1077_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1077_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

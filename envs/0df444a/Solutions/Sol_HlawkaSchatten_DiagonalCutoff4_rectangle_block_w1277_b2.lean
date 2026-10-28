-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:48.004905+00:00
-- url     : https://prove2.me/submissions/5da47318-5955-4aea-a0d7-1df3fc111359

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
theorem support_rectangle_w1277_s6_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050737691/5000000000 : ℝ)*x 0 + (5416110213/10000000000 : ℝ)*x 1 + (163823053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050737691/5000000000 : ℝ)^4237 ≤ (12782306878227/100000000000000 : ℝ)^3213 := by
    have hnat : (1050737691 : ℕ)^4237*100000000000000^3213 ≤ 12782306878227^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050737691 5000000000 12782306878227 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416110213/10000000000 : ℝ)^4237 ≤ (11136591900759/25000000000000 : ℝ)^3213 := by
    have hnat : (5416110213 : ℕ)^4237*25000000000000^3213 ≤ 11136591900759^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416110213 10000000000 11136591900759 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163823053/312500000 : ℝ)^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213 := by
    have hnat : (163823053 : ℕ)^4237*100000000000000^3213 ≤ 42671325507977^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163823053 312500000 42671325507977 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050737691/5000000000 : ℝ), (5416110213/10000000000 : ℝ), (163823053/312500000 : ℝ)] ![(12782306878227/100000000000000 : ℝ), (11136591900759/25000000000000 : ℝ), (42671325507977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050737691/5000000000 : ℝ)|^4237 ≤ (12782306878227/100000000000000 : ℝ)^3213
        have hw : |(-1050737691/5000000000 : ℝ)|=(1050737691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416110213/10000000000 : ℝ)|^4237 ≤ (11136591900759/25000000000000 : ℝ)^3213
        have hw : |(5416110213/10000000000 : ℝ)|=(5416110213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163823053/312500000 : ℝ)|^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213
        have hw : |(163823053/312500000 : ℝ)|=(163823053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350025847/10000000000 : ℝ)*x 0 + (-3504113/16000000 : ℝ)*x 1 + (163823053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350025847/10000000000 : ℝ)^4237 ≤ (5478876150947/12500000000000 : ℝ)^3213 := by
    have hnat : (5350025847 : ℕ)^4237*12500000000000^3213 ≤ 5478876150947^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350025847 10000000000 5478876150947 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3504113/16000000 : ℝ)^4237 ≤ (3374416317959/25000000000000 : ℝ)^3213 := by
    have hnat : (3504113 : ℕ)^4237*25000000000000^3213 ≤ 3374416317959^3213*16000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3504113 16000000 3374416317959 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163823053/312500000 : ℝ)^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213 := by
    have hnat : (163823053 : ℕ)^4237*100000000000000^3213 ≤ 42671325507977^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163823053 312500000 42671325507977 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350025847/10000000000 : ℝ), (-3504113/16000000 : ℝ), (163823053/312500000 : ℝ)] ![(5478876150947/12500000000000 : ℝ), (3374416317959/25000000000000 : ℝ), (42671325507977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350025847/10000000000 : ℝ)|^4237 ≤ (5478876150947/12500000000000 : ℝ)^3213
        have hw : |(5350025847/10000000000 : ℝ)|=(5350025847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3504113/16000000 : ℝ)|^4237 ≤ (3374416317959/25000000000000 : ℝ)^3213
        have hw : |(-3504113/16000000 : ℝ)|=(3504113/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163823053/312500000 : ℝ)|^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213
        have hw : |(163823053/312500000 : ℝ)|=(163823053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350025847/10000000000 : ℝ)*x 0 + (163823053/312500000 : ℝ)*x 1 + (-3504113/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350025847/10000000000 : ℝ)^4237 ≤ (5478876150947/12500000000000 : ℝ)^3213 := by
    have hnat : (5350025847 : ℕ)^4237*12500000000000^3213 ≤ 5478876150947^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350025847 10000000000 5478876150947 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163823053/312500000 : ℝ)^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213 := by
    have hnat : (163823053 : ℕ)^4237*100000000000000^3213 ≤ 42671325507977^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163823053 312500000 42671325507977 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3504113/16000000 : ℝ)^4237 ≤ (3374416317959/25000000000000 : ℝ)^3213 := by
    have hnat : (3504113 : ℕ)^4237*25000000000000^3213 ≤ 3374416317959^3213*16000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3504113 16000000 3374416317959 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350025847/10000000000 : ℝ), (163823053/312500000 : ℝ), (-3504113/16000000 : ℝ)] ![(5478876150947/12500000000000 : ℝ), (42671325507977/100000000000000 : ℝ), (3374416317959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350025847/10000000000 : ℝ)|^4237 ≤ (5478876150947/12500000000000 : ℝ)^3213
        have hw : |(5350025847/10000000000 : ℝ)|=(5350025847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163823053/312500000 : ℝ)|^4237 ≤ (42671325507977/100000000000000 : ℝ)^3213
        have hw : |(163823053/312500000 : ℝ)|=(163823053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3504113/16000000 : ℝ)|^4237 ≤ (3374416317959/25000000000000 : ℝ)^3213
        have hw : |(-3504113/16000000 : ℝ)|=(3504113/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085975253/2500000000 : ℝ)*x 0 + (833968869/2000000000 : ℝ)*x 1 + (180997687/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085975253/2500000000 : ℝ)^4237 ≤ (3330200225557/10000000000000 : ℝ)^3213 := by
    have hnat : (1085975253 : ℕ)^4237*10000000000000^3213 ≤ 3330200225557^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085975253 2500000000 3330200225557 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833968869/2000000000 : ℝ)^4237 ≤ (15776840828441/50000000000000 : ℝ)^3213 := by
    have hnat : (833968869 : ℕ)^4237*50000000000000^3213 ≤ 15776840828441^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833968869 2000000000 15776840828441 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180997687/400000000 : ℝ)^4237 ≤ (17572158032889/50000000000000 : ℝ)^3213 := by
    have hnat : (180997687 : ℕ)^4237*50000000000000^3213 ≤ 17572158032889^3213*400000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180997687 400000000 17572158032889 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085975253/2500000000 : ℝ), (833968869/2000000000 : ℝ), (180997687/400000000 : ℝ)] ![(3330200225557/10000000000000 : ℝ), (15776840828441/50000000000000 : ℝ), (17572158032889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085975253/2500000000 : ℝ)|^4237 ≤ (3330200225557/10000000000000 : ℝ)^3213
        have hw : |(1085975253/2500000000 : ℝ)|=(1085975253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833968869/2000000000 : ℝ)|^4237 ≤ (15776840828441/50000000000000 : ℝ)^3213
        have hw : |(833968869/2000000000 : ℝ)|=(833968869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180997687/400000000 : ℝ)|^4237 ≤ (17572158032889/50000000000000 : ℝ)^3213
        have hw : |(180997687/400000000 : ℝ)|=(180997687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-420297663/2000000000 : ℝ)*x 0 + (5242957091/10000000000 : ℝ)*x 1 + (2707743817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420297663/2000000000 : ℝ)^4237 ≤ (2556482122983/20000000000000 : ℝ)^3213 := by
    have hnat : (420297663 : ℕ)^4237*20000000000000^3213 ≤ 2556482122983^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420297663 2000000000 2556482122983 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242957091/10000000000 : ℝ)^4237 ≤ (42677974177559/100000000000000 : ℝ)^3213 := by
    have hnat : (5242957091 : ℕ)^4237*100000000000000^3213 ≤ 42677974177559^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242957091 10000000000 42677974177559 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707743817/5000000000 : ℝ)^4237 ≤ (44539615189157/100000000000000 : ℝ)^3213 := by
    have hnat : (2707743817 : ℕ)^4237*100000000000000^3213 ≤ 44539615189157^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707743817 5000000000 44539615189157 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420297663/2000000000 : ℝ), (5242957091/10000000000 : ℝ), (2707743817/5000000000 : ℝ)] ![(2556482122983/20000000000000 : ℝ), (42677974177559/100000000000000 : ℝ), (44539615189157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420297663/2000000000 : ℝ)|^4237 ≤ (2556482122983/20000000000000 : ℝ)^3213
        have hw : |(-420297663/2000000000 : ℝ)|=(420297663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242957091/10000000000 : ℝ)|^4237 ≤ (42677974177559/100000000000000 : ℝ)^3213
        have hw : |(5242957091/10000000000 : ℝ)|=(5242957091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707743817/5000000000 : ℝ)|^4237 ≤ (44539615189157/100000000000000 : ℝ)^3213
        have hw : |(2707743817/5000000000 : ℝ)|=(2707743817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652810559/5000000000 : ℝ)*x 0 + (-126057543/625000000 : ℝ)*x 1 + (2707743817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652810559/5000000000 : ℝ)^4237 ≤ (1734076345783/4000000000000 : ℝ)^3213 := by
    have hnat : (2652810559 : ℕ)^4237*4000000000000^3213 ≤ 1734076345783^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652810559 5000000000 1734076345783 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126057543/625000000 : ℝ)^4237 ≤ (2421695229193/20000000000000 : ℝ)^3213 := by
    have hnat : (126057543 : ℕ)^4237*20000000000000^3213 ≤ 2421695229193^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126057543 625000000 2421695229193 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707743817/5000000000 : ℝ)^4237 ≤ (44539615189157/100000000000000 : ℝ)^3213 := by
    have hnat : (2707743817 : ℕ)^4237*100000000000000^3213 ≤ 44539615189157^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707743817 5000000000 44539615189157 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652810559/5000000000 : ℝ), (-126057543/625000000 : ℝ), (2707743817/5000000000 : ℝ)] ![(1734076345783/4000000000000 : ℝ), (2421695229193/20000000000000 : ℝ), (44539615189157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652810559/5000000000 : ℝ)|^4237 ≤ (1734076345783/4000000000000 : ℝ)^3213
        have hw : |(2652810559/5000000000 : ℝ)|=(2652810559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126057543/625000000 : ℝ)|^4237 ≤ (2421695229193/20000000000000 : ℝ)^3213
        have hw : |(-126057543/625000000 : ℝ)|=(126057543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707743817/5000000000 : ℝ)|^4237 ≤ (44539615189157/100000000000000 : ℝ)^3213
        have hw : |(2707743817/5000000000 : ℝ)|=(2707743817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8290033/15625000 : ℝ)*x 0 + (5415487633/10000000000 : ℝ)*x 1 + (-2016920687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8290033/15625000 : ℝ)^4237 ≤ (346815269329/800000000000 : ℝ)^3213 := by
    have hnat : (8290033 : ℕ)^4237*800000000000^3213 ≤ 346815269329^3213*15625000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8290033 15625000 346815269329 800000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415487633/10000000000 : ℝ)^4237 ≤ (44539615178311/100000000000000 : ℝ)^3213 := by
    have hnat : (5415487633 : ℕ)^4237*100000000000000^3213 ≤ 44539615178311^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415487633 10000000000 44539615178311 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016920687/10000000000 : ℝ)^4237 ≤ (189194939657/1562500000000 : ℝ)^3213 := by
    have hnat : (2016920687 : ℕ)^4237*1562500000000^3213 ≤ 189194939657^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016920687 10000000000 189194939657 1562500000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8290033/15625000 : ℝ), (5415487633/10000000000 : ℝ), (-2016920687/10000000000 : ℝ)] ![(346815269329/800000000000 : ℝ), (44539615178311/100000000000000 : ℝ), (189194939657/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8290033/15625000 : ℝ)|^4237 ≤ (346815269329/800000000000 : ℝ)^3213
        have hw : |(8290033/15625000 : ℝ)|=(8290033/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415487633/10000000000 : ℝ)|^4237 ≤ (44539615178311/100000000000000 : ℝ)^3213
        have hw : |(5415487633/10000000000 : ℝ)|=(5415487633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016920687/10000000000 : ℝ)|^4237 ≤ (189194939657/1562500000000 : ℝ)^3213
        have hw : |(-2016920687/10000000000 : ℝ)|=(2016920687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s6_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343927441/10000000000 : ℝ)*x 0 + (282729779/625000000 : ℝ)*x 1 + (2085558281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343927441/10000000000 : ℝ)^4237 ≤ (33302269445027/100000000000000 : ℝ)^3213 := by
    have hnat : (4343927441 : ℕ)^4237*100000000000000^3213 ≤ 33302269445027^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343927441 10000000000 33302269445027 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282729779/625000000 : ℝ)^4237 ≤ (17565676540733/50000000000000 : ℝ)^3213 := by
    have hnat : (282729779 : ℕ)^4237*50000000000000^3213 ≤ 17565676540733^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282729779 625000000 17565676540733 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085558281/5000000000 : ℝ)^4237 ≤ (31566377461837/100000000000000 : ℝ)^3213 := by
    have hnat : (2085558281 : ℕ)^4237*100000000000000^3213 ≤ 31566377461837^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085558281 5000000000 31566377461837 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343927441/10000000000 : ℝ), (282729779/625000000 : ℝ), (2085558281/5000000000 : ℝ)] ![(33302269445027/100000000000000 : ℝ), (17565676540733/50000000000000 : ℝ), (31566377461837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343927441/10000000000 : ℝ)|^4237 ≤ (33302269445027/100000000000000 : ℝ)^3213
        have hw : |(4343927441/10000000000 : ℝ)|=(4343927441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282729779/625000000 : ℝ)|^4237 ≤ (17565676540733/50000000000000 : ℝ)^3213
        have hw : |(282729779/625000000 : ℝ)|=(282729779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085558281/5000000000 : ℝ)|^4237 ≤ (31566377461837/100000000000000 : ℝ)^3213
        have hw : |(2085558281/5000000000 : ℝ)|=(2085558281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1833/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5487/50000 : ℝ) ^ (1059/256 : ℝ) ≤ (10721602941686243/100000000000000000000 : ℝ) := by
    have hpowers : (5487/50000 : ℝ)^1059 ≤ (10721602941686243/100000000000000000000 : ℝ)^256 := by
      have hnat : (5487 : ℕ)^1059*100000000000000000000^256 ≤ 10721602941686243^256*50000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5487 50000 10721602941686243 100000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5487/50000 : ℝ)) (X := (10721602941686243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7339/50000 : ℝ) ^ (1059/256 : ℝ) ≤ (17852756262400869/50000000000000000000 : ℝ) := by
    have hpowers : (7339/50000 : ℝ)^1059 ≤ (17852756262400869/50000000000000000000 : ℝ)^256 := by
      have hnat : (7339 : ℕ)^1059*50000000000000000000^256 ≤ 17852756262400869^256*50000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 50000 17852756262400869 50000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/50000 : ℝ)) (X := (17852756262400869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010721602941686243/50000000000000000000 : ℝ) ≤ (5000259160268207/5000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (50010721602941686243/50000000000000000000 : ℝ)^256 ≤ (5000259160268207/5000000000000000 : ℝ)^1059 := by
      have hnat : (50010721602941686243 : ℕ)^256*5000000000000000^1059 ≤ 5000259160268207^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010721602941686243 50000000000000000000 5000259160268207 5000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259160268207/5000000000000000 : ℝ)) (X := (50010721602941686243/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046427115466487981/100000000000000000000 : ℝ) ≤ (10001122119931461/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (100046427115466487981/100000000000000000000 : ℝ)^256 ≤ (10001122119931461/10000000000000000 : ℝ)^1059 := by
      have hnat : (100046427115466487981 : ℕ)^256*10000000000000000^1059 ≤ 10001122119931461^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046427115466487981 100000000000000000000 10001122119931461 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001122119931461/10000000000000000 : ℝ)) (X := (100046427115466487981/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017852756262400869/25000000000000000000 : ℝ) ≤ (2500431479831627/2500000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (25017852756262400869/25000000000000000000 : ℝ)^256 ≤ (2500431479831627/2500000000000000 : ℝ)^1059 := by
      have hnat : (25017852756262400869 : ℕ)^256*2500000000000000^1059 ≤ 2500431479831627^1059*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017852756262400869 25000000000000000000 2500431479831627 2500000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500431479831627/2500000000000000 : ℝ)) (X := (25017852756262400869/25000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10721602941686243/100000000000000000000 : ℝ) ≤ ((370286676701443859/370400000000000000 : ℝ)+2*(603799395047/370400000000000 : ℝ)*(5487/50000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (370286676701443859/370400000000000000 : ℝ)+2*(603799395047/370400000000000 : ℝ)*(5487/50000 : ℝ)=(5000259160268207/5000000000000000 : ℝ) by norm_num, show 1+2*(10721602941686243/100000000000000000000 : ℝ)=(50010721602941686243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17852756262400869/50000000000000000000 : ℝ)+(10721602941686243/100000000000000000000 : ℝ) ≤ ((370286676701443859/370400000000000000 : ℝ)+(603799395047/370400000000000 : ℝ)*((7339/50000 : ℝ)+(5487/50000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (370286676701443859/370400000000000000 : ℝ)+(603799395047/370400000000000 : ℝ)*((7339/50000 : ℝ)+(5487/50000 : ℝ))=(10001122119931461/10000000000000000 : ℝ) by norm_num, show 1+(17852756262400869/50000000000000000000 : ℝ)+(10721602941686243/100000000000000000000 : ℝ)=(100046427115466487981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17852756262400869/50000000000000000000 : ℝ) ≤ ((370286676701443859/370400000000000000 : ℝ)+2*(603799395047/370400000000000 : ℝ)*(7339/50000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (370286676701443859/370400000000000000 : ℝ)+2*(603799395047/370400000000000 : ℝ)*(7339/50000 : ℝ)=(2500431479831627/2500000000000000 : ℝ) by norm_num, show 1+2*(17852756262400869/50000000000000000000 : ℝ)=(25017852756262400869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (370286676701443859/370400000000000000 : ℝ)*(X 1 0+X 2 0)+(603799395047/370400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (370286676701443859/370400000000000000 : ℝ)) (alpha := (603799395047/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (370286676701443859/370400000000000000 : ℝ)*(X 0 1+X 2 1)+(603799395047/370400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (370286676701443859/370400000000000000 : ℝ)) (alpha := (603799395047/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (370286676701443859/370400000000000000 : ℝ)*(X 0 2+X 1 2)+(603799395047/370400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (370286676701443859/370400000000000000 : ℝ)) (alpha := (603799395047/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050737691/5000000000 : ℝ)*X 0 0+(5416110213/10000000000 : ℝ)*X 0 1+(163823053/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350025847/10000000000 : ℝ)*X 1 0+(-3504113/16000000 : ℝ)*X 1 1+(163823053/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350025847/10000000000 : ℝ)*X 2 0+(163823053/312500000 : ℝ)*X 2 1+(-3504113/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085975253/2500000000 : ℝ)*X 0 0+(833968869/2000000000 : ℝ)*X 0 1+(180997687/400000000 : ℝ)*X 0 2+(1085975253/2500000000 : ℝ)*X 1 0+(833968869/2000000000 : ℝ)*X 1 1+(180997687/400000000 : ℝ)*X 1 2+(1085975253/2500000000 : ℝ)*X 2 0+(833968869/2000000000 : ℝ)*X 2 1+(180997687/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420297663/2000000000 : ℝ)*X 0 0+(5242957091/10000000000 : ℝ)*X 0 1+(2707743817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652810559/5000000000 : ℝ)*X 1 0+(-126057543/625000000 : ℝ)*X 1 1+(2707743817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8290033/15625000 : ℝ)*X 2 0+(5415487633/10000000000 : ℝ)*X 2 1+(-2016920687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343927441/10000000000 : ℝ)*X 0 0+(282729779/625000000 : ℝ)*X 0 1+(2085558281/5000000000 : ℝ)*X 0 2+(4343927441/10000000000 : ℝ)*X 1 0+(282729779/625000000 : ℝ)*X 1 1+(2085558281/5000000000 : ℝ)*X 1 2+(4343927441/10000000000 : ℝ)*X 2 0+(282729779/625000000 : ℝ)*X 2 1+(2085558281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6521198933331995546642547/2315000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136486977/25000000000000 : ℝ)*(base19) + (50915611/10000000000000 : ℝ)*(base23) + (19683707/100000000000000 : ℝ)*(lower2) + (17890441/25000000000000 : ℝ)*(upper3) + (44134057/100000000000000 : ℝ)*(upper5) + (1071351063163889/25000000000000 : ℝ)*(major0) + (1071351063163889/25000000000000 : ℝ)*(major1) + (1071351063163889/25000000000000 : ℝ)*(major2) + (143866531886713/2500000000000 : ℝ)*(sp0) + (5754671597662709/100000000000000 : ℝ)*(sp1) + (5754671634454507/100000000000000 : ℝ)*(sp2) + (1408065257241293/50000000000000 : ℝ)*(sp3) + (10868142097/100000000000000 : ℝ)*(sp4) + (719165019/12500000000000 : ℝ)*(sp7) + (1408068133901369/50000000000000 : ℝ)*(f.failure) + (5754672143610617/100000000000000 : ℝ)*(f.sum) + (7206603645687/4630000000000000000000000000 : ℝ)*base66 + (37600859311709349/9260000000000000000000000000000 : ℝ)*base68 + (133780006477470651/9260000000000000000000000000000 : ℝ)*base69 + (37385006651770651/9260000000000000000000000000000 : ℝ)*base71 + (18511946445207/4630000000000000000000000000 : ℝ)*base74 + (26655510851510651/9260000000000000000000000000000 : ℝ)*base75 + (34999603742210651/9260000000000000000000000000000 : ℝ)*base77 + (23057314389190651/9260000000000000000000000000000 : ℝ)*base79 + (5300562449413/4630000000000000000000000000 : ℝ)*base81 + (681947/1000000000000000000000 : ℝ)*base90 + (681947/1000000000000000000000 : ℝ)*base92 + (681947/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20545164406725987552563973/3704000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (991043211/100000000000000 : ℝ)*(base19) + (1079775139/100000000000000 : ℝ)*(base23) + (56528361/50000000000000 : ℝ)*(upper3) + (39055319/100000000000000 : ℝ)*(lower4) + (11395351/10000000000000 : ℝ)*(upper5) + (863247182465617/20000000000000 : ℝ)*(major0) + (863247182465617/20000000000000 : ℝ)*(major1) + (863247182465617/20000000000000 : ℝ)*(major2) + (19710562319/100000000000000 : ℝ)*(sp1) + (21256179349/100000000000000 : ℝ)*(sp2) + (1449018617525033/25000000000000 : ℝ)*(sp4) + (2898026884247301/50000000000000 : ℝ)*(sp5) + (1449013033536411/25000000000000 : ℝ)*(sp6) + (2836397169664343/100000000000000 : ℝ)*(sp7) + (2836397169664343/100000000000000 : ℝ)*(f.failure) + (1449018617525033/25000000000000 : ℝ)*(f.sum) + (21074100557167/3704000000000000000000000000 : ℝ)*base65 + (13587975635383003/7408000000000000000000000000000 : ℝ)*base67 + (39208119231063003/7408000000000000000000000000000 : ℝ)*base69 + (86894274277559003/7408000000000000000000000000000 : ℝ)*base71 + (2210038320979/740800000000000000000000000 : ℝ)*base73 + (94102428913431003/7408000000000000000000000000000 : ℝ)*base75 + (23292366872727003/7408000000000000000000000000000 : ℝ)*base77 + (603051413431003/7408000000000000000000000000000 : ℝ)*base79 + (3365297141953/3704000000000000000000000000 : ℝ)*base82 + (8951509/2000000000000000000000 : ℝ)*base90 + (8951509/2000000000000000000000 : ℝ)*base92 + (8951509/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s7_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101490293/10000000000 : ℝ)*x 0 + (5415984809/10000000000 : ℝ)*x 1 + (2621226633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101490293/10000000000 : ℝ)^4237 ≤ (6391213240319/50000000000000 : ℝ)^3213 := by
    have hnat : (2101490293 : ℕ)^4237*50000000000000^3213 ≤ 6391213240319^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101490293 10000000000 6391213240319 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415984809/10000000000 : ℝ)^4237 ≤ (22272503733529/50000000000000 : ℝ)^3213 := by
    have hnat : (5415984809 : ℕ)^4237*50000000000000^3213 ≤ 22272503733529^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415984809 10000000000 22272503733529 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621226633/5000000000 : ℝ)^4237 ≤ (5334070754121/12500000000000 : ℝ)^3213 := by
    have hnat : (2621226633 : ℕ)^4237*12500000000000^3213 ≤ 5334070754121^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621226633 5000000000 5334070754121 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101490293/10000000000 : ℝ), (5415984809/10000000000 : ℝ), (2621226633/5000000000 : ℝ)] ![(6391213240319/50000000000000 : ℝ), (22272503733529/50000000000000 : ℝ), (5334070754121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101490293/10000000000 : ℝ)|^4237 ≤ (6391213240319/50000000000000 : ℝ)^3213
        have hw : |(-2101490293/10000000000 : ℝ)|=(2101490293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415984809/10000000000 : ℝ)|^4237 ≤ (22272503733529/50000000000000 : ℝ)^3213
        have hw : |(5415984809/10000000000 : ℝ)|=(5415984809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621226633/5000000000 : ℝ)|^4237 ≤ (5334070754121/12500000000000 : ℝ)^3213
        have hw : |(2621226633/5000000000 : ℝ)|=(2621226633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349993463/10000000000 : ℝ)*x 0 + (-273745061/1250000000 : ℝ)*x 1 + (5242453681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349993463/10000000000 : ℝ)^4237 ≤ (21915329670119/50000000000000 : ℝ)^3213 := by
    have hnat : (5349993463 : ℕ)^4237*50000000000000^3213 ≤ 21915329670119^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349993463 10000000000 21915329670119 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273745061/1250000000 : ℝ)^4237 ≤ (6748385079243/50000000000000 : ℝ)^3213 := by
    have hnat : (273745061 : ℕ)^4237*50000000000000^3213 ≤ 6748385079243^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273745061 1250000000 6748385079243 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242453681/10000000000 : ℝ)^4237 ≤ (42672570487581/100000000000000 : ℝ)^3213 := by
    have hnat : (5242453681 : ℕ)^4237*100000000000000^3213 ≤ 42672570487581^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242453681 10000000000 42672570487581 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349993463/10000000000 : ℝ), (-273745061/1250000000 : ℝ), (5242453681/10000000000 : ℝ)] ![(21915329670119/50000000000000 : ℝ), (6748385079243/50000000000000 : ℝ), (42672570487581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349993463/10000000000 : ℝ)|^4237 ≤ (21915329670119/50000000000000 : ℝ)^3213
        have hw : |(5349993463/10000000000 : ℝ)|=(5349993463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273745061/1250000000 : ℝ)|^4237 ≤ (6748385079243/50000000000000 : ℝ)^3213
        have hw : |(-273745061/1250000000 : ℝ)|=(273745061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242453681/10000000000 : ℝ)|^4237 ≤ (42672570487581/100000000000000 : ℝ)^3213
        have hw : |(5242453681/10000000000 : ℝ)|=(5242453681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674996917/5000000000 : ℝ)*x 0 + (5242452017/10000000000 : ℝ)*x 1 + (-136872637/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674996917/5000000000 : ℝ)^4237 ≤ (4383066334841/10000000000000 : ℝ)^3213 := by
    have hnat : (2674996917 : ℕ)^4237*10000000000000^3213 ≤ 4383066334841^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674996917 5000000000 4383066334841 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242452017/10000000000 : ℝ)^4237 ≤ (2667034539137/6250000000000 : ℝ)^3213 := by
    have hnat : (5242452017 : ℕ)^4237*6250000000000^3213 ≤ 2667034539137^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242452017 10000000000 2667034539137 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136872637/625000000 : ℝ)^4237 ≤ (843549000453/6250000000000 : ℝ)^3213 := by
    have hnat : (136872637 : ℕ)^4237*6250000000000^3213 ≤ 843549000453^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136872637 625000000 843549000453 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674996917/5000000000 : ℝ), (5242452017/10000000000 : ℝ), (-136872637/625000000 : ℝ)] ![(4383066334841/10000000000000 : ℝ), (2667034539137/6250000000000 : ℝ), (843549000453/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674996917/5000000000 : ℝ)|^4237 ≤ (4383066334841/10000000000000 : ℝ)^3213
        have hw : |(2674996917/5000000000 : ℝ)|=(2674996917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242452017/10000000000 : ℝ)|^4237 ≤ (2667034539137/6250000000000 : ℝ)^3213
        have hw : |(5242452017/10000000000 : ℝ)|=(5242452017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136872637/625000000 : ℝ)|^4237 ≤ (843549000453/6250000000000 : ℝ)^3213
        have hw : |(-136872637/625000000 : ℝ)|=(136872637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343907967/10000000000 : ℝ)*x 0 + (2085044931/5000000000 : ℝ)*x 1 + (2262348051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343907967/10000000000 : ℝ)^4237 ≤ (6660414513707/20000000000000 : ℝ)^3213 := by
    have hnat : (4343907967 : ℕ)^4237*20000000000000^3213 ≤ 6660414513707^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343907967 10000000000 6660414513707 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085044931/5000000000 : ℝ)^4237 ≤ (31556131642743/100000000000000 : ℝ)^3213 := by
    have hnat : (2085044931 : ℕ)^4237*100000000000000^3213 ≤ 31556131642743^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085044931 5000000000 31556131642743 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262348051/5000000000 : ℝ)^4237 ≤ (35141795778767/100000000000000 : ℝ)^3213 := by
    have hnat : (2262348051 : ℕ)^4237*100000000000000^3213 ≤ 35141795778767^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262348051 5000000000 35141795778767 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343907967/10000000000 : ℝ), (2085044931/5000000000 : ℝ), (2262348051/5000000000 : ℝ)] ![(6660414513707/20000000000000 : ℝ), (31556131642743/100000000000000 : ℝ), (35141795778767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343907967/10000000000 : ℝ)|^4237 ≤ (6660414513707/20000000000000 : ℝ)^3213
        have hw : |(4343907967/10000000000 : ℝ)|=(4343907967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085044931/5000000000 : ℝ)|^4237 ≤ (31556131642743/100000000000000 : ℝ)^3213
        have hw : |(2085044931/5000000000 : ℝ)|=(2085044931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262348051/5000000000 : ℝ)|^4237 ≤ (35141795778767/100000000000000 : ℝ)^3213
        have hw : |(2262348051/5000000000 : ℝ)|=(2262348051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050751737/5000000000 : ℝ)*x 0 + (5243070491/10000000000 : ℝ)*x 1 + (5415364187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050751737/5000000000 : ℝ)^4237 ≤ (2556506441359/20000000000000 : ℝ)^3213 := by
    have hnat : (1050751737 : ℕ)^4237*20000000000000^3213 ≤ 2556506441359^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050751737 5000000000 2556506441359 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243070491/10000000000 : ℝ)^4237 ≤ (21339595727793/50000000000000 : ℝ)^3213 := by
    have hnat : (5243070491 : ℕ)^4237*50000000000000^3213 ≤ 21339595727793^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243070491 10000000000 21339595727793 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415364187/10000000000 : ℝ)^4237 ≤ (22269138163921/50000000000000 : ℝ)^3213 := by
    have hnat : (5415364187 : ℕ)^4237*50000000000000^3213 ≤ 22269138163921^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415364187 10000000000 22269138163921 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050751737/5000000000 : ℝ), (5243070491/10000000000 : ℝ), (5415364187/10000000000 : ℝ)] ![(2556506441359/20000000000000 : ℝ), (21339595727793/50000000000000 : ℝ), (22269138163921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050751737/5000000000 : ℝ)|^4237 ≤ (2556506441359/20000000000000 : ℝ)^3213
        have hw : |(-1050751737/5000000000 : ℝ)|=(1050751737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243070491/10000000000 : ℝ)|^4237 ≤ (21339595727793/50000000000000 : ℝ)^3213
        have hw : |(5243070491/10000000000 : ℝ)|=(5243070491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415364187/10000000000 : ℝ)|^4237 ≤ (22269138163921/50000000000000 : ℝ)^3213
        have hw : |(5415364187/10000000000 : ℝ)|=(5415364187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305650789/10000000000 : ℝ)*x 0 + (-2017049321/10000000000 : ℝ)*x 1 + (270768213/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305650789/10000000000 : ℝ)^4237 ≤ (5419028543961/12500000000000 : ℝ)^3213 := by
    have hnat : (5305650789 : ℕ)^4237*12500000000000^3213 ≤ 5419028543961^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305650789 10000000000 5419028543961 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017049321/10000000000 : ℝ)^4237 ≤ (12109494515081/100000000000000 : ℝ)^3213 := by
    have hnat : (2017049321 : ℕ)^4237*100000000000000^3213 ≤ 12109494515081^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017049321 10000000000 12109494515081 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270768213/500000000 : ℝ)^4237 ≤ (44538277119571/100000000000000 : ℝ)^3213 := by
    have hnat : (270768213 : ℕ)^4237*100000000000000^3213 ≤ 44538277119571^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270768213 500000000 44538277119571 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305650789/10000000000 : ℝ), (-2017049321/10000000000 : ℝ), (270768213/500000000 : ℝ)] ![(5419028543961/12500000000000 : ℝ), (12109494515081/100000000000000 : ℝ), (44538277119571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305650789/10000000000 : ℝ)|^4237 ≤ (5419028543961/12500000000000 : ℝ)^3213
        have hw : |(5305650789/10000000000 : ℝ)|=(5305650789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017049321/10000000000 : ℝ)|^4237 ≤ (12109494515081/100000000000000 : ℝ)^3213
        have hw : |(-2017049321/10000000000 : ℝ)|=(2017049321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270768213/500000000 : ℝ)|^4237 ≤ (44538277119571/100000000000000 : ℝ)^3213
        have hw : |(270768213/500000000 : ℝ)|=(270768213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305650633/10000000000 : ℝ)*x 0 + (338460267/625000000 : ℝ)*x 1 + (-2017049517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305650633/10000000000 : ℝ)^4237 ≤ (1734089066831/4000000000000 : ℝ)^3213 := by
    have hnat : (5305650633 : ℕ)^4237*4000000000000^3213 ≤ 1734089066831^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305650633 10000000000 1734089066831 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338460267/625000000 : ℝ)^4237 ≤ (22269138624859/50000000000000 : ℝ)^3213 := by
    have hnat : (338460267 : ℕ)^4237*50000000000000^3213 ≤ 22269138624859^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338460267 625000000 22269138624859 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017049517/10000000000 : ℝ)^4237 ≤ (12109496066801/100000000000000 : ℝ)^3213 := by
    have hnat : (2017049517 : ℕ)^4237*100000000000000^3213 ≤ 12109496066801^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017049517 10000000000 12109496066801 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305650633/10000000000 : ℝ), (338460267/625000000 : ℝ), (-2017049517/10000000000 : ℝ)] ![(1734089066831/4000000000000 : ℝ), (22269138624859/50000000000000 : ℝ), (12109496066801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305650633/10000000000 : ℝ)|^4237 ≤ (1734089066831/4000000000000 : ℝ)^3213
        have hw : |(5305650633/10000000000 : ℝ)|=(5305650633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338460267/625000000 : ℝ)|^4237 ≤ (22269138624859/50000000000000 : ℝ)^3213
        have hw : |(338460267/625000000 : ℝ)|=(338460267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017049517/10000000000 : ℝ)|^4237 ≤ (12109496066801/100000000000000 : ℝ)^3213
        have hw : |(-2017049517/10000000000 : ℝ)|=(2017049517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s7_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085983989/2500000000 : ℝ)*x 0 + (4523433061/10000000000 : ℝ)*x 1 + (4171357711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085983989/2500000000 : ℝ)^4237 ≤ (6660471105859/20000000000000 : ℝ)^3213 := by
    have hnat : (1085983989 : ℕ)^4237*20000000000000^3213 ≤ 6660471105859^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085983989 2500000000 6660471105859 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523433061/10000000000 : ℝ)^4237 ≤ (8782215090677/25000000000000 : ℝ)^3213 := by
    have hnat : (4523433061 : ℕ)^4237*25000000000000^3213 ≤ 8782215090677^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523433061 10000000000 8782215090677 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171357711/10000000000 : ℝ)^4237 ≤ (31568784093487/100000000000000 : ℝ)^3213 := by
    have hnat : (4171357711 : ℕ)^4237*100000000000000^3213 ≤ 31568784093487^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171357711 10000000000 31568784093487 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085983989/2500000000 : ℝ), (4523433061/10000000000 : ℝ), (4171357711/10000000000 : ℝ)] ![(6660471105859/20000000000000 : ℝ), (8782215090677/25000000000000 : ℝ), (31568784093487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085983989/2500000000 : ℝ)|^4237 ≤ (6660471105859/20000000000000 : ℝ)^3213
        have hw : |(1085983989/2500000000 : ℝ)|=(1085983989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523433061/10000000000 : ℝ)|^4237 ≤ (8782215090677/25000000000000 : ℝ)^3213
        have hw : |(4523433061/10000000000 : ℝ)|=(4523433061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171357711/10000000000 : ℝ)|^4237 ≤ (31568784093487/100000000000000 : ℝ)^3213
        have hw : |(4171357711/10000000000 : ℝ)|=(4171357711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7331/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10987/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (5387120564239951/50000000000000000000 : ℝ) := by
    have hpowers : (10987/100000 : ℝ)^1059 ≤ (5387120564239951/50000000000000000000 : ℝ)^256 := by
      have hnat : (10987 : ℕ)^1059*50000000000000000000^256 ≤ 5387120564239951^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10987 100000 5387120564239951 50000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10987/100000 : ℝ)) (X := (5387120564239951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1833/12500 : ℝ) ^ (1059/256 : ℝ) ≤ (355648421299019/1000000000000000000 : ℝ) := by
    have hpowers : (1833/12500 : ℝ)^1059 ≤ (355648421299019/1000000000000000000 : ℝ)^256 := by
      have hnat : (1833 : ℕ)^1059*1000000000000000000^256 ≤ 355648421299019^256*12500^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1833 12500 355648421299019 1000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1833/12500 : ℝ)) (X := (355648421299019/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005387120564239951/25000000000000000000 : ℝ) ≤ (5000260432523147/5000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (25005387120564239951/25000000000000000000 : ℝ)^256 ≤ (5000260432523147/5000000000000000 : ℝ)^1059 := by
      have hnat : (25005387120564239951 : ℕ)^256*5000000000000000^1059 ≤ 5000260432523147^1059*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005387120564239951 25000000000000000000 5000260432523147 5000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000260432523147/5000000000000000 : ℝ)) (X := (25005387120564239951/25000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023169541629190901/50000000000000000000 : ℝ) ≤ (10001119992611123/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (50023169541629190901/50000000000000000000 : ℝ)^256 ≤ (10001119992611123/10000000000000000 : ℝ)^1059 := by
      have hnat : (50023169541629190901 : ℕ)^256*10000000000000000^1059 ≤ 10001119992611123^1059*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023169541629190901 50000000000000000000 10001119992611123 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119992611123/10000000000000000 : ℝ)) (X := (50023169541629190901/50000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (500355648421299019/500000000000000000 : ℝ) ≤ (625107445010997/625000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (500355648421299019/500000000000000000 : ℝ)^256 ≤ (625107445010997/625000000000000 : ℝ)^1059 := by
      have hnat : (500355648421299019 : ℕ)^256*625000000000000^1059 ≤ 625107445010997^1059*500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500355648421299019 500000000000000000 625107445010997 625000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625107445010997/625000000000000 : ℝ)) (X := (500355648421299019/500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5387120564239951/50000000000000000000 : ℝ) ≤ ((574355468619776103/574531250000000000 : ℝ)+2*(599127564829/367700000000000 : ℝ)*(10987/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (574355468619776103/574531250000000000 : ℝ)+2*(599127564829/367700000000000 : ℝ)*(10987/100000 : ℝ)=(5000260432523147/5000000000000000 : ℝ) by norm_num, show 1+2*(5387120564239951/50000000000000000000 : ℝ)=(25005387120564239951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(355648421299019/1000000000000000000 : ℝ)+(5387120564239951/50000000000000000000 : ℝ) ≤ ((574355468619776103/574531250000000000 : ℝ)+(599127564829/367700000000000 : ℝ)*((1833/12500 : ℝ)+(10987/100000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (574355468619776103/574531250000000000 : ℝ)+(599127564829/367700000000000 : ℝ)*((1833/12500 : ℝ)+(10987/100000 : ℝ))=(10001119992611123/10000000000000000 : ℝ) by norm_num, show 1+(355648421299019/1000000000000000000 : ℝ)+(5387120564239951/50000000000000000000 : ℝ)=(50023169541629190901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(355648421299019/1000000000000000000 : ℝ) ≤ ((574355468619776103/574531250000000000 : ℝ)+2*(599127564829/367700000000000 : ℝ)*(1833/12500 : ℝ))^(1059/256 : ℝ) := by
    rw [show (574355468619776103/574531250000000000 : ℝ)+2*(599127564829/367700000000000 : ℝ)*(1833/12500 : ℝ)=(625107445010997/625000000000000 : ℝ) by norm_num, show 1+2*(355648421299019/1000000000000000000 : ℝ)=(500355648421299019/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (574355468619776103/574531250000000000 : ℝ)*(X 1 0+X 2 0)+(599127564829/367700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (574355468619776103/574531250000000000 : ℝ)) (alpha := (599127564829/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (574355468619776103/574531250000000000 : ℝ)*(X 0 1+X 2 1)+(599127564829/367700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (574355468619776103/574531250000000000 : ℝ)) (alpha := (599127564829/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (574355468619776103/574531250000000000 : ℝ)*(X 0 2+X 1 2)+(599127564829/367700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (574355468619776103/574531250000000000 : ℝ)) (alpha := (599127564829/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2101490293/10000000000 : ℝ)*X 0 0+(5415984809/10000000000 : ℝ)*X 0 1+(2621226633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349993463/10000000000 : ℝ)*X 1 0+(-273745061/1250000000 : ℝ)*X 1 1+(5242453681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674996917/5000000000 : ℝ)*X 2 0+(5242452017/10000000000 : ℝ)*X 2 1+(-136872637/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343907967/10000000000 : ℝ)*X 0 0+(2085044931/5000000000 : ℝ)*X 0 1+(2262348051/5000000000 : ℝ)*X 0 2+(4343907967/10000000000 : ℝ)*X 1 0+(2085044931/5000000000 : ℝ)*X 1 1+(2262348051/5000000000 : ℝ)*X 1 2+(4343907967/10000000000 : ℝ)*X 2 0+(2085044931/5000000000 : ℝ)*X 2 1+(2262348051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1050751737/5000000000 : ℝ)*X 0 0+(5243070491/10000000000 : ℝ)*X 0 1+(5415364187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305650789/10000000000 : ℝ)*X 1 0+(-2017049321/10000000000 : ℝ)*X 1 1+(270768213/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305650633/10000000000 : ℝ)*X 2 0+(338460267/625000000 : ℝ)*X 2 1+(-2017049517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085983989/2500000000 : ℝ)*X 0 0+(4523433061/10000000000 : ℝ)*X 0 1+(4171357711/10000000000 : ℝ)*X 0 2+(1085983989/2500000000 : ℝ)*X 1 0+(4523433061/10000000000 : ℝ)*X 1 1+(4171357711/10000000000 : ℝ)*X 1 2+(1085983989/2500000000 : ℝ)*X 2 0+(4523433061/10000000000 : ℝ)*X 2 1+(4171357711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689792373746680585513328361/57453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5146063/100000000000000 : ℝ)*(base15) + (64842437/50000000000000 : ℝ)*(upper2) + (104062981/100000000000000 : ℝ)*(upper4) + (106214237/100000000000000 : ℝ)*(lower5) + (2145681148411917/50000000000000 : ℝ)*(major0) + (2145681148411917/50000000000000 : ℝ)*(major1) + (2145681148411917/50000000000000 : ℝ)*(major2) + (2881329472943987/50000000000000 : ℝ)*(sp0) + (720334076949163/12500000000000 : ℝ)*(sp1) + (1440654792137079/25000000000000 : ℝ)*(sp2) + (2820039744685239/100000000000000 : ℝ)*(sp3) + (13674851393/100000000000000 : ℝ)*(sp4) + (53452191051/100000000000000 : ℝ)*(sp6) + (5914008581/50000000000000 : ℝ)*(sp7) + (2820051572702401/100000000000000 : ℝ)*(f.failure) + (5762672620739367/100000000000000 : ℝ)*(f.sum) + (63251619567199/18385000000000000000000000000 : ℝ)*base66 + (373431996949186799/28726562500000000000000000000000 : ℝ)*base68 + (13171241818275857/897705078125000000000000000000 : ℝ)*base70 + (472451794532905549/28726562500000000000000000000000 : ℝ)*base72 + (1309380482203/9192500000000000000000000000 : ℝ)*base73 + (371158231572357973/57453125000000000000000000000000 : ℝ)*base76 + (602459814765420473/57453125000000000000000000000000 : ℝ)*base78 + (875062157371107973/57453125000000000000000000000000 : ℝ)*base80 + (14955721550801/18385000000000000000000000000 : ℝ)*base81 + (3463437/2000000000000000000000 : ℝ)*base89 + (3463437/2000000000000000000000 : ℝ)*base91 + (3463437/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157166695123628490701947587/14363281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1184130137/50000000000000 : ℝ)*(base19) + (2223875873/100000000000000 : ℝ)*(base23) + (782711487/100000000000000 : ℝ)*(lower1) + (22723413/12500000000000 : ℝ)*(upper3) + (55900097/100000000000000 : ℝ)*(lower4) + (321247997/100000000000000 : ℝ)*(upper5) + (135066802175773/3125000000000 : ℝ)*(major0) + (135066802175773/3125000000000 : ℝ)*(major1) + (135066802175773/3125000000000 : ℝ)*(major2) + (9463358197/100000000000000 : ℝ)*(sp1) + (1450999872159053/25000000000000 : ℝ)*(sp4) + (5803987657017741/100000000000000 : ℝ)*(sp5) + (2901998632380169/50000000000000 : ℝ)*(sp6) + (2840275485871401/100000000000000 : ℝ)*(sp7) + (2840275485871401/100000000000000 : ℝ)*(f.failure) + (1450999872159053/25000000000000 : ℝ)*(f.sum) + (14892082063259/4596250000000000000000000000 : ℝ)*base66 + (110255266780244317/57453125000000000000000000000000 : ℝ)*base68 + (133256689457974433/57453125000000000000000000000000 : ℝ)*base69 + (59748714911692649/7181640625000000000000000000000 : ℝ)*base72 + (657402885031/1149062500000000000000000000 : ℝ)*base74 + (3497560546083363/3590820312500000000000000000000 : ℝ)*base75 + (95416055784567471/28726562500000000000000000000000 : ℝ)*base78 + (459376296067556817/57453125000000000000000000000000 : ℝ)*base80 + (60370401889619/18385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1883563/2000000000000000000000 : ℝ)*base90 + (1883563/2000000000000000000000 : ℝ)*base92 + (1883563/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s8_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349989531/10000000000 : ℝ)*x 0 + (1310617409/2500000000 : ℝ)*x 1 + (-1094972321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349989531/10000000000 : ℝ)^4237 ≤ (43830616860097/100000000000000 : ℝ)^3213 := by
    have hnat : (5349989531 : ℕ)^4237*100000000000000^3213 ≤ 43830616860097^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349989531 10000000000 43830616860097 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310617409/2500000000 : ℝ)^4237 ≤ (10668185437193/25000000000000 : ℝ)^3213 := by
    have hnat : (1310617409 : ℕ)^4237*25000000000000^3213 ≤ 10668185437193^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310617409 2500000000 10668185437193 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094972321/5000000000 : ℝ)^4237 ≤ (2699328274983/20000000000000 : ℝ)^3213 := by
    have hnat : (1094972321 : ℕ)^4237*20000000000000^3213 ≤ 2699328274983^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094972321 5000000000 2699328274983 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349989531/10000000000 : ℝ), (1310617409/2500000000 : ℝ), (-1094972321/5000000000 : ℝ)] ![(43830616860097/100000000000000 : ℝ), (10668185437193/25000000000000 : ℝ), (2699328274983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349989531/10000000000 : ℝ)|^4237 ≤ (43830616860097/100000000000000 : ℝ)^3213
        have hw : |(5349989531/10000000000 : ℝ)|=(5349989531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310617409/2500000000 : ℝ)|^4237 ≤ (10668185437193/25000000000000 : ℝ)^3213
        have hw : |(1310617409/2500000000 : ℝ)|=(1310617409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094972321/5000000000 : ℝ)|^4237 ≤ (2699328274983/20000000000000 : ℝ)^3213
        have hw : |(-1094972321/5000000000 : ℝ)|=(1094972321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s8_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-525376299/2500000000 : ℝ)*x 0 + (1048617477/2000000000 : ℝ)*x 1 + (338459137/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525376299/2500000000 : ℝ)^4237 ≤ (255650920383/2000000000000 : ℝ)^3213 := by
    have hnat : (525376299 : ℕ)^4237*2000000000000^3213 ≤ 255650920383^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525376299 2500000000 255650920383 2000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048617477/2000000000 : ℝ)^4237 ≤ (42679372802821/100000000000000 : ℝ)^3213 := by
    have hnat : (1048617477 : ℕ)^4237*100000000000000^3213 ≤ 42679372802821^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048617477 2000000000 42679372802821 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338459137/625000000 : ℝ)^4237 ≤ (22269040580711/50000000000000 : ℝ)^3213 := by
    have hnat : (338459137 : ℕ)^4237*50000000000000^3213 ≤ 22269040580711^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338459137 625000000 22269040580711 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525376299/2500000000 : ℝ), (1048617477/2000000000 : ℝ), (338459137/625000000 : ℝ)] ![(255650920383/2000000000000 : ℝ), (42679372802821/100000000000000 : ℝ), (22269040580711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525376299/2500000000 : ℝ)|^4237 ≤ (255650920383/2000000000000 : ℝ)^3213
        have hw : |(-525376299/2500000000 : ℝ)|=(525376299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048617477/2000000000 : ℝ)|^4237 ≤ (42679372802821/100000000000000 : ℝ)^3213
        have hw : |(1048617477/2000000000 : ℝ)|=(1048617477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338459137/625000000 : ℝ)|^4237 ≤ (22269040580711/50000000000000 : ℝ)^3213
        have hw : |(338459137/625000000 : ℝ)|=(338459137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s8_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061131039/2000000000 : ℝ)*x 0 + (-504267021/2500000000 : ℝ)*x 1 + (2707673093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061131039/2000000000 : ℝ)^4237 ≤ (5419034478337/12500000000000 : ℝ)^3213 := by
    have hnat : (1061131039 : ℕ)^4237*12500000000000^3213 ≤ 5419034478337^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061131039 2000000000 5419034478337 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504267021/2500000000 : ℝ)^4237 ≤ (12109643060807/100000000000000 : ℝ)^3213 := by
    have hnat : (504267021 : ℕ)^4237*100000000000000^3213 ≤ 12109643060807^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504267021 2500000000 12109643060807 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707673093/5000000000 : ℝ)^4237 ≤ (11134520274087/25000000000000 : ℝ)^3213 := by
    have hnat : (2707673093 : ℕ)^4237*25000000000000^3213 ≤ 11134520274087^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707673093 5000000000 11134520274087 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061131039/2000000000 : ℝ), (-504267021/2500000000 : ℝ), (2707673093/5000000000 : ℝ)] ![(5419034478337/12500000000000 : ℝ), (12109643060807/100000000000000 : ℝ), (11134520274087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061131039/2000000000 : ℝ)|^4237 ≤ (5419034478337/12500000000000 : ℝ)^3213
        have hw : |(1061131039/2000000000 : ℝ)|=(1061131039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504267021/2500000000 : ℝ)|^4237 ≤ (12109643060807/100000000000000 : ℝ)^3213
        have hw : |(-504267021/2500000000 : ℝ)|=(504267021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707673093/5000000000 : ℝ)|^4237 ≤ (11134520274087/25000000000000 : ℝ)^3213
        have hw : |(2707673093/5000000000 : ℝ)|=(2707673093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s8_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061131039/2000000000 : ℝ)*x 0 + (1083069237/2000000000 : ℝ)*x 1 + (-2017068087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061131039/2000000000 : ℝ)^4237 ≤ (5419034478337/12500000000000 : ℝ)^3213 := by
    have hnat : (1061131039 : ℕ)^4237*12500000000000^3213 ≤ 5419034478337^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061131039 2000000000 5419034478337 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083069237/2000000000 : ℝ)^4237 ≤ (44538081085503/100000000000000 : ℝ)^3213 := by
    have hnat : (1083069237 : ℕ)^4237*100000000000000^3213 ≤ 44538081085503^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083069237 2000000000 44538081085503 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017068087/10000000000 : ℝ)^4237 ≤ (12109643084557/100000000000000 : ℝ)^3213 := by
    have hnat : (2017068087 : ℕ)^4237*100000000000000^3213 ≤ 12109643084557^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017068087 10000000000 12109643084557 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061131039/2000000000 : ℝ), (1083069237/2000000000 : ℝ), (-2017068087/10000000000 : ℝ)] ![(5419034478337/12500000000000 : ℝ), (44538081085503/100000000000000 : ℝ), (12109643084557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061131039/2000000000 : ℝ)|^4237 ≤ (5419034478337/12500000000000 : ℝ)^3213
        have hw : |(1061131039/2000000000 : ℝ)|=(1061131039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083069237/2000000000 : ℝ)|^4237 ≤ (44538081085503/100000000000000 : ℝ)^3213
        have hw : |(1083069237/2000000000 : ℝ)|=(1083069237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017068087/10000000000 : ℝ)|^4237 ≤ (12109643084557/100000000000000 : ℝ)^3213
        have hw : |(-2017068087/10000000000 : ℝ)|=(2017068087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s8_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868787427/2000000000 : ℝ)*x 0 + (4523397559/10000000000 : ℝ)*x 1 + (1042848237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868787427/2000000000 : ℝ)^4237 ≤ (1665118372433/5000000000000 : ℝ)^3213 := by
    have hnat : (868787427 : ℕ)^4237*5000000000000^3213 ≤ 1665118372433^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868787427 2000000000 1665118372433 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523397559/10000000000 : ℝ)^4237 ≤ (35128496786121/100000000000000 : ℝ)^3213 := by
    have hnat : (4523397559 : ℕ)^4237*100000000000000^3213 ≤ 35128496786121^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523397559 10000000000 35128496786121 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042848237/2500000000 : ℝ)^4237 ≤ (31569135757291/100000000000000 : ℝ)^3213 := by
    have hnat : (1042848237 : ℕ)^4237*100000000000000^3213 ≤ 31569135757291^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042848237 2500000000 31569135757291 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868787427/2000000000 : ℝ), (4523397559/10000000000 : ℝ), (1042848237/2500000000 : ℝ)] ![(1665118372433/5000000000000 : ℝ), (35128496786121/100000000000000 : ℝ), (31569135757291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868787427/2000000000 : ℝ)|^4237 ≤ (1665118372433/5000000000000 : ℝ)^3213
        have hw : |(868787427/2000000000 : ℝ)|=(868787427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523397559/10000000000 : ℝ)|^4237 ≤ (35128496786121/100000000000000 : ℝ)^3213
        have hw : |(4523397559/10000000000 : ℝ)|=(4523397559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042848237/2500000000 : ℝ)|^4237 ≤ (31569135757291/100000000000000 : ℝ)^3213
        have hw : |(1042848237/2500000000 : ℝ)|=(1042848237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14661/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (2156471334147663/20000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^1059 ≤ (2156471334147663/20000000000000000000 : ℝ)^256 := by
      have hnat : (10989 : ℕ)^1059*20000000000000000000^256 ≤ 2156471334147663^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 2156471334147663 20000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (2156471334147663/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7331/50000 : ℝ) ^ (1059/256 : ℝ) ≤ (888619517915783/2500000000000000000 : ℝ) := by
    have hpowers : (7331/50000 : ℝ)^1059 ≤ (888619517915783/2500000000000000000 : ℝ)^256 := by
      have hnat : (7331 : ℕ)^1059*2500000000000000000^256 ≤ 888619517915783^256*50000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7331 50000 888619517915783 2500000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7331/50000 : ℝ)) (X := (888619517915783/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002156471334147663/10000000000000000000 : ℝ) ≤ (2500130314337083/2500000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (10002156471334147663/10000000000000000000 : ℝ)^256 ≤ (2500130314337083/2500000000000000 : ℝ)^1059 := by
      have hnat : (10002156471334147663 : ℕ)^256*2500000000000000^1059 ≤ 2500130314337083^1059*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002156471334147663 10000000000000000000 2500130314337083 2500000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500130314337083/2500000000000000 : ℝ)) (X := (10002156471334147663/10000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009265427477473927/20000000000000000000 : ℝ) ≤ (10001119703936051/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (20009265427477473927/20000000000000000000 : ℝ)^256 ≤ (10001119703936051/10000000000000000 : ℝ)^1059 := by
      have hnat : (20009265427477473927 : ℕ)^256*10000000000000000^1059 ≤ 10001119703936051^1059*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009265427477473927 20000000000000000000 10001119703936051 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119703936051/10000000000000000 : ℝ)) (X := (20009265427477473927/20000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250888619517915783/1250000000000000000 : ℝ) ≤ (1000171815052377/1000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (1250888619517915783/1250000000000000000 : ℝ)^256 ≤ (1000171815052377/1000000000000000 : ℝ)^1059 := by
      have hnat : (1250888619517915783 : ℕ)^256*1000000000000000^1059 ≤ 1000171815052377^1059*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250888619517915783 1250000000000000000 1000171815052377 1000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000171815052377/1000000000000000 : ℝ)) (X := (1250888619517915783/1250000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2156471334147663/20000000000000000000 : ℝ) ≤ ((18359380959567767627/18365000000000000000 : ℝ)+2*(598446587719/367300000000000 : ℝ)*(10989/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (18359380959567767627/18365000000000000000 : ℝ)+2*(598446587719/367300000000000 : ℝ)*(10989/100000 : ℝ)=(2500130314337083/2500000000000000 : ℝ) by norm_num, show 1+2*(2156471334147663/20000000000000000000 : ℝ)=(10002156471334147663/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(888619517915783/2500000000000000000 : ℝ)+(2156471334147663/20000000000000000000 : ℝ) ≤ ((18359380959567767627/18365000000000000000 : ℝ)+(598446587719/367300000000000 : ℝ)*((7331/50000 : ℝ)+(10989/100000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (18359380959567767627/18365000000000000000 : ℝ)+(598446587719/367300000000000 : ℝ)*((7331/50000 : ℝ)+(10989/100000 : ℝ))=(10001119703936051/10000000000000000 : ℝ) by norm_num, show 1+(888619517915783/2500000000000000000 : ℝ)+(2156471334147663/20000000000000000000 : ℝ)=(20009265427477473927/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(888619517915783/2500000000000000000 : ℝ) ≤ ((18359380959567767627/18365000000000000000 : ℝ)+2*(598446587719/367300000000000 : ℝ)*(7331/50000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (18359380959567767627/18365000000000000000 : ℝ)+2*(598446587719/367300000000000 : ℝ)*(7331/50000 : ℝ)=(1000171815052377/1000000000000000 : ℝ) by norm_num, show 1+2*(888619517915783/2500000000000000000 : ℝ)=(1250888619517915783/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18359380959567767627/18365000000000000000 : ℝ)*(X 1 0+X 2 0)+(598446587719/367300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (18359380959567767627/18365000000000000000 : ℝ)) (alpha := (598446587719/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18359380959567767627/18365000000000000000 : ℝ)*(X 0 1+X 2 1)+(598446587719/367300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (18359380959567767627/18365000000000000000 : ℝ)) (alpha := (598446587719/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18359380959567767627/18365000000000000000 : ℝ)*(X 0 2+X 1 2)+(598446587719/367300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (18359380959567767627/18365000000000000000 : ℝ)) (alpha := (598446587719/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349989531/10000000000 : ℝ)*X 2 0+(1310617409/2500000000 : ℝ)*X 2 1+(-1094972321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-525376299/2500000000 : ℝ)*X 0 0+(1048617477/2000000000 : ℝ)*X 0 1+(338459137/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1061131039/2000000000 : ℝ)*X 1 0+(-504267021/2500000000 : ℝ)*X 1 1+(2707673093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061131039/2000000000 : ℝ)*X 2 0+(1083069237/2000000000 : ℝ)*X 2 1+(-2017068087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((868787427/2000000000 : ℝ)*X 0 0+(4523397559/10000000000 : ℝ)*X 0 1+(1042848237/2500000000 : ℝ)*X 0 2+(868787427/2000000000 : ℝ)*X 1 0+(4523397559/10000000000 : ℝ)*X 1 1+(1042848237/2500000000 : ℝ)*X 1 2+(868787427/2000000000 : ℝ)*X 2 0+(4523397559/10000000000 : ℝ)*X 2 1+(1042848237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1269512846464797878376491553/229562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245934099/25000000000000 : ℝ)*(base19) + (536574281/50000000000000 : ℝ)*(base23) + (336577467/100000000000000 : ℝ)*(lower1) + (6934281/6250000000000 : ℝ)*(upper3) + (8218959/20000000000000 : ℝ)*(lower4) + (114126887/100000000000000 : ℝ)*(upper5) + (2161515082136113/50000000000000 : ℝ)*(major0) + (2161515082136113/50000000000000 : ℝ)*(major1) + (2161515082136113/50000000000000 : ℝ)*(major2) + (11179641/781250000000 : ℝ)*(sp0) + (1161039631809283/20000000000000 : ℝ)*(sp1) + (5805197175310019/100000000000000 : ℝ)*(sp2) + (2902597827451903/50000000000000 : ℝ)*(sp3) + (1420430992580009/50000000000000 : ℝ)*(sp4) + (1420430992580009/50000000000000 : ℝ)*(f.failure) + (1161039631809283/20000000000000 : ℝ)*(f.sum) + (17286562700089/4591250000000000000000000000 : ℝ)*base66 + (6905840913293886149/918250000000000000000000000000000 : ℝ)*base68 + (2441294635896636149/918250000000000000000000000000000 : ℝ)*base70 + (1624429511067613851/918250000000000000000000000000000 : ℝ)*base71 + (26172772698899/4591250000000000000000000000 : ℝ)*base74 + (3302370583832136149/918250000000000000000000000000000 : ℝ)*base76 + (1322771872024636149/918250000000000000000000000000000 : ℝ)*base78 + (21767562771493636149/918250000000000000000000000000000 : ℝ)*base80 + (2716714542719/1147812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7371733/1000000000000000000000 : ℝ)*base89 + (7371733/1000000000000000000000 : ℝ)*base91 + (7371733/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1277_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1277_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1277_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1277_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1277_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

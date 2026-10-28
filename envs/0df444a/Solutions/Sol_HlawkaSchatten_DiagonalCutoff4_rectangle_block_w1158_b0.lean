-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:42.705427+00:00
-- url     : https://prove2.me/submissions/239025d5-519d-44d3-b8f7-e7d5fe9739f3

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
theorem support_rectangle_w1158_s0_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1886757241/10000000000 : ℝ)*x 0 + (1512659871/2500000000 : ℝ)*x 1 + (4782492477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1886757241/10000000000 : ℝ)^8351 ≤ (1097433760639/10000000000000 : ℝ)^6303 := by
    have hnat : (1886757241 : ℕ)^8351*10000000000000^6303 ≤ 1097433760639^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886757241 10000000000 1097433760639 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512659871/2500000000 : ℝ)^8351 ≤ (1606028165811/3125000000000 : ℝ)^6303 := by
    have hnat : (1512659871 : ℕ)^8351*3125000000000^6303 ≤ 1606028165811^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512659871 2500000000 1606028165811 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782492477/10000000000 : ℝ)^8351 ≤ (2352047566867/6250000000000 : ℝ)^6303 := by
    have hnat : (4782492477 : ℕ)^8351*6250000000000^6303 ≤ 2352047566867^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782492477 10000000000 2352047566867 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1886757241/10000000000 : ℝ), (1512659871/2500000000 : ℝ), (4782492477/10000000000 : ℝ)] ![(1097433760639/10000000000000 : ℝ), (1606028165811/3125000000000 : ℝ), (2352047566867/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1886757241/10000000000 : ℝ)|^8351 ≤ (1097433760639/10000000000000 : ℝ)^6303
        have hw : |(-1886757241/10000000000 : ℝ)|=(1886757241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1512659871/2500000000 : ℝ)|^8351 ≤ (1606028165811/3125000000000 : ℝ)^6303
        have hw : |(1512659871/2500000000 : ℝ)|=(1512659871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782492477/10000000000 : ℝ)|^8351 ≤ (2352047566867/6250000000000 : ℝ)^6303
        have hw : |(4782492477/10000000000 : ℝ)|=(4782492477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (220635691/400000000 : ℝ)*x 0 + (-1307035483/5000000000 : ℝ)*x 1 + (95649853/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220635691/400000000 : ℝ)^8351 ≤ (22731619580753/50000000000000 : ℝ)^6303 := by
    have hnat : (220635691 : ℕ)^8351*50000000000000^6303 ≤ 22731619580753^6303*400000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220635691 400000000 22731619580753 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307035483/5000000000 : ℝ)^8351 ≤ (8451998975379/50000000000000 : ℝ)^6303 := by
    have hnat : (1307035483 : ℕ)^8351*50000000000000^6303 ≤ 8451998975379^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307035483 5000000000 8451998975379 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95649853/200000000 : ℝ)^8351 ≤ (37632762873509/100000000000000 : ℝ)^6303 := by
    have hnat : (95649853 : ℕ)^8351*100000000000000^6303 ≤ 37632762873509^6303*200000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95649853 200000000 37632762873509 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220635691/400000000 : ℝ), (-1307035483/5000000000 : ℝ), (95649853/200000000 : ℝ)] ![(22731619580753/50000000000000 : ℝ), (8451998975379/50000000000000 : ℝ), (37632762873509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220635691/400000000 : ℝ)|^8351 ≤ (22731619580753/50000000000000 : ℝ)^6303
        have hw : |(220635691/400000000 : ℝ)|=(220635691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307035483/5000000000 : ℝ)|^8351 ≤ (8451998975379/50000000000000 : ℝ)^6303
        have hw : |(-1307035483/5000000000 : ℝ)|=(1307035483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95649853/200000000 : ℝ)|^8351 ≤ (37632762873509/100000000000000 : ℝ)^6303
        have hw : |(95649853/200000000 : ℝ)|=(95649853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (17237163/31250000 : ℝ)*x 0 + (956498537/2000000000 : ℝ)*x 1 + (-261407107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17237163/31250000 : ℝ)^8351 ≤ (11365809476417/25000000000000 : ℝ)^6303 := by
    have hnat : (17237163 : ℕ)^8351*25000000000000^6303 ≤ 11365809476417^6303*31250000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17237163 31250000 11365809476417 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956498537/2000000000 : ℝ)^8351 ≤ (18816381619203/50000000000000 : ℝ)^6303 := by
    have hnat : (956498537 : ℕ)^8351*50000000000000^6303 ≤ 18816381619203^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956498537 2000000000 18816381619203 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261407107/1000000000 : ℝ)^8351 ≤ (16903998841797/100000000000000 : ℝ)^6303 := by
    have hnat : (261407107 : ℕ)^8351*100000000000000^6303 ≤ 16903998841797^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261407107 1000000000 16903998841797 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17237163/31250000 : ℝ), (956498537/2000000000 : ℝ), (-261407107/1000000000 : ℝ)] ![(11365809476417/25000000000000 : ℝ), (18816381619203/50000000000000 : ℝ), (16903998841797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17237163/31250000 : ℝ)|^8351 ≤ (11365809476417/25000000000000 : ℝ)^6303
        have hw : |(17237163/31250000 : ℝ)|=(17237163/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956498537/2000000000 : ℝ)|^8351 ≤ (18816381619203/50000000000000 : ℝ)^6303
        have hw : |(956498537/2000000000 : ℝ)|=(956498537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261407107/1000000000 : ℝ)|^8351 ≤ (16903998841797/100000000000000 : ℝ)^6303
        have hw : |(-261407107/1000000000 : ℝ)|=(261407107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4199700071/10000000000 : ℝ)*x 0 + (624069749/2000000000 : ℝ)*x 1 + (1412803657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199700071/10000000000 : ℝ)^8351 ≤ (31680542494091/100000000000000 : ℝ)^6303 := by
    have hnat : (4199700071 : ℕ)^8351*100000000000000^6303 ≤ 31680542494091^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199700071 10000000000 31680542494091 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624069749/2000000000 : ℝ)^8351 ≤ (10686297887603/50000000000000 : ℝ)^6303 := by
    have hnat : (624069749 : ℕ)^8351*50000000000000^6303 ≤ 10686297887603^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624069749 2000000000 10686297887603 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1412803657/2500000000 : ℝ)^8351 ≤ (2347343086173/5000000000000 : ℝ)^6303 := by
    have hnat : (1412803657 : ℕ)^8351*5000000000000^6303 ≤ 2347343086173^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412803657 2500000000 2347343086173 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199700071/10000000000 : ℝ), (624069749/2000000000 : ℝ), (1412803657/2500000000 : ℝ)] ![(31680542494091/100000000000000 : ℝ), (10686297887603/50000000000000 : ℝ), (2347343086173/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199700071/10000000000 : ℝ)|^8351 ≤ (31680542494091/100000000000000 : ℝ)^6303
        have hw : |(4199700071/10000000000 : ℝ)|=(4199700071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624069749/2000000000 : ℝ)|^8351 ≤ (10686297887603/50000000000000 : ℝ)^6303
        have hw : |(624069749/2000000000 : ℝ)|=(624069749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1412803657/2500000000 : ℝ)|^8351 ≤ (2347343086173/5000000000000 : ℝ)^6303
        have hw : |(1412803657/2500000000 : ℝ)|=(1412803657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891855769/10000000000 : ℝ)*x 0 + (4815199047/10000000000 : ℝ)*x 1 + (1203356383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891855769/10000000000 : ℝ)^8351 ≤ (1376705789431/12500000000000 : ℝ)^6303 := by
    have hnat : (1891855769 : ℕ)^8351*12500000000000^6303 ≤ 1376705789431^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891855769 10000000000 1376705789431 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815199047/10000000000 : ℝ)^8351 ≤ (18987063227309/50000000000000 : ℝ)^6303 := by
    have hnat : (4815199047 : ℕ)^8351*50000000000000^6303 ≤ 18987063227309^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815199047 10000000000 18987063227309 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203356383/2000000000 : ℝ)^8351 ≤ (10202445443557/20000000000000 : ℝ)^6303 := by
    have hnat : (1203356383 : ℕ)^8351*20000000000000^6303 ≤ 10202445443557^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203356383 2000000000 10202445443557 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891855769/10000000000 : ℝ), (4815199047/10000000000 : ℝ), (1203356383/2000000000 : ℝ)] ![(1376705789431/12500000000000 : ℝ), (18987063227309/50000000000000 : ℝ), (10202445443557/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891855769/10000000000 : ℝ)|^8351 ≤ (1376705789431/12500000000000 : ℝ)^6303
        have hw : |(-1891855769/10000000000 : ℝ)|=(1891855769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815199047/10000000000 : ℝ)|^8351 ≤ (18987063227309/50000000000000 : ℝ)^6303
        have hw : |(4815199047/10000000000 : ℝ)|=(4815199047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203356383/2000000000 : ℝ)|^8351 ≤ (10202445443557/20000000000000 : ℝ)^6303
        have hw : |(1203356383/2000000000 : ℝ)|=(1203356383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034246149/2000000000 : ℝ)*x 0 + (-1379781867/10000000000 : ℝ)*x 1 + (6016781723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034246149/2000000000 : ℝ)^8351 ≤ (2086909076657/5000000000000 : ℝ)^6303 := by
    have hnat : (1034246149 : ℕ)^8351*5000000000000^6303 ≤ 2086909076657^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034246149 2000000000 2086909076657 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379781867/10000000000 : ℝ)^8351 ≤ (3624796693331/50000000000000 : ℝ)^6303 := by
    have hnat : (1379781867 : ℕ)^8351*50000000000000^6303 ≤ 3624796693331^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379781867 10000000000 3624796693331 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6016781723/10000000000 : ℝ)^8351 ≤ (25506112530511/50000000000000 : ℝ)^6303 := by
    have hnat : (6016781723 : ℕ)^8351*50000000000000^6303 ≤ 25506112530511^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6016781723 10000000000 25506112530511 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034246149/2000000000 : ℝ), (-1379781867/10000000000 : ℝ), (6016781723/10000000000 : ℝ)] ![(2086909076657/5000000000000 : ℝ), (3624796693331/50000000000000 : ℝ), (25506112530511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034246149/2000000000 : ℝ)|^8351 ≤ (2086909076657/5000000000000 : ℝ)^6303
        have hw : |(1034246149/2000000000 : ℝ)|=(1034246149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1379781867/10000000000 : ℝ)|^8351 ≤ (3624796693331/50000000000000 : ℝ)^6303
        have hw : |(-1379781867/10000000000 : ℝ)|=(1379781867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6016781723/10000000000 : ℝ)|^8351 ≤ (25506112530511/50000000000000 : ℝ)^6303
        have hw : |(6016781723/10000000000 : ℝ)|=(6016781723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171230723/10000000000 : ℝ)*x 0 + (6016781791/10000000000 : ℝ)*x 1 + (-43118181/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171230723/10000000000 : ℝ)^8351 ≤ (41738181297877/100000000000000 : ℝ)^6303 := by
    have hnat : (5171230723 : ℕ)^8351*100000000000000^6303 ≤ 41738181297877^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171230723 10000000000 41738181297877 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6016781791/10000000000 : ℝ)^8351 ≤ (12753056456219/25000000000000 : ℝ)^6303 := by
    have hnat : (6016781791 : ℕ)^8351*25000000000000^6303 ≤ 12753056456219^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6016781791 10000000000 12753056456219 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43118181/312500000 : ℝ)^8351 ≤ (90619910807/1250000000000 : ℝ)^6303 := by
    have hnat : (43118181 : ℕ)^8351*1250000000000^6303 ≤ 90619910807^6303*312500000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43118181 312500000 90619910807 1250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171230723/10000000000 : ℝ), (6016781791/10000000000 : ℝ), (-43118181/312500000 : ℝ)] ![(41738181297877/100000000000000 : ℝ), (12753056456219/25000000000000 : ℝ), (90619910807/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171230723/10000000000 : ℝ)|^8351 ≤ (41738181297877/100000000000000 : ℝ)^6303
        have hw : |(5171230723/10000000000 : ℝ)|=(5171230723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6016781791/10000000000 : ℝ)|^8351 ≤ (12753056456219/25000000000000 : ℝ)^6303
        have hw : |(6016781791/10000000000 : ℝ)|=(6016781791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43118181/312500000 : ℝ)|^8351 ≤ (90619910807/1250000000000 : ℝ)^6303
        have hw : |(-43118181/312500000 : ℝ)|=(43118181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s0_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052468897/2500000000 : ℝ)*x 0 + (5585941447/10000000000 : ℝ)*x 1 + (398489921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052468897/2500000000 : ℝ)^8351 ≤ (31782282748813/100000000000000 : ℝ)^6303 := by
    have hnat : (1052468897 : ℕ)^8351*100000000000000^6303 ≤ 31782282748813^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052468897 2500000000 31782282748813 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5585941447/10000000000 : ℝ)^8351 ≤ (11557443258369/25000000000000 : ℝ)^6303 := by
    have hnat : (5585941447 : ℕ)^8351*25000000000000^6303 ≤ 11557443258369^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585941447 10000000000 11557443258369 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398489921/1250000000 : ℝ)^8351 ≤ (21987944196683/100000000000000 : ℝ)^6303 := by
    have hnat : (398489921 : ℕ)^8351*100000000000000^6303 ≤ 21987944196683^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398489921 1250000000 21987944196683 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052468897/2500000000 : ℝ), (5585941447/10000000000 : ℝ), (398489921/1250000000 : ℝ)] ![(31782282748813/100000000000000 : ℝ), (11557443258369/25000000000000 : ℝ), (21987944196683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052468897/2500000000 : ℝ)|^8351 ≤ (31782282748813/100000000000000 : ℝ)^6303
        have hw : |(1052468897/2500000000 : ℝ)|=(1052468897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5585941447/10000000000 : ℝ)|^8351 ≤ (11557443258369/25000000000000 : ℝ)^6303
        have hw : |(5585941447/10000000000 : ℝ)|=(5585941447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398489921/1250000000 : ℝ)|^8351 ≤ (21987944196683/100000000000000 : ℝ)^6303
        have hw : |(398489921/1250000000 : ℝ)|=(398489921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (479/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13877/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4175/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4175 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4175*1^1024 ≤ 0^1024*1^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4175/1024 : ℝ) ≤ (2385280816631629409/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4175 ≤ (2385280816631629409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4175*100000000000000000000^1024 ≤ 2385280816631629409^1024*5^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2385280816631629409 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2385280816631629409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4175 := by
      have hnat : (1 : ℕ)^1024*1^4175 ≤ 1^4175*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102385280816631629409/100000000000000000000 : ℝ) ≤ (5028992139091861/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (102385280816631629409/100000000000000000000 : ℝ)^1024 ≤ (5028992139091861/5000000000000000 : ℝ)^4175 := by
      have hnat : (102385280816631629409 : ℕ)^1024*5000000000000000^4175 ≤ 5028992139091861^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102385280816631629409 100000000000000000000 5028992139091861 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028992139091861/5000000000000000 : ℝ)) (X := (102385280816631629409/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52385280816631629409/50000000000000000000 : ℝ) ≤ (2528992139091861/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (52385280816631629409/50000000000000000000 : ℝ)^1024 ≤ (2528992139091861/2500000000000000 : ℝ)^4175 := by
      have hnat : (52385280816631629409 : ℕ)^1024*2500000000000000^4175 ≤ 2528992139091861^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52385280816631629409 50000000000000000000 2528992139091861 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528992139091861/2500000000000000 : ℝ)) (X := (52385280816631629409/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28992139091861/2000000000000000 : ℝ)*(0 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28992139091861/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2385280816631629409/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28992139091861/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28992139091861/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028992139091861/5000000000000000 : ℝ) by norm_num, show 1+(2385280816631629409/100000000000000000000 : ℝ)+(0 : ℝ)=(102385280816631629409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2385280816631629409/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28992139091861/2000000000000000 : ℝ)*(2/5 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28992139091861/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528992139091861/2500000000000000 : ℝ) by norm_num, show 1+2*(2385280816631629409/100000000000000000000 : ℝ)=(52385280816631629409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28992139091861/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28992139091861/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28992139091861/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28992139091861/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28992139091861/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28992139091861/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1886757241/10000000000 : ℝ)*X 0 0+(1512659871/2500000000 : ℝ)*X 0 1+(4782492477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((220635691/400000000 : ℝ)*X 1 0+(-1307035483/5000000000 : ℝ)*X 1 1+(95649853/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((17237163/31250000 : ℝ)*X 2 0+(956498537/2000000000 : ℝ)*X 2 1+(-261407107/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199700071/10000000000 : ℝ)*X 0 0+(624069749/2000000000 : ℝ)*X 0 1+(1412803657/2500000000 : ℝ)*X 0 2+(4199700071/10000000000 : ℝ)*X 1 0+(624069749/2000000000 : ℝ)*X 1 1+(1412803657/2500000000 : ℝ)*X 1 2+(4199700071/10000000000 : ℝ)*X 2 0+(624069749/2000000000 : ℝ)*X 2 1+(1412803657/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1891855769/10000000000 : ℝ)*X 0 0+(4815199047/10000000000 : ℝ)*X 0 1+(1203356383/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034246149/2000000000 : ℝ)*X 1 0+(-1379781867/10000000000 : ℝ)*X 1 1+(6016781723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171230723/10000000000 : ℝ)*X 2 0+(6016781791/10000000000 : ℝ)*X 2 1+(-43118181/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052468897/2500000000 : ℝ)*X 0 0+(5585941447/10000000000 : ℝ)*X 0 1+(398489921/1250000000 : ℝ)*X 0 2+(1052468897/2500000000 : ℝ)*X 1 0+(5585941447/10000000000 : ℝ)*X 1 1+(398489921/1250000000 : ℝ)*X 1 2+(1052468897/2500000000 : ℝ)*X 2 0+(5585941447/10000000000 : ℝ)*X 2 1+(398489921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137713161604852182296331/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26199607/50000000000000 : ℝ)*(base1) + (1422433011/100000000000000 : ℝ)*(base19) + (10508853/800000000000 : ℝ)*(base23) + (18477169/20000000000000 : ℝ)*(base24) + (42310059/12500000000000 : ℝ)*(upper3) + (591843061135757/100000000000000 : ℝ)*(major0) + (591843061135757/100000000000000 : ℝ)*(major1) + (591843061135757/100000000000000 : ℝ)*(major2) + (394278508673611/50000000000000 : ℝ)*(sp0) + (49284920032197/6250000000000 : ℝ)*(sp1) + (788558736955693/100000000000000 : ℝ)*(sp2) + (7902463742271/2000000000000 : ℝ)*(sp3) + (635600031/20000000000000 : ℝ)*(sp4) + (2556193033/100000000000000 : ℝ)*(sp7) + (395125795705797/100000000000000 : ℝ)*(f.failure) + (788560142948163/100000000000000 : ℝ)*(f.sum) + (262052960926223/100000000000000000000000000000 : ℝ)*base66 + (1254766632026223/200000000000000000000000000000 : ℝ)*base68 + (1197230437826223/200000000000000000000000000000 : ℝ)*base70 + (1539685036026223/200000000000000000000000000000 : ℝ)*base72 + (147352452126223/100000000000000000000000000000 : ℝ)*base74 + (1691347854026223/200000000000000000000000000000 : ℝ)*base76 + (1209448252026223/200000000000000000000000000000 : ℝ)*base78 + (1024534626426223/200000000000000000000000000000 : ℝ)*base80 + (44126111373777/100000000000000000000000000000 : ℝ)*base81 + (610541/78125000000000000000 : ℝ)*base89 + (610541/78125000000000000000 : ℝ)*base91 + (610541/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (636594747753549358881579/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19692229/25000000000000 : ℝ)*(base1) + (1577776619/100000000000000 : ℝ)*(base19) + (1574198399/100000000000000 : ℝ)*(base23) + (170085361/100000000000000 : ℝ)*(upper3) + (46738459/25000000000000 : ℝ)*(upper5) + (624623088553013/100000000000000 : ℝ)*(major0) + (624623088553013/100000000000000 : ℝ)*(major1) + (624623088553013/100000000000000 : ℝ)*(major2) + (3200263633/100000000000000 : ℝ)*(sp1) + (3199699721/100000000000000 : ℝ)*(sp2) + (104029459003753/12500000000000 : ℝ)*(sp4) + (166446163044171/20000000000000 : ℝ)*(sp5) + (208057704840747/25000000000000 : ℝ)*(sp6) + (104252573219437/25000000000000 : ℝ)*(sp7) + (52126296455833/12500000000000 : ℝ)*(f.failure) + (208058898315277/25000000000000 : ℝ)*(f.sum) + (109498361472807/100000000000000000000000000000 : ℝ)*base66 + (47820678527193/200000000000000000000000000000 : ℝ)*base67 + (554174530527193/200000000000000000000000000000 : ℝ)*base69 + (334714800527193/200000000000000000000000000000 : ℝ)*base71 + (392398183972807/100000000000000000000000000000 : ℝ)*base74 + (1810771599527193/200000000000000000000000000000 : ℝ)*base75 + (1974326272807/200000000000000000000000000000 : ℝ)*base78 + (12499625527193/200000000000000000000000000000 : ℝ)*base79 + (243811354472807/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (126729/39062500000000000000 : ℝ)*base90 + (126729/39062500000000000000 : ℝ)*base92 + (126729/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13877/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s1_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045131203/5000000000 : ℝ)*x 0 + (5697257713/10000000000 : ℝ)*x 1 + (100111923/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045131203/5000000000 : ℝ)^8351 ≤ (6284739882771/50000000000000 : ℝ)^6303 := by
    have hnat : (1045131203 : ℕ)^8351*50000000000000^6303 ≤ 6284739882771^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045131203 5000000000 6284739882771 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5697257713/10000000000 : ℝ)^8351 ≤ (11863578084637/25000000000000 : ℝ)^6303 := by
    have hnat : (5697257713 : ℕ)^8351*25000000000000^6303 ≤ 11863578084637^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697257713 10000000000 11863578084637 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100111923/200000000 : ℝ)^8351 ≤ (39976207879689/100000000000000 : ℝ)^6303 := by
    have hnat : (100111923 : ℕ)^8351*100000000000000^6303 ≤ 39976207879689^6303*200000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100111923 200000000 39976207879689 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045131203/5000000000 : ℝ), (5697257713/10000000000 : ℝ), (100111923/200000000 : ℝ)] ![(6284739882771/50000000000000 : ℝ), (11863578084637/25000000000000 : ℝ), (39976207879689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045131203/5000000000 : ℝ)|^8351 ≤ (6284739882771/50000000000000 : ℝ)^6303
        have hw : |(-1045131203/5000000000 : ℝ)|=(1045131203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5697257713/10000000000 : ℝ)|^8351 ≤ (11863578084637/25000000000000 : ℝ)^6303
        have hw : |(5697257713/10000000000 : ℝ)|=(5697257713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100111923/200000000 : ℝ)|^8351 ≤ (39976207879689/100000000000000 : ℝ)^6303
        have hw : |(100111923/200000000 : ℝ)|=(100111923/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418245273/10000000000 : ℝ)*x 0 + (-2463218537/10000000000 : ℝ)*x 1 + (625699403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418245273/10000000000 : ℝ)^8351 ≤ (44399980787327/100000000000000 : ℝ)^6303 := by
    have hnat : (5418245273 : ℕ)^8351*100000000000000^6303 ≤ 44399980787327^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418245273 10000000000 44399980787327 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463218537/10000000000 : ℝ)^8351 ≤ (15623821119377/100000000000000 : ℝ)^6303 := by
    have hnat : (2463218537 : ℕ)^8351*100000000000000^6303 ≤ 15623821119377^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463218537 10000000000 15623821119377 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625699403/1250000000 : ℝ)^8351 ≤ (9994049520363/25000000000000 : ℝ)^6303 := by
    have hnat : (625699403 : ℕ)^8351*25000000000000^6303 ≤ 9994049520363^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625699403 1250000000 9994049520363 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418245273/10000000000 : ℝ), (-2463218537/10000000000 : ℝ), (625699403/1250000000 : ℝ)] ![(44399980787327/100000000000000 : ℝ), (15623821119377/100000000000000 : ℝ), (9994049520363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418245273/10000000000 : ℝ)|^8351 ≤ (44399980787327/100000000000000 : ℝ)^6303
        have hw : |(5418245273/10000000000 : ℝ)|=(5418245273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2463218537/10000000000 : ℝ)|^8351 ≤ (15623821119377/100000000000000 : ℝ)^6303
        have hw : |(-2463218537/10000000000 : ℝ)|=(2463218537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625699403/1250000000 : ℝ)|^8351 ≤ (9994049520363/25000000000000 : ℝ)^6303
        have hw : |(625699403/1250000000 : ℝ)|=(625699403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418247369/10000000000 : ℝ)*x 0 + (1251398333/2500000000 : ℝ)*x 1 + (-2463218211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418247369/10000000000 : ℝ)^8351 ≤ (22200001771943/50000000000000 : ℝ)^6303 := by
    have hnat : (5418247369 : ℕ)^8351*50000000000000^6303 ≤ 22200001771943^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418247369 10000000000 22200001771943 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251398333/2500000000 : ℝ)^8351 ≤ (3997617806173/10000000000000 : ℝ)^6303 := by
    have hnat : (1251398333 : ℕ)^8351*10000000000000^6303 ≤ 3997617806173^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251398333 2500000000 3997617806173 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2463218211/10000000000 : ℝ)^8351 ≤ (15623818379739/100000000000000 : ℝ)^6303 := by
    have hnat : (2463218211 : ℕ)^8351*100000000000000^6303 ≤ 15623818379739^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463218211 10000000000 15623818379739 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418247369/10000000000 : ℝ), (1251398333/2500000000 : ℝ), (-2463218211/10000000000 : ℝ)] ![(22200001771943/50000000000000 : ℝ), (3997617806173/10000000000000 : ℝ), (15623818379739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418247369/10000000000 : ℝ)|^8351 ≤ (22200001771943/50000000000000 : ℝ)^6303
        have hw : |(5418247369/10000000000 : ℝ)|=(5418247369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251398333/2500000000 : ℝ)|^8351 ≤ (3997617806173/10000000000000 : ℝ)^6303
        have hw : |(1251398333/2500000000 : ℝ)|=(1251398333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2463218211/10000000000 : ℝ)|^8351 ≤ (15623818379739/100000000000000 : ℝ)^6303
        have hw : |(-2463218211/10000000000 : ℝ)|=(2463218211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2158040037/5000000000 : ℝ)*x 0 + (230001703/625000000 : ℝ)*x 1 + (2530192877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158040037/5000000000 : ℝ)^8351 ≤ (8212229681749/25000000000000 : ℝ)^6303 := by
    have hnat : (2158040037 : ℕ)^8351*25000000000000^6303 ≤ 8212229681749^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158040037 5000000000 8212229681749 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230001703/625000000 : ℝ)^8351 ≤ (26594102503823/100000000000000 : ℝ)^6303 := by
    have hnat : (230001703 : ℕ)^8351*100000000000000^6303 ≤ 26594102503823^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230001703 625000000 26594102503823 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2530192877/5000000000 : ℝ)^8351 ≤ (20278489382777/50000000000000 : ℝ)^6303 := by
    have hnat : (2530192877 : ℕ)^8351*50000000000000^6303 ≤ 20278489382777^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530192877 5000000000 20278489382777 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158040037/5000000000 : ℝ), (230001703/625000000 : ℝ), (2530192877/5000000000 : ℝ)] ![(8212229681749/25000000000000 : ℝ), (26594102503823/100000000000000 : ℝ), (20278489382777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158040037/5000000000 : ℝ)|^8351 ≤ (8212229681749/25000000000000 : ℝ)^6303
        have hw : |(2158040037/5000000000 : ℝ)|=(2158040037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(230001703/625000000 : ℝ)|^8351 ≤ (26594102503823/100000000000000 : ℝ)^6303
        have hw : |(230001703/625000000 : ℝ)|=(230001703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2530192877/5000000000 : ℝ)|^8351 ≤ (20278489382777/50000000000000 : ℝ)^6303
        have hw : |(2530192877/5000000000 : ℝ)|=(2530192877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045525503/5000000000 : ℝ)*x 0 + (2507491401/5000000000 : ℝ)*x 1 + (5687682907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045525503/5000000000 : ℝ)^8351 ≤ (12575763112749/100000000000000 : ℝ)^6303 := by
    have hnat : (1045525503 : ℕ)^8351*100000000000000^6303 ≤ 12575763112749^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045525503 5000000000 12575763112749 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507491401/5000000000 : ℝ)^8351 ≤ (20037780317351/50000000000000 : ℝ)^6303 := by
    have hnat : (2507491401 : ℕ)^8351*50000000000000^6303 ≤ 20037780317351^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507491401 5000000000 20037780317351 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5687682907/10000000000 : ℝ)^8351 ≤ (23674338121471/50000000000000 : ℝ)^6303 := by
    have hnat : (5687682907 : ℕ)^8351*50000000000000^6303 ≤ 23674338121471^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687682907 10000000000 23674338121471 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045525503/5000000000 : ℝ), (2507491401/5000000000 : ℝ), (5687682907/10000000000 : ℝ)] ![(12575763112749/100000000000000 : ℝ), (20037780317351/50000000000000 : ℝ), (23674338121471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045525503/5000000000 : ℝ)|^8351 ≤ (12575763112749/100000000000000 : ℝ)^6303
        have hw : |(-1045525503/5000000000 : ℝ)|=(1045525503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507491401/5000000000 : ℝ)|^8351 ≤ (20037780317351/50000000000000 : ℝ)^6303
        have hw : |(2507491401/5000000000 : ℝ)|=(2507491401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5687682907/10000000000 : ℝ)|^8351 ≤ (23674338121471/50000000000000 : ℝ)^6303
        have hw : |(5687682907/10000000000 : ℝ)|=(5687682907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620386971/5000000000 : ℝ)*x 0 + (-1781127073/10000000000 : ℝ)*x 1 + (2843843187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620386971/5000000000 : ℝ)^8351 ≤ (10620870074487/25000000000000 : ℝ)^6303 := by
    have hnat : (2620386971 : ℕ)^8351*25000000000000^6303 ≤ 10620870074487^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620386971 5000000000 10620870074487 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781127073/10000000000 : ℝ)^8351 ≤ (10167805204467/100000000000000 : ℝ)^6303 := by
    have hnat : (1781127073 : ℕ)^8351*100000000000000^6303 ≤ 10167805204467^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781127073 10000000000 10167805204467 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843843187/5000000000 : ℝ)^8351 ≤ (47348714482911/100000000000000 : ℝ)^6303 := by
    have hnat : (2843843187 : ℕ)^8351*100000000000000^6303 ≤ 47348714482911^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843843187 5000000000 47348714482911 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620386971/5000000000 : ℝ), (-1781127073/10000000000 : ℝ), (2843843187/5000000000 : ℝ)] ![(10620870074487/25000000000000 : ℝ), (10167805204467/100000000000000 : ℝ), (47348714482911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620386971/5000000000 : ℝ)|^8351 ≤ (10620870074487/25000000000000 : ℝ)^6303
        have hw : |(2620386971/5000000000 : ℝ)|=(2620386971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781127073/10000000000 : ℝ)|^8351 ≤ (10167805204467/100000000000000 : ℝ)^6303
        have hw : |(-1781127073/10000000000 : ℝ)|=(1781127073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843843187/5000000000 : ℝ)|^8351 ≤ (47348714482911/100000000000000 : ℝ)^6303
        have hw : |(2843843187/5000000000 : ℝ)|=(2843843187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620386437/5000000000 : ℝ)*x 0 + (5687687941/10000000000 : ℝ)*x 1 + (-356225261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620386437/5000000000 : ℝ)^8351 ≤ (42483468827323/100000000000000 : ℝ)^6303 := by
    have hnat : (2620386437 : ℕ)^8351*100000000000000^6303 ≤ 42483468827323^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620386437 5000000000 42483468827323 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687687941/10000000000 : ℝ)^8351 ≤ (11837182941613/25000000000000 : ℝ)^6303 := by
    have hnat : (5687687941 : ℕ)^8351*25000000000000^6303 ≤ 11837182941613^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687687941 10000000000 11837182941613 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356225261/2000000000 : ℝ)^8351 ≤ (10167799395691/100000000000000 : ℝ)^6303 := by
    have hnat : (356225261 : ℕ)^8351*100000000000000^6303 ≤ 10167799395691^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356225261 2000000000 10167799395691 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620386437/5000000000 : ℝ), (5687687941/10000000000 : ℝ), (-356225261/2000000000 : ℝ)] ![(42483468827323/100000000000000 : ℝ), (11837182941613/25000000000000 : ℝ), (10167799395691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620386437/5000000000 : ℝ)|^8351 ≤ (42483468827323/100000000000000 : ℝ)^6303
        have hw : |(2620386437/5000000000 : ℝ)|=(2620386437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687687941/10000000000 : ℝ)|^8351 ≤ (11837182941613/25000000000000 : ℝ)^6303
        have hw : |(5687687941/10000000000 : ℝ)|=(5687687941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356225261/2000000000 : ℝ)|^8351 ≤ (10167799395691/100000000000000 : ℝ)^6303
        have hw : |(-356225261/2000000000 : ℝ)|=(356225261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079410583/2500000000 : ℝ)*x 0 + (63020679/125000000 : ℝ)*x 1 + (1849563587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079410583/2500000000 : ℝ)^8351 ≤ (4108084137189/12500000000000 : ℝ)^6303 := by
    have hnat : (1079410583 : ℕ)^8351*12500000000000^6303 ≤ 4108084137189^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079410583 2500000000 4108084137189 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63020679/125000000 : ℝ)^8351 ≤ (39412299003/97656250000 : ℝ)^6303 := by
    have hnat : (63020679 : ℕ)^8351*97656250000^6303 ≤ 39412299003^6303*125000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63020679 125000000 39412299003 97656250000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1849563587/5000000000 : ℝ)^8351 ≤ (3347141589539/12500000000000 : ℝ)^6303 := by
    have hnat : (1849563587 : ℕ)^8351*12500000000000^6303 ≤ 3347141589539^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849563587 5000000000 3347141589539 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079410583/2500000000 : ℝ), (63020679/125000000 : ℝ), (1849563587/5000000000 : ℝ)] ![(4108084137189/12500000000000 : ℝ), (39412299003/97656250000 : ℝ), (3347141589539/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079410583/2500000000 : ℝ)|^8351 ≤ (4108084137189/12500000000000 : ℝ)^6303
        have hw : |(1079410583/2500000000 : ℝ)|=(1079410583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63020679/125000000 : ℝ)|^8351 ≤ (39412299003/97656250000 : ℝ)^6303
        have hw : |(63020679/125000000 : ℝ)|=(63020679/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1849563587/5000000000 : ℝ)|^8351 ≤ (3347141589539/12500000000000 : ℝ)^6303
        have hw : |(1849563587/5000000000 : ℝ)|=(1849563587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_8 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (563449/1000000000 : ℝ)*x 0 + (5490448971/10000000000 : ℝ)*x 1 + (6351825129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563449/1000000000 : ℝ)^8351 ≤ (4955953469/100000000000000 : ℝ)^6303 := by
    have hnat : (563449 : ℕ)^8351*100000000000000^6303 ≤ 4955953469^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563449 1000000000 4955953469 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490448971/10000000000 : ℝ)^8351 ≤ (45185598312219/100000000000000 : ℝ)^6303 := by
    have hnat : (5490448971 : ℕ)^8351*100000000000000^6303 ≤ 45185598312219^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490448971 10000000000 45185598312219 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6351825129/10000000000 : ℝ)^8351 ≤ (27404722858011/50000000000000 : ℝ)^6303 := by
    have hnat : (6351825129 : ℕ)^8351*50000000000000^6303 ≤ 27404722858011^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6351825129 10000000000 27404722858011 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(563449/1000000000 : ℝ), (5490448971/10000000000 : ℝ), (6351825129/10000000000 : ℝ)] ![(4955953469/100000000000000 : ℝ), (45185598312219/100000000000000 : ℝ), (27404722858011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(563449/1000000000 : ℝ)|^8351 ≤ (4955953469/100000000000000 : ℝ)^6303
        have hw : |(563449/1000000000 : ℝ)|=(563449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490448971/10000000000 : ℝ)|^8351 ≤ (45185598312219/100000000000000 : ℝ)^6303
        have hw : |(5490448971/10000000000 : ℝ)|=(5490448971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6351825129/10000000000 : ℝ)|^8351 ≤ (27404722858011/50000000000000 : ℝ)^6303
        have hw : |(6351825129/10000000000 : ℝ)|=(6351825129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_9 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (196632313/2000000000 : ℝ)*x 0 + (-1099786329/2500000000 : ℝ)*x 1 + (6944318959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196632313/2000000000 : ℝ)^8351 ≤ (4627046871977/100000000000000 : ℝ)^6303 := by
    have hnat : (196632313 : ℕ)^8351*100000000000000^6303 ≤ 4627046871977^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196632313 2000000000 4627046871977 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099786329/2500000000 : ℝ)^8351 ≤ (16844568439161/50000000000000 : ℝ)^6303 := by
    have hnat : (1099786329 : ℕ)^8351*50000000000000^6303 ≤ 16844568439161^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099786329 2500000000 16844568439161 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6944318959/10000000000 : ℝ)^8351 ≤ (61683816234933/100000000000000 : ℝ)^6303 := by
    have hnat : (6944318959 : ℕ)^8351*100000000000000^6303 ≤ 61683816234933^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6944318959 10000000000 61683816234933 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(196632313/2000000000 : ℝ), (-1099786329/2500000000 : ℝ), (6944318959/10000000000 : ℝ)] ![(4627046871977/100000000000000 : ℝ), (16844568439161/50000000000000 : ℝ), (61683816234933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(196632313/2000000000 : ℝ)|^8351 ≤ (4627046871977/100000000000000 : ℝ)^6303
        have hw : |(196632313/2000000000 : ℝ)|=(196632313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099786329/2500000000 : ℝ)|^8351 ≤ (16844568439161/50000000000000 : ℝ)^6303
        have hw : |(-1099786329/2500000000 : ℝ)|=(1099786329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6944318959/10000000000 : ℝ)|^8351 ≤ (61683816234933/100000000000000 : ℝ)^6303
        have hw : |(6944318959/10000000000 : ℝ)|=(6944318959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_10 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (983154319/10000000000 : ℝ)*x 0 + (3472150771/5000000000 : ℝ)*x 1 + (-4399169971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983154319/10000000000 : ℝ)^8351 ≤ (4627001689713/100000000000000 : ℝ)^6303 := by
    have hnat : (983154319 : ℕ)^8351*100000000000000^6303 ≤ 4627001689713^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983154319 10000000000 4627001689713 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3472150771/5000000000 : ℝ)^8351 ≤ (61683611257559/100000000000000 : ℝ)^6303 := by
    have hnat : (3472150771 : ℕ)^8351*100000000000000^6303 ≤ 61683611257559^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472150771 5000000000 61683611257559 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399169971/10000000000 : ℝ)^8351 ≤ (33689387038487/100000000000000 : ℝ)^6303 := by
    have hnat : (4399169971 : ℕ)^8351*100000000000000^6303 ≤ 33689387038487^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399169971 10000000000 33689387038487 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(983154319/10000000000 : ℝ), (3472150771/5000000000 : ℝ), (-4399169971/10000000000 : ℝ)] ![(4627001689713/100000000000000 : ℝ), (61683611257559/100000000000000 : ℝ), (33689387038487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(983154319/10000000000 : ℝ)|^8351 ≤ (4627001689713/100000000000000 : ℝ)^6303
        have hw : |(983154319/10000000000 : ℝ)|=(983154319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3472150771/5000000000 : ℝ)|^8351 ≤ (61683611257559/100000000000000 : ℝ)^6303
        have hw : |(3472150771/5000000000 : ℝ)|=(3472150771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4399169971/10000000000 : ℝ)|^8351 ≤ (33689387038487/100000000000000 : ℝ)^6303
        have hw : |(-4399169971/10000000000 : ℝ)|=(4399169971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s1_11 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (957025657/5000000000 : ℝ)*x 0 + (1161617587/2000000000 : ℝ)*x 1 + (5020461379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957025657/5000000000 : ℝ)^8351 ≤ (5592585161119/50000000000000 : ℝ)^6303 := by
    have hnat : (957025657 : ℕ)^8351*50000000000000^6303 ≤ 5592585161119^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957025657 5000000000 5592585161119 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161617587/2000000000 : ℝ)^8351 ≤ (6085156655973/12500000000000 : ℝ)^6303 := by
    have hnat : (1161617587 : ℕ)^8351*12500000000000^6303 ≤ 6085156655973^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161617587 2000000000 6085156655973 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020461379/10000000000 : ℝ)^8351 ≤ (40133576417723/100000000000000 : ℝ)^6303 := by
    have hnat : (5020461379 : ℕ)^8351*100000000000000^6303 ≤ 40133576417723^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020461379 10000000000 40133576417723 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957025657/5000000000 : ℝ), (1161617587/2000000000 : ℝ), (5020461379/10000000000 : ℝ)] ![(5592585161119/50000000000000 : ℝ), (6085156655973/12500000000000 : ℝ), (40133576417723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957025657/5000000000 : ℝ)|^8351 ≤ (5592585161119/50000000000000 : ℝ)^6303
        have hw : |(957025657/5000000000 : ℝ)|=(957025657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1161617587/2000000000 : ℝ)|^8351 ≤ (6085156655973/12500000000000 : ℝ)^6303
        have hw : |(1161617587/2000000000 : ℝ)|=(1161617587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020461379/10000000000 : ℝ)|^8351 ≤ (40133576417723/100000000000000 : ℝ)^6303
        have hw : |(5020461379/10000000000 : ℝ)|=(5020461379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13877/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5739/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4073/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13877/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13877/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13877/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13877/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13877/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13877/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (479/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (34864509773/100000000000000000000 : ℝ) := by
    have hpowers : (479/100000 : ℝ)^4175 ≤ (34864509773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (479 : ℕ)^4175*100000000000000000000^1024 ≤ 34864509773^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        479 100000 34864509773 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (479/100000 : ℝ)) (X := (34864509773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13877/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (537471913536800801/100000000000000000000 : ℝ) := by
    have hpowers : (13877/50000 : ℝ)^4175 ≤ (537471913536800801/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13877 : ℕ)^4175*100000000000000000000^1024 ≤ 537471913536800801^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13877 50000 537471913536800801 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13877/50000 : ℝ)) (X := (537471913536800801/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000034864509773/50000000000000000000 : ℝ) ≤ (62500000010689/62500000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50000000034864509773/50000000000000000000 : ℝ)^1024 ≤ (62500000010689/62500000000000 : ℝ)^4175 := by
      have hnat : (50000000034864509773 : ℕ)^1024*62500000000000^4175 ≤ 62500000010689^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000034864509773 50000000000000000000 62500000010689 62500000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500000010689/62500000000000 : ℝ)) (X := (50000000034864509773/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50268735974200655287/50000000000000000000 : ℝ) ≤ (10013155891990909/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50268735974200655287/50000000000000000000 : ℝ)^1024 ≤ (10013155891990909/10000000000000000 : ℝ)^4175 := by
      have hnat : (50268735974200655287 : ℕ)^1024*10000000000000000^4175 ≤ 10013155891990909^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50268735974200655287 50000000000000000000 10013155891990909 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013155891990909/10000000000000000 : ℝ)) (X := (50268735974200655287/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50537471913536800801/50000000000000000000 : ℝ) ≤ (5013155891135789/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50537471913536800801/50000000000000000000 : ℝ)^1024 ≤ (5013155891135789/5000000000000000 : ℝ)^4175 := by
      have hnat : (50537471913536800801 : ℕ)^1024*5000000000000000^4175 ≤ 5013155891135789^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50537471913536800801 50000000000000000000 5013155891135789 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013155891135789/5000000000000000 : ℝ)) (X := (50537471913536800801/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(34864509773/100000000000000000000 : ℝ) ≤ ((136368698351878957549/136375000000000000000 : ℝ)+2*(13155890280669/2727500000000000 : ℝ)*(479/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (136368698351878957549/136375000000000000000 : ℝ)+2*(13155890280669/2727500000000000 : ℝ)*(479/100000 : ℝ)=(62500000010689/62500000000000 : ℝ) by norm_num, show 1+2*(34864509773/100000000000000000000 : ℝ)=(50000000034864509773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(537471913536800801/100000000000000000000 : ℝ)+(34864509773/100000000000000000000 : ℝ) ≤ ((136368698351878957549/136375000000000000000 : ℝ)+(13155890280669/2727500000000000 : ℝ)*((13877/50000 : ℝ)+(479/100000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (136368698351878957549/136375000000000000000 : ℝ)+(13155890280669/2727500000000000 : ℝ)*((13877/50000 : ℝ)+(479/100000 : ℝ))=(10013155891990909/10000000000000000 : ℝ) by norm_num, show 1+(537471913536800801/100000000000000000000 : ℝ)+(34864509773/100000000000000000000 : ℝ)=(50268735974200655287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(537471913536800801/100000000000000000000 : ℝ) ≤ ((136368698351878957549/136375000000000000000 : ℝ)+2*(13155890280669/2727500000000000 : ℝ)*(13877/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (136368698351878957549/136375000000000000000 : ℝ)+2*(13155890280669/2727500000000000 : ℝ)*(13877/50000 : ℝ)=(5013155891135789/5000000000000000 : ℝ) by norm_num, show 1+2*(537471913536800801/100000000000000000000 : ℝ)=(50537471913536800801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (136368698351878957549/136375000000000000000 : ℝ)*(X 1 0+X 2 0)+(13155890280669/2727500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (479/100000 : ℝ)) (hi := (13877/50000 : ℝ)) (c := (136368698351878957549/136375000000000000000 : ℝ)) (alpha := (13155890280669/2727500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (136368698351878957549/136375000000000000000 : ℝ)*(X 0 1+X 2 1)+(13155890280669/2727500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (479/100000 : ℝ)) (hi := (13877/50000 : ℝ)) (c := (136368698351878957549/136375000000000000000 : ℝ)) (alpha := (13155890280669/2727500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (136368698351878957549/136375000000000000000 : ℝ)*(X 0 2+X 1 2)+(13155890280669/2727500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (479/100000 : ℝ)) (hi := (13877/50000 : ℝ)) (c := (136368698351878957549/136375000000000000000 : ℝ)) (alpha := (13155890280669/2727500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045131203/5000000000 : ℝ)*X 0 0+(5697257713/10000000000 : ℝ)*X 0 1+(100111923/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418245273/10000000000 : ℝ)*X 1 0+(-2463218537/10000000000 : ℝ)*X 1 1+(625699403/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5418247369/10000000000 : ℝ)*X 2 0+(1251398333/2500000000 : ℝ)*X 2 1+(-2463218211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158040037/5000000000 : ℝ)*X 0 0+(230001703/625000000 : ℝ)*X 0 1+(2530192877/5000000000 : ℝ)*X 0 2+(2158040037/5000000000 : ℝ)*X 1 0+(230001703/625000000 : ℝ)*X 1 1+(2530192877/5000000000 : ℝ)*X 1 2+(2158040037/5000000000 : ℝ)*X 2 0+(230001703/625000000 : ℝ)*X 2 1+(2530192877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045525503/5000000000 : ℝ)*X 0 0+(2507491401/5000000000 : ℝ)*X 0 1+(5687682907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2620386971/5000000000 : ℝ)*X 1 0+(-1781127073/10000000000 : ℝ)*X 1 1+(2843843187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620386437/5000000000 : ℝ)*X 2 0+(5687687941/10000000000 : ℝ)*X 2 1+(-356225261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079410583/2500000000 : ℝ)*X 0 0+(63020679/125000000 : ℝ)*X 0 1+(1849563587/5000000000 : ℝ)*X 0 2+(1079410583/2500000000 : ℝ)*X 1 0+(63020679/125000000 : ℝ)*X 1 1+(1849563587/5000000000 : ℝ)*X 1 2+(1079410583/2500000000 : ℝ)*X 2 0+(63020679/125000000 : ℝ)*X 2 1+(1849563587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((563449/1000000000 : ℝ)*X 0 0+(5490448971/10000000000 : ℝ)*X 0 1+(6351825129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((196632313/2000000000 : ℝ)*X 1 0+(-1099786329/2500000000 : ℝ)*X 1 1+(6944318959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((983154319/10000000000 : ℝ)*X 2 0+(3472150771/5000000000 : ℝ)*X 2 1+(-4399169971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((957025657/5000000000 : ℝ)*X 0 0+(1161617587/2000000000 : ℝ)*X 0 1+(5020461379/10000000000 : ℝ)*X 0 2+(957025657/5000000000 : ℝ)*X 1 0+(1161617587/2000000000 : ℝ)*X 1 1+(5020461379/10000000000 : ℝ)*X 1 2+(957025657/5000000000 : ℝ)*X 2 0+(1161617587/2000000000 : ℝ)*X 2 1+(5020461379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (668328696477707185664500557/340937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (391588337/100000000000000 : ℝ)*(lower2) + (54256101499469/5000000000000 : ℝ)*(major0) + (54256101499469/5000000000000 : ℝ)*(major1) + (54256101499469/5000000000000 : ℝ)*(major2) + (45181036574549/3125000000000 : ℝ)*(sp0) + (722896138084381/50000000000000 : ℝ)*(sp1) + (144579089523579/10000000000000 : ℝ)*(sp2) + (362224040800729/50000000000000 : ℝ)*(sp3) + (1257030497/50000000000000 : ℝ)*(sp4) + (176766791/6250000000000 : ℝ)*(sp5) + (1431919/32000000000 : ℝ)*(sp6) + (72501143/12500000000000 : ℝ)*(sp9) + (157231949/50000000000000 : ℝ)*(sp10) + (114294243/50000000000000 : ℝ)*(sp11) + (90556038773743/12500000000000 : ℝ)*(f.failure) + (722897842223281/50000000000000 : ℝ)*(f.sum) + (19948297139757/3409375000000000000000000000 : ℝ)*base66 + (1952654619418841481/681875000000000000000000000000000 : ℝ)*base67 + (2835512877082591481/681875000000000000000000000000000 : ℝ)*base69 + (4157335372051341481/681875000000000000000000000000000 : ℝ)*base71 + (10837178436039/6818750000000000000000000000 : ℝ)*base74 + (2852795428538841481/681875000000000000000000000000000 : ℝ)*base75 + (943366731038658519/681875000000000000000000000000000 : ℝ)*base78 + (897928045024283519/681875000000000000000000000000000 : ℝ)*base80 + (33728347127219/27275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2699/2441406250000000000 : ℝ)*base90 + (2699/2441406250000000000 : ℝ)*base92 + (2699/2441406250000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23346400554520321672835931831/3409375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (557853131103709/50000000000000 : ℝ)*(major0) + (557853131103709/50000000000000 : ℝ)*(major1) + (557853131103709/50000000000000 : ℝ)*(major2) + (4866084471/100000000000000 : ℝ)*(sp1) + (7666144219/100000000000000 : ℝ)*(sp2) + (1205141133/100000000000000 : ℝ)*(sp3) + (743270882505661/50000000000000 : ℝ)*(sp4) + (1486540056369199/100000000000000 : ℝ)*(sp5) + (1486537512480497/100000000000000 : ℝ)*(sp6) + (744864119798809/100000000000000 : ℝ)*(sp7) + (3600067517/100000000000000 : ℝ)*(sp8) + (44262517/10000000000000 : ℝ)*(sp9) + (46613531/25000000000000 : ℝ)*(sp10) + (401534787/25000000000000 : ℝ)*(sp11) + (74486693107909/10000000000000 : ℝ)*(f.failure) + (1486545365078839/100000000000000 : ℝ)*(f.sum) + (186618217820071/68187500000000000000000000000 : ℝ)*base65 + (51604704689262249241/6818750000000000000000000000000000 : ℝ)*base67 + (57743677191312249241/6818750000000000000000000000000000 : ℝ)*base69 + (21071497981024749241/6818750000000000000000000000000000 : ℝ)*base71 + (41025932930087/8523437500000000000000000000 : ℝ)*base73 + (23191357982668499241/6818750000000000000000000000000000 : ℝ)*base75 + (19037801334062249241/6818750000000000000000000000000000 : ℝ)*base77 + (10976312394749749241/6818750000000000000000000000000000 : ℝ)*base79 + (51243817964049/17046875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (95723/7812500000000000000 : ℝ)*base90 + (95723/7812500000000000000 : ℝ)*base92 + (95723/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13877/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s2_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071320729/5000000000 : ℝ)*x 0 + (2753893413/5000000000 : ℝ)*x 1 + (5161744531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071320729/5000000000 : ℝ)^8351 ≤ (12988485469529/100000000000000 : ℝ)^6303 := by
    have hnat : (1071320729 : ℕ)^8351*100000000000000^6303 ≤ 12988485469529^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071320729 5000000000 12988485469529 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753893413/5000000000 : ℝ)^8351 ≤ (45374746119231/100000000000000 : ℝ)^6303 := by
    have hnat : (2753893413 : ℕ)^8351*100000000000000^6303 ≤ 45374746119231^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753893413 5000000000 45374746119231 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161744531/10000000000 : ℝ)^8351 ≤ (41636768400559/100000000000000 : ℝ)^6303 := by
    have hnat : (5161744531 : ℕ)^8351*100000000000000^6303 ≤ 41636768400559^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161744531 10000000000 41636768400559 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071320729/5000000000 : ℝ), (2753893413/5000000000 : ℝ), (5161744531/10000000000 : ℝ)] ![(12988485469529/100000000000000 : ℝ), (45374746119231/100000000000000 : ℝ), (41636768400559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071320729/5000000000 : ℝ)|^8351 ≤ (12988485469529/100000000000000 : ℝ)^6303
        have hw : |(-1071320729/5000000000 : ℝ)|=(1071320729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753893413/5000000000 : ℝ)|^8351 ≤ (45374746119231/100000000000000 : ℝ)^6303
        have hw : |(2753893413/5000000000 : ℝ)|=(2753893413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161744531/10000000000 : ℝ)|^8351 ≤ (41636768400559/100000000000000 : ℝ)^6303
        have hw : |(5161744531/10000000000 : ℝ)|=(5161744531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686589417/5000000000 : ℝ)*x 0 + (-1161218647/5000000000 : ℝ)*x 1 + (5161747003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686589417/5000000000 : ℝ)^8351 ≤ (21955675361683/50000000000000 : ℝ)^6303 := by
    have hnat : (2686589417 : ℕ)^8351*50000000000000^6303 ≤ 21955675361683^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686589417 5000000000 21955675361683 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161218647/5000000000 : ℝ)^8351 ≤ (14451854446273/100000000000000 : ℝ)^6303 := by
    have hnat : (1161218647 : ℕ)^8351*100000000000000^6303 ≤ 14451854446273^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161218647 5000000000 14451854446273 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161747003/10000000000 : ℝ)^8351 ≤ (4163679481979/10000000000000 : ℝ)^6303 := by
    have hnat : (5161747003 : ℕ)^8351*10000000000000^6303 ≤ 4163679481979^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161747003 10000000000 4163679481979 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686589417/5000000000 : ℝ), (-1161218647/5000000000 : ℝ), (5161747003/10000000000 : ℝ)] ![(21955675361683/50000000000000 : ℝ), (14451854446273/100000000000000 : ℝ), (4163679481979/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686589417/5000000000 : ℝ)|^8351 ≤ (21955675361683/50000000000000 : ℝ)^6303
        have hw : |(2686589417/5000000000 : ℝ)|=(2686589417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1161218647/5000000000 : ℝ)|^8351 ≤ (14451854446273/100000000000000 : ℝ)^6303
        have hw : |(-1161218647/5000000000 : ℝ)|=(1161218647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161747003/10000000000 : ℝ)|^8351 ≤ (4163679481979/10000000000000 : ℝ)^6303
        have hw : |(5161747003/10000000000 : ℝ)|=(5161747003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373179089/10000000000 : ℝ)*x 0 + (516174647/1000000000 : ℝ)*x 1 + (-46448753/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373179089/10000000000 : ℝ)^8351 ≤ (2744459592777/6250000000000 : ℝ)^6303 := by
    have hnat : (5373179089 : ℕ)^8351*6250000000000^6303 ≤ 2744459592777^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373179089 10000000000 2744459592777 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516174647/1000000000 : ℝ)^8351 ≤ (4163678912341/10000000000000 : ℝ)^6303 := by
    have hnat : (516174647 : ℕ)^8351*10000000000000^6303 ≤ 4163678912341^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516174647 1000000000 4163678912341 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46448753/200000000 : ℝ)^8351 ≤ (7225928690679/50000000000000 : ℝ)^6303 := by
    have hnat : (46448753 : ℕ)^8351*50000000000000^6303 ≤ 7225928690679^6303*200000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46448753 200000000 7225928690679 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373179089/10000000000 : ℝ), (516174647/1000000000 : ℝ), (-46448753/200000000 : ℝ)] ![(2744459592777/6250000000000 : ℝ), (4163678912341/10000000000000 : ℝ), (7225928690679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373179089/10000000000 : ℝ)|^8351 ≤ (2744459592777/6250000000000 : ℝ)^6303
        have hw : |(5373179089/10000000000 : ℝ)|=(5373179089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516174647/1000000000 : ℝ)|^8351 ≤ (4163678912341/10000000000000 : ℝ)^6303
        have hw : |(516174647/1000000000 : ℝ)|=(516174647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46448753/200000000 : ℝ)|^8351 ≤ (7225928690679/50000000000000 : ℝ)^6303
        have hw : |(-46448753/200000000 : ℝ)|=(46448753/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870410781/2000000000 : ℝ)*x 0 + (502534993/1250000000 : ℝ)*x 1 + (4710878477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870410781/2000000000 : ℝ)^8351 ≤ (33212160706287/100000000000000 : ℝ)^6303 := by
    have hnat : (870410781 : ℕ)^8351*100000000000000^6303 ≤ 33212160706287^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870410781 2000000000 33212160706287 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502534993/1250000000 : ℝ)^8351 ≤ (29899877908497/100000000000000 : ℝ)^6303 := by
    have hnat : (502534993 : ℕ)^8351*100000000000000^6303 ≤ 29899877908497^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502534993 1250000000 29899877908497 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4710878477/10000000000 : ℝ)^8351 ≤ (18443980687051/50000000000000 : ℝ)^6303 := by
    have hnat : (4710878477 : ℕ)^8351*50000000000000^6303 ≤ 18443980687051^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4710878477 10000000000 18443980687051 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870410781/2000000000 : ℝ), (502534993/1250000000 : ℝ), (4710878477/10000000000 : ℝ)] ![(33212160706287/100000000000000 : ℝ), (29899877908497/100000000000000 : ℝ), (18443980687051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870410781/2000000000 : ℝ)|^8351 ≤ (33212160706287/100000000000000 : ℝ)^6303
        have hw : |(870410781/2000000000 : ℝ)|=(870410781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502534993/1250000000 : ℝ)|^8351 ≤ (29899877908497/100000000000000 : ℝ)^6303
        have hw : |(502534993/1250000000 : ℝ)|=(502534993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4710878477/10000000000 : ℝ)|^8351 ≤ (18443980687051/50000000000000 : ℝ)^6303
        have hw : |(4710878477/10000000000 : ℝ)|=(4710878477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428547831/2000000000 : ℝ)*x 0 + (5164104649/10000000000 : ℝ)*x 1 + (137635093/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428547831/2000000000 : ℝ)^8351 ≤ (324731753379/2500000000000 : ℝ)^6303 := by
    have hnat : (428547831 : ℕ)^8351*2500000000000^6303 ≤ 324731753379^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428547831 2000000000 324731753379 2500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164104649/10000000000 : ℝ)^8351 ≤ (2083099688857/5000000000000 : ℝ)^6303 := by
    have hnat : (5164104649 : ℕ)^8351*5000000000000^6303 ≤ 2083099688857^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164104649 10000000000 2083099688857 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137635093/250000000 : ℝ)^8351 ≤ (22674368037539/50000000000000 : ℝ)^6303 := by
    have hnat : (137635093 : ℕ)^8351*50000000000000^6303 ≤ 22674368037539^6303*250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137635093 250000000 22674368037539 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428547831/2000000000 : ℝ), (5164104649/10000000000 : ℝ), (137635093/250000000 : ℝ)] ![(324731753379/2500000000000 : ℝ), (2083099688857/5000000000000 : ℝ), (22674368037539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428547831/2000000000 : ℝ)|^8351 ≤ (324731753379/2500000000000 : ℝ)^6303
        have hw : |(-428547831/2000000000 : ℝ)|=(428547831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164104649/10000000000 : ℝ)|^8351 ≤ (2083099688857/5000000000000 : ℝ)^6303
        have hw : |(5164104649/10000000000 : ℝ)|=(5164104649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137635093/250000000 : ℝ)|^8351 ≤ (22674368037539/50000000000000 : ℝ)^6303
        have hw : |(137635093/250000000 : ℝ)|=(137635093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642642673/5000000000 : ℝ)*x 0 + (-1978779533/10000000000 : ℝ)*x 1 + (5505403711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642642673/5000000000 : ℝ)^8351 ≤ (1074055097347/2500000000000 : ℝ)^6303 := by
    have hnat : (2642642673 : ℕ)^8351*2500000000000^6303 ≤ 1074055097347^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642642673 5000000000 1074055097347 2500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978779533/10000000000 : ℝ)^8351 ≤ (1168906011121/10000000000000 : ℝ)^6303 := by
    have hnat : (1978779533 : ℕ)^8351*10000000000000^6303 ≤ 1168906011121^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978779533 10000000000 1168906011121 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505403711/10000000000 : ℝ)^8351 ≤ (5668591997107/12500000000000 : ℝ)^6303 := by
    have hnat : (5505403711 : ℕ)^8351*12500000000000^6303 ≤ 5668591997107^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505403711 10000000000 5668591997107 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642642673/5000000000 : ℝ), (-1978779533/10000000000 : ℝ), (5505403711/10000000000 : ℝ)] ![(1074055097347/2500000000000 : ℝ), (1168906011121/10000000000000 : ℝ), (5668591997107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642642673/5000000000 : ℝ)|^8351 ≤ (1074055097347/2500000000000 : ℝ)^6303
        have hw : |(2642642673/5000000000 : ℝ)|=(2642642673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978779533/10000000000 : ℝ)|^8351 ≤ (1168906011121/10000000000000 : ℝ)^6303
        have hw : |(-1978779533/10000000000 : ℝ)|=(1978779533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505403711/10000000000 : ℝ)|^8351 ≤ (5668591997107/12500000000000 : ℝ)^6303
        have hw : |(5505403711/10000000000 : ℝ)|=(5505403711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642642729/5000000000 : ℝ)*x 0 + (688175463/1250000000 : ℝ)*x 1 + (-1978779389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642642729/5000000000 : ℝ)^8351 ≤ (21481102550051/50000000000000 : ℝ)^6303 := by
    have hnat : (2642642729 : ℕ)^8351*50000000000000^6303 ≤ 21481102550051^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642642729 5000000000 21481102550051 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688175463/1250000000 : ℝ)^8351 ≤ (45348735900461/100000000000000 : ℝ)^6303 := by
    have hnat : (688175463 : ℕ)^8351*100000000000000^6303 ≤ 45348735900461^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688175463 1250000000 45348735900461 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978779389/10000000000 : ℝ)^8351 ≤ (11689058984179/100000000000000 : ℝ)^6303 := by
    have hnat : (1978779389 : ℕ)^8351*100000000000000^6303 ≤ 11689058984179^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978779389 10000000000 11689058984179 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642642729/5000000000 : ℝ), (688175463/1250000000 : ℝ), (-1978779389/10000000000 : ℝ)] ![(21481102550051/50000000000000 : ℝ), (45348735900461/100000000000000 : ℝ), (11689058984179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642642729/5000000000 : ℝ)|^8351 ≤ (21481102550051/50000000000000 : ℝ)^6303
        have hw : |(2642642729/5000000000 : ℝ)|=(2642642729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688175463/1250000000 : ℝ)|^8351 ≤ (45348735900461/100000000000000 : ℝ)^6303
        have hw : |(688175463/1250000000 : ℝ)|=(688175463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978779389/10000000000 : ℝ)|^8351 ≤ (11689058984179/100000000000000 : ℝ)^6303
        have hw : |(-1978779389/10000000000 : ℝ)|=(1978779389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s2_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176125229/5000000000 : ℝ)*x 0 + (2353085343/5000000000 : ℝ)*x 1 + (161001327/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176125229/5000000000 : ℝ)^8351 ≤ (1037942127123/3125000000000 : ℝ)^6303 := by
    have hnat : (2176125229 : ℕ)^8351*3125000000000^6303 ≤ 1037942127123^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176125229 5000000000 1037942127123 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353085343/5000000000 : ℝ)^8351 ≤ (18419563784123/50000000000000 : ℝ)^6303 := by
    have hnat : (2353085343 : ℕ)^8351*50000000000000^6303 ≤ 18419563784123^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353085343 5000000000 18419563784123 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161001327/400000000 : ℝ)^8351 ≤ (29946724349963/100000000000000 : ℝ)^6303 := by
    have hnat : (161001327 : ℕ)^8351*100000000000000^6303 ≤ 29946724349963^6303*400000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161001327 400000000 29946724349963 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176125229/5000000000 : ℝ), (2353085343/5000000000 : ℝ), (161001327/400000000 : ℝ)] ![(1037942127123/3125000000000 : ℝ), (18419563784123/50000000000000 : ℝ), (29946724349963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176125229/5000000000 : ℝ)|^8351 ≤ (1037942127123/3125000000000 : ℝ)^6303
        have hw : |(2176125229/5000000000 : ℝ)|=(2176125229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2353085343/5000000000 : ℝ)|^8351 ≤ (18419563784123/50000000000000 : ℝ)^6303
        have hw : |(2353085343/5000000000 : ℝ)|=(2353085343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161001327/400000000 : ℝ)|^8351 ≤ (29946724349963/100000000000000 : ℝ)^6303
        have hw : |(161001327/400000000 : ℝ)|=(161001327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4571/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3291/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4073/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4073/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4073/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4073/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4073/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4073/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5739/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (217535961506487/25000000000000000000 : ℝ) := by
    have hpowers : (5739/100000 : ℝ)^4175 ≤ (217535961506487/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5739 : ℕ)^4175*25000000000000000000^1024 ≤ 217535961506487^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5739 100000 217535961506487 25000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5739/100000 : ℝ)) (X := (217535961506487/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4073/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (76065753983554183/50000000000000000000 : ℝ) := by
    have hpowers : (4073/20000 : ℝ)^4175 ≤ (76065753983554183/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4073 : ℕ)^4175*50000000000000000000^1024 ≤ 76065753983554183^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4073 20000 76065753983554183 50000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4073/20000 : ℝ)) (X := (76065753983554183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500217535961506487/12500000000000000000 : ℝ) ≤ (10000042683662123/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (12500217535961506487/12500000000000000000 : ℝ)^1024 ≤ (10000042683662123/10000000000000000 : ℝ)^4175 := by
      have hnat : (12500217535961506487 : ℕ)^1024*10000000000000000^4175 ≤ 10000042683662123^4175*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500217535961506487 12500000000000000000 10000042683662123 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042683662123/10000000000000000 : ℝ)) (X := (12500217535961506487/12500000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50076500825906567157/50000000000000000000 : ℝ) ≤ (2500937624627773/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50076500825906567157/50000000000000000000 : ℝ)^1024 ≤ (2500937624627773/2500000000000000 : ℝ)^4175 := by
      have hnat : (50076500825906567157 : ℕ)^1024*2500000000000000^4175 ≤ 2500937624627773^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076500825906567157 50000000000000000000 2500937624627773 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500937624627773/2500000000000000 : ℝ)) (X := (50076500825906567157/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25076065753983554183/25000000000000000000 : ℝ) ≤ (10007458313360061/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (25076065753983554183/25000000000000000000 : ℝ)^1024 ≤ (10007458313360061/10000000000000000 : ℝ)^4175 := by
      have hnat : (25076065753983554183 : ℕ)^1024*10000000000000000^4175 ≤ 10007458313360061^4175*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25076065753983554183 25000000000000000000 10007458313360061 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007458313360061/10000000000000000 : ℝ)) (X := (25076065753983554183/25000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(217535961506487/25000000000000000000 : ℝ) ≤ ((9138629124525359051/9141250000000000000 : ℝ)+2*(3707814848969/1462600000000000 : ℝ)*(5739/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (9138629124525359051/9141250000000000000 : ℝ)+2*(3707814848969/1462600000000000 : ℝ)*(5739/100000 : ℝ)=(10000042683662123/10000000000000000 : ℝ) by norm_num, show 1+2*(217535961506487/25000000000000000000 : ℝ)=(12500217535961506487/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76065753983554183/50000000000000000000 : ℝ)+(217535961506487/25000000000000000000 : ℝ) ≤ ((9138629124525359051/9141250000000000000 : ℝ)+(3707814848969/1462600000000000 : ℝ)*((4073/20000 : ℝ)+(5739/100000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (9138629124525359051/9141250000000000000 : ℝ)+(3707814848969/1462600000000000 : ℝ)*((4073/20000 : ℝ)+(5739/100000 : ℝ))=(2500937624627773/2500000000000000 : ℝ) by norm_num, show 1+(76065753983554183/50000000000000000000 : ℝ)+(217535961506487/25000000000000000000 : ℝ)=(50076500825906567157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76065753983554183/50000000000000000000 : ℝ) ≤ ((9138629124525359051/9141250000000000000 : ℝ)+2*(3707814848969/1462600000000000 : ℝ)*(4073/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (9138629124525359051/9141250000000000000 : ℝ)+2*(3707814848969/1462600000000000 : ℝ)*(4073/20000 : ℝ)=(10007458313360061/10000000000000000 : ℝ) by norm_num, show 1+2*(76065753983554183/50000000000000000000 : ℝ)=(25076065753983554183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9138629124525359051/9141250000000000000 : ℝ)*(X 1 0+X 2 0)+(3707814848969/1462600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5739/100000 : ℝ)) (hi := (4073/20000 : ℝ)) (c := (9138629124525359051/9141250000000000000 : ℝ)) (alpha := (3707814848969/1462600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9138629124525359051/9141250000000000000 : ℝ)*(X 0 1+X 2 1)+(3707814848969/1462600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5739/100000 : ℝ)) (hi := (4073/20000 : ℝ)) (c := (9138629124525359051/9141250000000000000 : ℝ)) (alpha := (3707814848969/1462600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9138629124525359051/9141250000000000000 : ℝ)*(X 0 2+X 1 2)+(3707814848969/1462600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5739/100000 : ℝ)) (hi := (4073/20000 : ℝ)) (c := (9138629124525359051/9141250000000000000 : ℝ)) (alpha := (3707814848969/1462600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071320729/5000000000 : ℝ)*X 0 0+(2753893413/5000000000 : ℝ)*X 0 1+(5161744531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686589417/5000000000 : ℝ)*X 1 0+(-1161218647/5000000000 : ℝ)*X 1 1+(5161747003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373179089/10000000000 : ℝ)*X 2 0+(516174647/1000000000 : ℝ)*X 2 1+(-46448753/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870410781/2000000000 : ℝ)*X 0 0+(502534993/1250000000 : ℝ)*X 0 1+(4710878477/10000000000 : ℝ)*X 0 2+(870410781/2000000000 : ℝ)*X 1 0+(502534993/1250000000 : ℝ)*X 1 1+(4710878477/10000000000 : ℝ)*X 1 2+(870410781/2000000000 : ℝ)*X 2 0+(502534993/1250000000 : ℝ)*X 2 1+(4710878477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428547831/2000000000 : ℝ)*X 0 0+(5164104649/10000000000 : ℝ)*X 0 1+(137635093/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642642673/5000000000 : ℝ)*X 1 0+(-1978779533/10000000000 : ℝ)*X 1 1+(5505403711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642642729/5000000000 : ℝ)*X 2 0+(688175463/1250000000 : ℝ)*X 2 1+(-1978779389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176125229/5000000000 : ℝ)*X 0 0+(2353085343/5000000000 : ℝ)*X 0 1+(161001327/400000000 : ℝ)*X 0 2+(2176125229/5000000000 : ℝ)*X 1 0+(2353085343/5000000000 : ℝ)*X 1 1+(161001327/400000000 : ℝ)*X 1 2+(2176125229/5000000000 : ℝ)*X 2 0+(2353085343/5000000000 : ℝ)*X 2 1+(161001327/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188644170624340062251193813/22853125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12255797/1562500000000 : ℝ)*(base19) + (139333967/20000000000000 : ℝ)*(base23) + (2205627/5000000000000 : ℝ)*(upper2) + (185286139/50000000000000 : ℝ)*(upper3) + (82463769/50000000000000 : ℝ)*(upper4) + (54223749107827/2500000000000 : ℝ)*(major0) + (54223749107827/2500000000000 : ℝ)*(major1) + (54223749107827/2500000000000 : ℝ)*(major2) + (36123074364503/1250000000000 : ℝ)*(sp0) + (1444933105922071/50000000000000 : ℝ)*(sp1) + (1444933149772657/50000000000000 : ℝ)*(sp2) + (1448024126397123/100000000000000 : ℝ)*(sp3) + (2104705491/10000000000000 : ℝ)*(sp4) + (8530859433/100000000000000 : ℝ)*(sp7) + (362008164314139/25000000000000 : ℝ)*(f.failure) + (57797339924303/2000000000000 : ℝ)*(f.sum) + (5164247980037/1462600000000000000000000000 : ℝ)*base65 + (10887170170598427/22853125000000000000000000000000 : ℝ)*base67 + (99981728723707823/22853125000000000000000000000000 : ℝ)*base70 + (71404341788266401/11426562500000000000000000000000 : ℝ)*base71 + (8846070115813/3656500000000000000000000000 : ℝ)*base73 + (45119759848110927/22853125000000000000000000000000 : ℝ)*base75 + (7098581459096487/5713281250000000000000000000000 : ℝ)*base78 + (170395886599504677/22853125000000000000000000000000 : ℝ)*base79 + (4376890407923/3656500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (37283/19531250000000000000 : ℝ)*base90 + (37283/19531250000000000000 : ℝ)*base92 + (37283/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19344272466715103424550647/4570625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040433969/100000000000000 : ℝ)*(base19) + (577183629/50000000000000 : ℝ)*(base23) + (123727/1250000000000 : ℝ)*(upper2) + (125670063/100000000000000 : ℝ)*(upper3) + (47142799/50000000000000 : ℝ)*(upper5) + (21990570633651/1000000000000 : ℝ)*(major0) + (21990570633651/1000000000000 : ℝ)*(major1) + (21990570633651/1000000000000 : ℝ)*(major2) + (78991857/800000000000 : ℝ)*(sp1) + (1483169609/12500000000000 : ℝ)*(sp2) + (585996250154817/20000000000000 : ℝ)*(sp4) + (292997033635799/10000000000000 : ℝ)*(sp5) + (732492057762489/25000000000000 : ℝ)*(sp6) + (1468132734879319/100000000000000 : ℝ)*(sp7) + (1468132734879319/100000000000000 : ℝ)*(f.failure) + (585996250154817/20000000000000 : ℝ)*(f.sum) + (11880070747961/7313000000000000000000000000 : ℝ)*base66 + (88313757301035201/9141250000000000000000000000000 : ℝ)*base67 + (25926188413362701/9141250000000000000000000000000 : ℝ)*base69 + (54393587000398951/9141250000000000000000000000000 : ℝ)*base71 + (458903494197/114265625000000000000000000 : ℝ)*base73 + (50367824396681451/9141250000000000000000000000000 : ℝ)*base75 + (16632395857673549/9141250000000000000000000000000 : ℝ)*base78 + (73581964139948549/9141250000000000000000000000000 : ℝ)*base80 + (39957835667057/7313000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (643243/78125000000000000000 : ℝ)*base90 + (643243/78125000000000000000 : ℝ)*base92 + (643243/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1158_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1158_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1158_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1158_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

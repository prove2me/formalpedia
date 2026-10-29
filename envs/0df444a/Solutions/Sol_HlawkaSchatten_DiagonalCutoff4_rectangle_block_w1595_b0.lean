-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:44.873846+00:00
-- url     : https://prove2.me/submissions/244eb762-a1ff-474e-ab05-be7c6fbe7808

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
theorem support_rectangle_w1595_s0_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199285041/1250000000 : ℝ)*x 0 + (5857772393/10000000000 : ℝ)*x 1 + (488157587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199285041/1250000000 : ℝ)^4699 ≤ (4779007918443/50000000000000 : ℝ)^3675 := by
    have hnat : (199285041 : ℕ)^4699*50000000000000^3675 ≤ 4779007918443^3675*1250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199285041 1250000000 4779007918443 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5857772393/10000000000 : ℝ)^4699 ≤ (50467710269691/100000000000000 : ℝ)^3675 := by
    have hnat : (5857772393 : ℕ)^4699*100000000000000^3675 ≤ 50467710269691^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857772393 10000000000 50467710269691 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488157587/1000000000 : ℝ)^4699 ≤ (249839211699/625000000000 : ℝ)^3675 := by
    have hnat : (488157587 : ℕ)^4699*625000000000^3675 ≤ 249839211699^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488157587 1000000000 249839211699 625000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199285041/1250000000 : ℝ), (5857772393/10000000000 : ℝ), (488157587/1000000000 : ℝ)] ![(4779007918443/50000000000000 : ℝ), (50467710269691/100000000000000 : ℝ), (249839211699/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199285041/1250000000 : ℝ)|^4699 ≤ (4779007918443/50000000000000 : ℝ)^3675
        have hw : |(-199285041/1250000000 : ℝ)|=(199285041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5857772393/10000000000 : ℝ)|^4699 ≤ (50467710269691/100000000000000 : ℝ)^3675
        have hw : |(5857772393/10000000000 : ℝ)|=(5857772393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(488157587/1000000000 : ℝ)|^4699 ≤ (249839211699/625000000000 : ℝ)^3675
        have hw : |(488157587/1000000000 : ℝ)|=(488157587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091988289/2000000000 : ℝ)*x 0 + (-133539303/625000000 : ℝ)*x 1 + (2440787853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091988289/2000000000 : ℝ)^4699 ≤ (46127316341269/100000000000000 : ℝ)^3675 := by
    have hnat : (1091988289 : ℕ)^4699*100000000000000^3675 ≤ 46127316341269^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091988289 2000000000 46127316341269 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133539303/625000000 : ℝ)^4699 ≤ (2779682297351/20000000000000 : ℝ)^3675 := by
    have hnat : (133539303 : ℕ)^4699*20000000000000^3675 ≤ 2779682297351^3675*625000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133539303 625000000 2779682297351 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2440787853/5000000000 : ℝ)^4699 ≤ (39974272154673/100000000000000 : ℝ)^3675 := by
    have hnat : (2440787853 : ℕ)^4699*100000000000000^3675 ≤ 39974272154673^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440787853 5000000000 39974272154673 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091988289/2000000000 : ℝ), (-133539303/625000000 : ℝ), (2440787853/5000000000 : ℝ)] ![(46127316341269/100000000000000 : ℝ), (2779682297351/20000000000000 : ℝ), (39974272154673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091988289/2000000000 : ℝ)|^4699 ≤ (46127316341269/100000000000000 : ℝ)^3675
        have hw : |(1091988289/2000000000 : ℝ)|=(1091988289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133539303/625000000 : ℝ)|^4699 ≤ (2779682297351/20000000000000 : ℝ)^3675
        have hw : |(-133539303/625000000 : ℝ)|=(133539303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2440787853/5000000000 : ℝ)|^4699 ≤ (39974272154673/100000000000000 : ℝ)^3675
        have hw : |(2440787853/5000000000 : ℝ)|=(2440787853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2729970719/5000000000 : ℝ)*x 0 + (976315131/2000000000 : ℝ)*x 1 + (-1068314461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729970719/5000000000 : ℝ)^4699 ≤ (46127316265653/100000000000000 : ℝ)^3675 := by
    have hnat : (2729970719 : ℕ)^4699*100000000000000^3675 ≤ 46127316265653^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729970719 5000000000 46127316265653 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976315131/2000000000 : ℝ)^4699 ≤ (9993567905169/25000000000000 : ℝ)^3675 := by
    have hnat : (976315131 : ℕ)^4699*25000000000000^3675 ≤ 9993567905169^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976315131 2000000000 9993567905169 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068314461/5000000000 : ℝ)^4699 ≤ (13898412102237/100000000000000 : ℝ)^3675 := by
    have hnat : (1068314461 : ℕ)^4699*100000000000000^3675 ≤ 13898412102237^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068314461 5000000000 13898412102237 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729970719/5000000000 : ℝ), (976315131/2000000000 : ℝ), (-1068314461/5000000000 : ℝ)] ![(46127316265653/100000000000000 : ℝ), (9993567905169/25000000000000 : ℝ), (13898412102237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729970719/5000000000 : ℝ)|^4699 ≤ (46127316265653/100000000000000 : ℝ)^3675
        have hw : |(2729970719/5000000000 : ℝ)|=(2729970719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(976315131/2000000000 : ℝ)|^4699 ≤ (9993567905169/25000000000000 : ℝ)^3675
        have hw : |(976315131/2000000000 : ℝ)|=(976315131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068314461/5000000000 : ℝ)|^4699 ≤ (13898412102237/100000000000000 : ℝ)^3675
        have hw : |(-1068314461/5000000000 : ℝ)|=(1068314461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823442637/2000000000 : ℝ)*x 0 + (614425281/2000000000 : ℝ)*x 1 + (271183207/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823442637/2000000000 : ℝ)^4699 ≤ (32152640408473/100000000000000 : ℝ)^3675 := by
    have hnat : (823442637 : ℕ)^4699*100000000000000^3675 ≤ 32152640408473^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823442637 2000000000 32152640408473 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614425281/2000000000 : ℝ)^4699 ≤ (5527890024157/25000000000000 : ℝ)^3675 := by
    have hnat : (614425281 : ℕ)^4699*25000000000000^3675 ≤ 5527890024157^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614425281 2000000000 5527890024157 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271183207/500000000 : ℝ)^4699 ≤ (45735799477001/100000000000000 : ℝ)^3675 := by
    have hnat : (271183207 : ℕ)^4699*100000000000000^3675 ≤ 45735799477001^3675*500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271183207 500000000 45735799477001 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823442637/2000000000 : ℝ), (614425281/2000000000 : ℝ), (271183207/500000000 : ℝ)] ![(32152640408473/100000000000000 : ℝ), (5527890024157/25000000000000 : ℝ), (45735799477001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823442637/2000000000 : ℝ)|^4699 ≤ (32152640408473/100000000000000 : ℝ)^3675
        have hw : |(823442637/2000000000 : ℝ)|=(823442637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614425281/2000000000 : ℝ)|^4699 ≤ (5527890024157/25000000000000 : ℝ)^3675
        have hw : |(614425281/2000000000 : ℝ)|=(614425281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271183207/500000000 : ℝ)|^4699 ≤ (45735799477001/100000000000000 : ℝ)^3675
        have hw : |(271183207/500000000 : ℝ)|=(271183207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-798642423/5000000000 : ℝ)*x 0 + (981290979/2000000000 : ℝ)*x 1 + (1458000429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798642423/5000000000 : ℝ)^4699 ≤ (4790526789979/50000000000000 : ℝ)^3675 := by
    have hnat : (798642423 : ℕ)^4699*50000000000000^3675 ≤ 4790526789979^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798642423 5000000000 4790526789979 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981290979/2000000000 : ℝ)^4699 ≤ (40234955173309/100000000000000 : ℝ)^3675 := by
    have hnat : (981290979 : ℕ)^4699*100000000000000^3675 ≤ 40234955173309^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981290979 2000000000 40234955173309 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458000429/2500000000 : ℝ)^4699 ≤ (50183991227841/100000000000000 : ℝ)^3675 := by
    have hnat : (1458000429 : ℕ)^4699*100000000000000^3675 ≤ 50183991227841^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458000429 2500000000 50183991227841 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798642423/5000000000 : ℝ), (981290979/2000000000 : ℝ), (1458000429/2500000000 : ℝ)] ![(4790526789979/50000000000000 : ℝ), (40234955173309/100000000000000 : ℝ), (50183991227841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798642423/5000000000 : ℝ)|^4699 ≤ (4790526789979/50000000000000 : ℝ)^3675
        have hw : |(-798642423/5000000000 : ℝ)|=(798642423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(981290979/2000000000 : ℝ)|^4699 ≤ (40234955173309/100000000000000 : ℝ)^3675
        have hw : |(981290979/2000000000 : ℝ)|=(981290979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458000429/2500000000 : ℝ)|^4699 ≤ (50183991227841/100000000000000 : ℝ)^3675
        have hw : |(1458000429/2500000000 : ℝ)|=(1458000429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649163593/1250000000 : ℝ)*x 0 + (-593101219/5000000000 : ℝ)*x 1 + (5832001871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649163593/1250000000 : ℝ)^4699 ≤ (8653377472407/20000000000000 : ℝ)^3675 := by
    have hnat : (649163593 : ℕ)^4699*20000000000000^3675 ≤ 8653377472407^3675*1250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649163593 1250000000 8653377472407 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593101219/5000000000 : ℝ)^4699 ≤ (6549119691033/100000000000000 : ℝ)^3675 := by
    have hnat : (593101219 : ℕ)^4699*100000000000000^3675 ≤ 6549119691033^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593101219 5000000000 6549119691033 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5832001871/10000000000 : ℝ)^4699 ≤ (10036798586649/20000000000000 : ℝ)^3675 := by
    have hnat : (5832001871 : ℕ)^4699*20000000000000^3675 ≤ 10036798586649^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5832001871 10000000000 10036798586649 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649163593/1250000000 : ℝ), (-593101219/5000000000 : ℝ), (5832001871/10000000000 : ℝ)] ![(8653377472407/20000000000000 : ℝ), (6549119691033/100000000000000 : ℝ), (10036798586649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649163593/1250000000 : ℝ)|^4699 ≤ (8653377472407/20000000000000 : ℝ)^3675
        have hw : |(649163593/1250000000 : ℝ)|=(649163593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-593101219/5000000000 : ℝ)|^4699 ≤ (6549119691033/100000000000000 : ℝ)^3675
        have hw : |(-593101219/5000000000 : ℝ)|=(593101219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5832001871/10000000000 : ℝ)|^4699 ≤ (10036798586649/20000000000000 : ℝ)^3675
        have hw : |(5832001871/10000000000 : ℝ)|=(5832001871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596654379/5000000000 : ℝ)*x 0 + (145800043/250000000 : ℝ)*x 1 + (-296550663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596654379/5000000000 : ℝ)^4699 ≤ (43266887511173/100000000000000 : ℝ)^3675 := by
    have hnat : (2596654379 : ℕ)^4699*100000000000000^3675 ≤ 43266887511173^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596654379 5000000000 43266887511173 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145800043/250000000 : ℝ)^4699 ≤ (50183991271851/100000000000000 : ℝ)^3675 := by
    have hnat : (145800043 : ℕ)^4699*100000000000000^3675 ≤ 50183991271851^3675*250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145800043 250000000 50183991271851 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296550663/2500000000 : ℝ)^4699 ≤ (40932007511/625000000000 : ℝ)^3675 := by
    have hnat : (296550663 : ℕ)^4699*625000000000^3675 ≤ 40932007511^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296550663 2500000000 40932007511 625000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596654379/5000000000 : ℝ), (145800043/250000000 : ℝ), (-296550663/2500000000 : ℝ)] ![(43266887511173/100000000000000 : ℝ), (50183991271851/100000000000000 : ℝ), (40932007511/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596654379/5000000000 : ℝ)|^4699 ≤ (43266887511173/100000000000000 : ℝ)^3675
        have hw : |(2596654379/5000000000 : ℝ)|=(2596654379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145800043/250000000 : ℝ)|^4699 ≤ (50183991271851/100000000000000 : ℝ)^3675
        have hw : |(145800043/250000000 : ℝ)|=(145800043/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-296550663/2500000000 : ℝ)|^4699 ≤ (40932007511/625000000000 : ℝ)^3675
        have hw : |(-296550663/2500000000 : ℝ)|=(296550663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s0_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4124451297/10000000000 : ℝ)*x 0 + (214549329/400000000 : ℝ)*x 1 + (626840889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124451297/10000000000 : ℝ)^4699 ≤ (32224932868093/100000000000000 : ℝ)^3675 := by
    have hnat : (4124451297 : ℕ)^4699*100000000000000^3675 ≤ 32224932868093^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124451297 10000000000 32224932868093 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214549329/400000000 : ℝ)^4699 ≤ (22545301779061/50000000000000 : ℝ)^3675 := by
    have hnat : (214549329 : ℕ)^4699*50000000000000^3675 ≤ 22545301779061^3675*400000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214549329 400000000 22545301779061 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626840889/2000000000 : ℝ)^4699 ≤ (22684463555193/100000000000000 : ℝ)^3675 := by
    have hnat : (626840889 : ℕ)^4699*100000000000000^3675 ≤ 22684463555193^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626840889 2000000000 22684463555193 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124451297/10000000000 : ℝ), (214549329/400000000 : ℝ), (626840889/2000000000 : ℝ)] ![(32224932868093/100000000000000 : ℝ), (22545301779061/50000000000000 : ℝ), (22684463555193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124451297/10000000000 : ℝ)|^4699 ≤ (32224932868093/100000000000000 : ℝ)^3675
        have hw : |(4124451297/10000000000 : ℝ)|=(4124451297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214549329/400000000 : ℝ)|^4699 ≤ (22545301779061/50000000000000 : ℝ)^3675
        have hw : |(214549329/400000000 : ℝ)|=(214549329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626840889/2000000000 : ℝ)|^4699 ≤ (22684463555193/100000000000000 : ℝ)^3675
        have hw : |(626840889/2000000000 : ℝ)|=(626840889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3689/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24593/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4695/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4695 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4695*1^1024 ≤ 0^1024*1^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4695/1024 : ℝ) ≤ (149782337802259377/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4695 ≤ (149782337802259377/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4695*10000000000000000000^1024 ≤ 149782337802259377^1024*5^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 149782337802259377 10000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (149782337802259377/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4695 := by
      have hnat : (1 : ℕ)^1024*1^4695 ≤ 1^4695*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10149782337802259377/10000000000000000000 : ℝ) ≤ (10032478570887627/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (10149782337802259377/10000000000000000000 : ℝ)^1024 ≤ (10032478570887627/10000000000000000 : ℝ)^4695 := by
      have hnat : (10149782337802259377 : ℕ)^1024*10000000000000000^4695 ≤ 10032478570887627^4695*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10149782337802259377 10000000000000000000 10032478570887627 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032478570887627/10000000000000000 : ℝ)) (X := (10149782337802259377/10000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5149782337802259377/5000000000000000000 : ℝ) ≤ (5032478570887627/5000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (5149782337802259377/5000000000000000000 : ℝ)^1024 ≤ (5032478570887627/5000000000000000 : ℝ)^4695 := by
      have hnat : (5149782337802259377 : ℕ)^1024*5000000000000000^4695 ≤ 5032478570887627^4695*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5149782337802259377 5000000000000000000 5032478570887627 5000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032478570887627/5000000000000000 : ℝ)) (X := (5149782337802259377/5000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(32478570887627/4000000000000000 : ℝ)*(0 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32478570887627/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(149782337802259377/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(32478570887627/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (1 : ℝ)+(32478570887627/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10032478570887627/10000000000000000 : ℝ) by norm_num, show 1+(149782337802259377/10000000000000000000 : ℝ)+(0 : ℝ)=(10149782337802259377/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(149782337802259377/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(32478570887627/4000000000000000 : ℝ)*(2/5 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32478570887627/4000000000000000 : ℝ)*(2/5 : ℝ)=(5032478570887627/5000000000000000 : ℝ) by norm_num, show 1+2*(149782337802259377/10000000000000000000 : ℝ)=(5149782337802259377/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(32478570887627/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32478570887627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(32478570887627/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32478570887627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(32478570887627/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32478570887627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-199285041/1250000000 : ℝ)*X 0 0+(5857772393/10000000000 : ℝ)*X 0 1+(488157587/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1091988289/2000000000 : ℝ)*X 1 0+(-133539303/625000000 : ℝ)*X 1 1+(2440787853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2729970719/5000000000 : ℝ)*X 2 0+(976315131/2000000000 : ℝ)*X 2 1+(-1068314461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823442637/2000000000 : ℝ)*X 0 0+(614425281/2000000000 : ℝ)*X 0 1+(271183207/500000000 : ℝ)*X 0 2+(823442637/2000000000 : ℝ)*X 1 0+(614425281/2000000000 : ℝ)*X 1 1+(271183207/500000000 : ℝ)*X 1 2+(823442637/2000000000 : ℝ)*X 2 0+(614425281/2000000000 : ℝ)*X 2 1+(271183207/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-798642423/5000000000 : ℝ)*X 0 0+(981290979/2000000000 : ℝ)*X 0 1+(1458000429/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((649163593/1250000000 : ℝ)*X 1 0+(-593101219/5000000000 : ℝ)*X 1 1+(5832001871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596654379/5000000000 : ℝ)*X 2 0+(145800043/250000000 : ℝ)*X 2 1+(-296550663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4124451297/10000000000 : ℝ)*X 0 0+(214549329/400000000 : ℝ)*X 0 1+(626840889/2000000000 : ℝ)*X 0 2+(4124451297/10000000000 : ℝ)*X 1 0+(214549329/400000000 : ℝ)*X 1 1+(626840889/2000000000 : ℝ)*X 1 2+(4124451297/10000000000 : ℝ)*X 2 0+(214549329/400000000 : ℝ)*X 2 1+(626840889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148200431465658387/31250000000000000000000 : ℝ) := by norm_num
    linear_combination (37439399/100000000000000 : ℝ)*(base1) + (860162963/100000000000000 : ℝ)*(base19) + (85884963/10000000000000 : ℝ)*(base23) + (1884683/1562500000000 : ℝ)*(upper3) + (6105639/6250000000000 : ℝ)*(upper5) + (45301448369949/6250000000000 : ℝ)*(major0) + (45301448369949/6250000000000 : ℝ)*(major1) + (45301448369949/6250000000000 : ℝ)*(major2) + (1024386911851321/100000000000000 : ℝ)*(sp0) + (204877801680031/20000000000000 : ℝ)*(sp1) + (64024313107093/6250000000000 : ℝ)*(sp2) + (425254897837799/100000000000000 : ℝ)*(sp3) + (748537799/25000000000000 : ℝ)*(sp4) + (346479397/25000000000000 : ℝ)*(sp7) + (212628160597393/50000000000000 : ℝ)*(f.failure) + (512194934281559/50000000000000 : ℝ)*(f.sum) + (9940173383523/12500000000000000000000000000 : ℝ)*base65 + (192823033978977/25000000000000000000000000000 : ℝ)*base68 + (29635624571023/25000000000000000000000000000 : ℝ)*base69 + (107415182928977/25000000000000000000000000000 : ℝ)*base72 + (37816952966477/12500000000000000000000000000 : ℝ)*base74 + (81686678971023/25000000000000000000000000000 : ℝ)*base75 + (62659977153977/25000000000000000000000000000 : ℝ)*base78 + (115004260653977/25000000000000000000000000000 : ℝ)*base80 + (47057620421023/12500000000000000000000000000 : ℝ)*base81 + (32727369/5000000000000000000000 : ℝ)*base89 + (32727369/5000000000000000000000 : ℝ)*base91 + (32727369/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102902440063062325253007/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1758620949/100000000000000 : ℝ)*(base19) + (443473271/25000000000000 : ℝ)*(base23) + (161348189/100000000000000 : ℝ)*(base32) + (7276883/2500000000000 : ℝ)*(upper3) + (16271131/10000000000000 : ℝ)*(upper5) + (191120837175353/25000000000000 : ℝ)*(major0) + (191120837175353/25000000000000 : ℝ)*(major1) + (191120837175353/25000000000000 : ℝ)*(major2) + (965176297/20000000000000 : ℝ)*(sp1) + (5066612887/100000000000000 : ℝ)*(sp2) + (216088267380903/20000000000000 : ℝ)*(sp4) + (1080434752402081/100000000000000 : ℝ)*(sp5) + (67527156024909/6250000000000 : ℝ)*(sp6) + (44852492474361/10000000000000 : ℝ)*(sp7) + (448525086091799/100000000000000 : ℝ)*(f.failure) + (216088267380903/20000000000000 : ℝ)*(f.sum) + (44899466942669/50000000000000000000000000000 : ℝ)*base66 + (586745339557331/100000000000000000000000000000 : ℝ)*base67 + (464475238057331/100000000000000000000000000000 : ℝ)*base69 + (267254231157331/100000000000000000000000000000 : ℝ)*base71 + (177780182457331/50000000000000000000000000000 : ℝ)*base73 + (490540315957331/100000000000000000000000000000 : ℝ)*base75 + (349352454257331/100000000000000000000000000000 : ℝ)*base77 + (273484265557331/100000000000000000000000000000 : ℝ)*base79 + (86850159657331/50000000000000000000000000000 : ℝ)*base81 + (11425567/10000000000000000000000 : ℝ)*base89 + (11425567/10000000000000000000000 : ℝ)*base91 + (11425567/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1595_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3689/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24593/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1595_s1_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-862386001/5000000000 : ℝ)*x 0 + (173268259/312500000 : ℝ)*x 1 + (5110513401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862386001/5000000000 : ℝ)^4699 ≤ (5284757120447/50000000000000 : ℝ)^3675 := by
    have hnat : (862386001 : ℕ)^4699*50000000000000^3675 ≤ 5284757120447^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862386001 5000000000 5284757120447 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173268259/312500000 : ℝ)^4699 ≤ (4704362557213/10000000000000 : ℝ)^3675 := by
    have hnat : (173268259 : ℕ)^4699*10000000000000^3675 ≤ 4704362557213^3675*312500000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173268259 312500000 4704362557213 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5110513401/10000000000 : ℝ)^4699 ≤ (5298357521191/12500000000000 : ℝ)^3675 := by
    have hnat : (5110513401 : ℕ)^4699*12500000000000^3675 ≤ 5298357521191^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110513401 10000000000 5298357521191 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862386001/5000000000 : ℝ), (173268259/312500000 : ℝ), (5110513401/10000000000 : ℝ)] ![(5284757120447/50000000000000 : ℝ), (4704362557213/10000000000000 : ℝ), (5298357521191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862386001/5000000000 : ℝ)|^4699 ≤ (5284757120447/50000000000000 : ℝ)^3675
        have hw : |(-862386001/5000000000 : ℝ)|=(862386001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173268259/312500000 : ℝ)|^4699 ≤ (4704362557213/10000000000000 : ℝ)^3675
        have hw : |(173268259/312500000 : ℝ)|=(173268259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5110513401/10000000000 : ℝ)|^4699 ≤ (5298357521191/12500000000000 : ℝ)^3675
        have hw : |(5110513401/10000000000 : ℝ)|=(5110513401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376540117/10000000000 : ℝ)*x 0 + (-1952388797/10000000000 : ℝ)*x 1 + (5110513253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376540117/10000000000 : ℝ)^4699 ≤ (11307077566021/25000000000000 : ℝ)^3675 := by
    have hnat : (5376540117 : ℕ)^4699*25000000000000^3675 ≤ 11307077566021^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376540117 10000000000 11307077566021 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952388797/10000000000 : ℝ)^4699 ≤ (12384831117703/100000000000000 : ℝ)^3675 := by
    have hnat : (1952388797 : ℕ)^4699*100000000000000^3675 ≤ 12384831117703^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952388797 10000000000 12384831117703 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5110513253/10000000000 : ℝ)^4699 ≤ (42386858599973/100000000000000 : ℝ)^3675 := by
    have hnat : (5110513253 : ℕ)^4699*100000000000000^3675 ≤ 42386858599973^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110513253 10000000000 42386858599973 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376540117/10000000000 : ℝ), (-1952388797/10000000000 : ℝ), (5110513253/10000000000 : ℝ)] ![(11307077566021/25000000000000 : ℝ), (12384831117703/100000000000000 : ℝ), (42386858599973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376540117/10000000000 : ℝ)|^4699 ≤ (11307077566021/25000000000000 : ℝ)^3675
        have hw : |(5376540117/10000000000 : ℝ)|=(5376540117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952388797/10000000000 : ℝ)|^4699 ≤ (12384831117703/100000000000000 : ℝ)^3675
        have hw : |(-1952388797/10000000000 : ℝ)|=(1952388797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5110513253/10000000000 : ℝ)|^4699 ≤ (42386858599973/100000000000000 : ℝ)^3675
        have hw : |(5110513253/10000000000 : ℝ)|=(5110513253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537653981/1000000000 : ℝ)*x 0 + (5110513511/10000000000 : ℝ)*x 1 + (-488097217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537653981/1000000000 : ℝ)^4699 ≤ (11307076740489/25000000000000 : ℝ)^3675 := by
    have hnat : (537653981 : ℕ)^4699*25000000000000^3675 ≤ 11307076740489^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537653981 1000000000 11307076740489 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5110513511/10000000000 : ℝ)^4699 ≤ (42386861336089/100000000000000 : ℝ)^3675 := by
    have hnat : (5110513511 : ℕ)^4699*100000000000000^3675 ≤ 42386861336089^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110513511 10000000000 42386861336089 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488097217/2500000000 : ℝ)^4699 ≤ (12384831693581/100000000000000 : ℝ)^3675 := by
    have hnat : (488097217 : ℕ)^4699*100000000000000^3675 ≤ 12384831693581^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488097217 2500000000 12384831693581 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537653981/1000000000 : ℝ), (5110513511/10000000000 : ℝ), (-488097217/2500000000 : ℝ)] ![(11307076740489/25000000000000 : ℝ), (42386861336089/100000000000000 : ℝ), (12384831693581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537653981/1000000000 : ℝ)|^4699 ≤ (11307076740489/25000000000000 : ℝ)^3675
        have hw : |(537653981/1000000000 : ℝ)|=(537653981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5110513511/10000000000 : ℝ)|^4699 ≤ (42386861336089/100000000000000 : ℝ)^3675
        have hw : |(5110513511/10000000000 : ℝ)|=(5110513511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488097217/2500000000 : ℝ)|^4699 ≤ (12384831693581/100000000000000 : ℝ)^3675
        have hw : |(-488097217/2500000000 : ℝ)|=(488097217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211989193/10000000000 : ℝ)*x 0 + (1857333761/5000000000 : ℝ)*x 1 + (148759091/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211989193/10000000000 : ℝ)^4699 ≤ (33102026301801/100000000000000 : ℝ)^3675 := by
    have hnat : (4211989193 : ℕ)^4699*100000000000000^3675 ≤ 33102026301801^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211989193 10000000000 33102026301801 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1857333761/5000000000 : ℝ)^4699 ≤ (563783904381/2000000000000 : ℝ)^3675 := by
    have hnat : (1857333761 : ℕ)^4699*2000000000000^3675 ≤ 563783904381^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857333761 5000000000 563783904381 2000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148759091/312500000 : ℝ)^4699 ≤ (19354389233707/50000000000000 : ℝ)^3675 := by
    have hnat : (148759091 : ℕ)^4699*50000000000000^3675 ≤ 19354389233707^3675*312500000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148759091 312500000 19354389233707 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211989193/10000000000 : ℝ), (1857333761/5000000000 : ℝ), (148759091/312500000 : ℝ)] ![(33102026301801/100000000000000 : ℝ), (563783904381/2000000000000 : ℝ), (19354389233707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211989193/10000000000 : ℝ)|^4699 ≤ (33102026301801/100000000000000 : ℝ)^3675
        have hw : |(4211989193/10000000000 : ℝ)|=(4211989193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1857333761/5000000000 : ℝ)|^4699 ≤ (563783904381/2000000000000 : ℝ)^3675
        have hw : |(1857333761/5000000000 : ℝ)|=(1857333761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148759091/312500000 : ℝ)|^4699 ≤ (19354389233707/50000000000000 : ℝ)^3675
        have hw : |(148759091/312500000 : ℝ)|=(148759091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43125733/250000000 : ℝ)*x 0 + (2557688921/5000000000 : ℝ)*x 1 + (5539642001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43125733/250000000 : ℝ)^4699 ≤ (2642882629977/25000000000000 : ℝ)^3675 := by
    have hnat : (43125733 : ℕ)^4699*25000000000000^3675 ≤ 2642882629977^3675*250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43125733 250000000 2642882629977 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2557688921/5000000000 : ℝ)^4699 ≤ (42438454898211/100000000000000 : ℝ)^3675 := by
    have hnat : (2557688921 : ℕ)^4699*100000000000000^3675 ≤ 42438454898211^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557688921 5000000000 42438454898211 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5539642001/10000000000 : ℝ)^4699 ≤ (46990014571941/100000000000000 : ℝ)^3675 := by
    have hnat : (5539642001 : ℕ)^4699*100000000000000^3675 ≤ 46990014571941^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539642001 10000000000 46990014571941 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43125733/250000000 : ℝ), (2557688921/5000000000 : ℝ), (5539642001/10000000000 : ℝ)] ![(2642882629977/25000000000000 : ℝ), (42438454898211/100000000000000 : ℝ), (46990014571941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43125733/250000000 : ℝ)|^4699 ≤ (2642882629977/25000000000000 : ℝ)^3675
        have hw : |(-43125733/250000000 : ℝ)|=(43125733/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2557688921/5000000000 : ℝ)|^4699 ≤ (42438454898211/100000000000000 : ℝ)^3675
        have hw : |(2557688921/5000000000 : ℝ)|=(2557688921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5539642001/10000000000 : ℝ)|^4699 ≤ (46990014571941/100000000000000 : ℝ)^3675
        have hw : |(5539642001/10000000000 : ℝ)|=(5539642001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261344499/10000000000 : ℝ)*x 0 + (-1523260067/10000000000 : ℝ)*x 1 + (2769821123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261344499/10000000000 : ℝ)^4699 ≤ (549912129877/1250000000000 : ℝ)^3675 := by
    have hnat : (5261344499 : ℕ)^4699*1250000000000^3675 ≤ 549912129877^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261344499 10000000000 549912129877 1250000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1523260067/10000000000 : ℝ)^4699 ≤ (4508506180023/50000000000000 : ℝ)^3675 := by
    have hnat : (1523260067 : ℕ)^4699*50000000000000^3675 ≤ 4508506180023^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523260067 10000000000 4508506180023 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2769821123/5000000000 : ℝ)^4699 ≤ (23495008614613/50000000000000 : ℝ)^3675 := by
    have hnat : (2769821123 : ℕ)^4699*50000000000000^3675 ≤ 23495008614613^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769821123 5000000000 23495008614613 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261344499/10000000000 : ℝ), (-1523260067/10000000000 : ℝ), (2769821123/5000000000 : ℝ)] ![(549912129877/1250000000000 : ℝ), (4508506180023/50000000000000 : ℝ), (23495008614613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261344499/10000000000 : ℝ)|^4699 ≤ (549912129877/1250000000000 : ℝ)^3675
        have hw : |(5261344499/10000000000 : ℝ)|=(5261344499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1523260067/10000000000 : ℝ)|^4699 ≤ (4508506180023/50000000000000 : ℝ)^3675
        have hw : |(-1523260067/10000000000 : ℝ)|=(1523260067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2769821123/5000000000 : ℝ)|^4699 ≤ (23495008614613/50000000000000 : ℝ)^3675
        have hw : |(2769821123/5000000000 : ℝ)|=(2769821123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315336007/2500000000 : ℝ)*x 0 + (1107928483/2000000000 : ℝ)*x 1 + (-1523260491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315336007/2500000000 : ℝ)^4699 ≤ (4399296535451/10000000000000 : ℝ)^3675 := by
    have hnat : (1315336007 : ℕ)^4699*10000000000000^3675 ≤ 4399296535451^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315336007 2500000000 4399296535451 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107928483/2000000000 : ℝ)^4699 ≤ (4699001906221/10000000000000 : ℝ)^3675 := by
    have hnat : (1107928483 : ℕ)^4699*10000000000000^3675 ≤ 4699001906221^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107928483 2000000000 4699001906221 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523260491/10000000000 : ℝ)^4699 ≤ (9017015569289/100000000000000 : ℝ)^3675 := by
    have hnat : (1523260491 : ℕ)^4699*100000000000000^3675 ≤ 9017015569289^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523260491 10000000000 9017015569289 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315336007/2500000000 : ℝ), (1107928483/2000000000 : ℝ), (-1523260491/10000000000 : ℝ)] ![(4399296535451/10000000000000 : ℝ), (4699001906221/10000000000000 : ℝ), (9017015569289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315336007/2500000000 : ℝ)|^4699 ≤ (4399296535451/10000000000000 : ℝ)^3675
        have hw : |(1315336007/2500000000 : ℝ)|=(1315336007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107928483/2000000000 : ℝ)|^4699 ≤ (4699001906221/10000000000000 : ℝ)^3675
        have hw : |(1107928483/2000000000 : ℝ)|=(1107928483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1523260491/10000000000 : ℝ)|^4699 ≤ (9017015569289/100000000000000 : ℝ)^3675
        have hw : |(-1523260491/10000000000 : ℝ)|=(1523260491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s1_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526576049/1250000000 : ℝ)*x 0 + (474857367/1000000000 : ℝ)*x 1 + (1863286131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526576049/1250000000 : ℝ)^4699 ≤ (33108248653771/100000000000000 : ℝ)^3675 := by
    have hnat : (526576049 : ℕ)^4699*100000000000000^3675 ≤ 33108248653771^3675*1250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526576049 1250000000 33108248653771 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474857367/1000000000 : ℝ)^4699 ≤ (7717398321813/20000000000000 : ℝ)^3675 := by
    have hnat : (474857367 : ℕ)^4699*20000000000000^3675 ≤ 7717398321813^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474857367 1000000000 7717398321813 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863286131/5000000000 : ℝ)^4699 ≤ (3538094965429/12500000000000 : ℝ)^3675 := by
    have hnat : (1863286131 : ℕ)^4699*12500000000000^3675 ≤ 3538094965429^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863286131 5000000000 3538094965429 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526576049/1250000000 : ℝ), (474857367/1000000000 : ℝ), (1863286131/5000000000 : ℝ)] ![(33108248653771/100000000000000 : ℝ), (7717398321813/20000000000000 : ℝ), (3538094965429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526576049/1250000000 : ℝ)|^4699 ≤ (33108248653771/100000000000000 : ℝ)^3675
        have hw : |(526576049/1250000000 : ℝ)|=(526576049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474857367/1000000000 : ℝ)|^4699 ≤ (7717398321813/20000000000000 : ℝ)^3675
        have hw : |(474857367/1000000000 : ℝ)|=(474857367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863286131/5000000000 : ℝ)|^4699 ≤ (3538094965429/12500000000000 : ℝ)^3675
        have hw : |(1863286131/5000000000 : ℝ)|=(1863286131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (553/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3689/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3689/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3689/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3689/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3689/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3689/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3689/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (839812212873/3125000000000000000 : ℝ) := by
    have hpowers : (3689/100000 : ℝ)^4695 ≤ (839812212873/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4695*3125000000000000000^1024 ≤ 839812212873^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 100000 839812212873 3125000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/100000 : ℝ)) (X := (839812212873/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24593/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (8051273376774043/5000000000000000000 : ℝ) := by
    have hpowers : (24593/100000 : ℝ)^4695 ≤ (8051273376774043/5000000000000000000 : ℝ)^1024 := by
      have hnat : (24593 : ℕ)^4695*5000000000000000000^1024 ≤ 8051273376774043^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24593 100000 8051273376774043 5000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24593/100000 : ℝ)) (X := (8051273376774043/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500839812212873/1562500000000000000 : ℝ) ≤ (5000000586133351/5000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (1562500839812212873/1562500000000000000 : ℝ)^1024 ≤ (5000000586133351/5000000000000000 : ℝ)^4695 := by
      have hnat : (1562500839812212873 : ℕ)^1024*5000000000000000^4695 ≤ 5000000586133351^4695*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500839812212873 1562500000000000000 5000000586133351 5000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000586133351/5000000000000000 : ℝ)) (X := (1562500839812212873/1562500000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25040263085381573199/25000000000000000000 : ℝ) ≤ (10003510412348749/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (25040263085381573199/25000000000000000000 : ℝ)^1024 ≤ (10003510412348749/10000000000000000 : ℝ)^4695 := by
      have hnat : (25040263085381573199 : ℕ)^1024*10000000000000000^4695 ≤ 10003510412348749^4695*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25040263085381573199 25000000000000000000 10003510412348749 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003510412348749/10000000000000000 : ℝ)) (X := (25040263085381573199/25000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2508051273376774043/2500000000000000000 : ℝ) ≤ (2501754913107699/2500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (2508051273376774043/2500000000000000000 : ℝ)^1024 ≤ (2501754913107699/2500000000000000 : ℝ)^4695 := by
      have hnat : (2508051273376774043 : ℕ)^1024*2500000000000000^4695 ≤ 2501754913107699^4695*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2508051273376774043 2500000000000000000 2501754913107699 2500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501754913107699/2500000000000000 : ℝ)) (X := (2508051273376774043/2500000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(839812212873/3125000000000000000 : ℝ) ≤ ((104507066665868897921/104520000000000000000 : ℝ)+2*(3509240082047/2090400000000000 : ℝ)*(3689/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (104507066665868897921/104520000000000000000 : ℝ)+2*(3509240082047/2090400000000000 : ℝ)*(3689/100000 : ℝ)=(5000000586133351/5000000000000000 : ℝ) by norm_num, show 1+2*(839812212873/3125000000000000000 : ℝ)=(1562500839812212873/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8051273376774043/5000000000000000000 : ℝ)+(839812212873/3125000000000000000 : ℝ) ≤ ((104507066665868897921/104520000000000000000 : ℝ)+(3509240082047/2090400000000000 : ℝ)*((24593/100000 : ℝ)+(3689/100000 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (104507066665868897921/104520000000000000000 : ℝ)+(3509240082047/2090400000000000 : ℝ)*((24593/100000 : ℝ)+(3689/100000 : ℝ))=(10003510412348749/10000000000000000 : ℝ) by norm_num, show 1+(8051273376774043/5000000000000000000 : ℝ)+(839812212873/3125000000000000000 : ℝ)=(25040263085381573199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8051273376774043/5000000000000000000 : ℝ) ≤ ((104507066665868897921/104520000000000000000 : ℝ)+2*(3509240082047/2090400000000000 : ℝ)*(24593/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (104507066665868897921/104520000000000000000 : ℝ)+2*(3509240082047/2090400000000000 : ℝ)*(24593/100000 : ℝ)=(2501754913107699/2500000000000000 : ℝ) by norm_num, show 1+2*(8051273376774043/5000000000000000000 : ℝ)=(2508051273376774043/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104507066665868897921/104520000000000000000 : ℝ)*(X 1 0+X 2 0)+(3509240082047/2090400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (3689/100000 : ℝ)) (hi := (24593/100000 : ℝ)) (c := (104507066665868897921/104520000000000000000 : ℝ)) (alpha := (3509240082047/2090400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104507066665868897921/104520000000000000000 : ℝ)*(X 0 1+X 2 1)+(3509240082047/2090400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (3689/100000 : ℝ)) (hi := (24593/100000 : ℝ)) (c := (104507066665868897921/104520000000000000000 : ℝ)) (alpha := (3509240082047/2090400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104507066665868897921/104520000000000000000 : ℝ)*(X 0 2+X 1 2)+(3509240082047/2090400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (3689/100000 : ℝ)) (hi := (24593/100000 : ℝ)) (c := (104507066665868897921/104520000000000000000 : ℝ)) (alpha := (3509240082047/2090400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-862386001/5000000000 : ℝ)*X 0 0+(173268259/312500000 : ℝ)*X 0 1+(5110513401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376540117/10000000000 : ℝ)*X 1 0+(-1952388797/10000000000 : ℝ)*X 1 1+(5110513253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537653981/1000000000 : ℝ)*X 2 0+(5110513511/10000000000 : ℝ)*X 2 1+(-488097217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4211989193/10000000000 : ℝ)*X 0 0+(1857333761/5000000000 : ℝ)*X 0 1+(148759091/312500000 : ℝ)*X 0 2+(4211989193/10000000000 : ℝ)*X 1 0+(1857333761/5000000000 : ℝ)*X 1 1+(148759091/312500000 : ℝ)*X 1 2+(4211989193/10000000000 : ℝ)*X 2 0+(1857333761/5000000000 : ℝ)*X 2 1+(148759091/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43125733/250000000 : ℝ)*X 0 0+(2557688921/5000000000 : ℝ)*X 0 1+(5539642001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261344499/10000000000 : ℝ)*X 1 0+(-1523260067/10000000000 : ℝ)*X 1 1+(2769821123/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315336007/2500000000 : ℝ)*X 2 0+(1107928483/2000000000 : ℝ)*X 2 1+(-1523260491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526576049/1250000000 : ℝ)*X 0 0+(474857367/1000000000 : ℝ)*X 0 1+(1863286131/5000000000 : ℝ)*X 0 2+(526576049/1250000000 : ℝ)*X 1 0+(474857367/1000000000 : ℝ)*X 1 1+(1863286131/5000000000 : ℝ)*X 1 2+(526576049/1250000000 : ℝ)*X 2 0+(474857367/1000000000 : ℝ)*X 2 1+(1863286131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4252920083090203124482870089/871000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8343113/20000000000000 : ℝ)*(base1) + (151356589/12500000000000 : ℝ)*(base19) + (43172261/4000000000000 : ℝ)*(base23) + (7281843/5000000000000 : ℝ)*(upper3) + (83412661/100000000000000 : ℝ)*(upper5) + (815041537037603/50000000000000 : ℝ)*(major0) + (815041537037603/50000000000000 : ℝ)*(major1) + (815041537037603/50000000000000 : ℝ)*(major2) + (14398633797277/625000000000 : ℝ)*(sp0) + (46075785326449/2000000000000 : ℝ)*(sp1) + (575947349467159/25000000000000 : ℝ)*(sp2) + (191274246024557/20000000000000 : ℝ)*(sp3) + (9111326407/100000000000000 : ℝ)*(sp4) + (1059094211/25000000000000 : ℝ)*(sp7) + (478187754107597/50000000000000 : ℝ)*(f.failure) + (2303790477175161/100000000000000 : ℝ)*(f.sum) + (90305654405639/52260000000000000000000000000 : ℝ)*base66 + (16161918861363808879/1742000000000000000000000000000000 : ℝ)*base68 + (20221544768245808879/1742000000000000000000000000000000 : ℝ)*base70 + (13942959085421808879/1742000000000000000000000000000000 : ℝ)*base72 + (63218153322659/52260000000000000000000000000 : ℝ)*base74 + (16962884876511808879/1742000000000000000000000000000000 : ℝ)*base76 + (15896912597841808879/1742000000000000000000000000000000 : ℝ)*base78 + (2683129654727808879/1742000000000000000000000000000000 : ℝ)*base80 + (68349740406659/52260000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (27099301/5000000000000000000000 : ℝ)*base89 + (27099301/5000000000000000000000 : ℝ)*base91 + (27099301/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4092965157888102143019360687/435500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1800606441/100000000000000 : ℝ)*(base19) + (1587688991/100000000000000 : ℝ)*(base23) + (3201831/25000000000000 : ℝ)*(upper2) + (144402253/50000000000000 : ℝ)*(upper3) + (86234177/50000000000000 : ℝ)*(upper5) + (833873084984553/50000000000000 : ℝ)*(major0) + (833873084984553/50000000000000 : ℝ)*(major1) + (833873084984553/50000000000000 : ℝ)*(major2) + (6665564087/50000000000000 : ℝ)*(sp1) + (12131847533/100000000000000 : ℝ)*(sp2) + (589254861700023/25000000000000 : ℝ)*(sp4) + (589251078766369/25000000000000 : ℝ)*(sp5) + (1178502863631783/50000000000000 : ℝ)*(sp6) + (489236289930509/50000000000000 : ℝ)*(sp7) + (489236289930509/50000000000000 : ℝ)*(f.failure) + (589254861700023/25000000000000 : ℝ)*(f.sum) + (85702925509277/17420000000000000000000000000 : ℝ)*base65 + (4143931813331454771/1742000000000000000000000000000000 : ℝ)*base67 + (2754369519396545229/1742000000000000000000000000000000 : ℝ)*base70 + (13302882816143454771/1742000000000000000000000000000000 : ℝ)*base71 + (46984939564197/17420000000000000000000000000 : ℝ)*base73 + (12783355885311454771/1742000000000000000000000000000000 : ℝ)*base75 + (26501146345711454771/1742000000000000000000000000000000 : ℝ)*base77 + (31204318702893454771/1742000000000000000000000000000000 : ℝ)*base79 + (95780089931723/17420000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (42399003/5000000000000000000000 : ℝ)*base90 + (42399003/5000000000000000000000 : ℝ)*base92 + (42399003/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1595_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1595_s2_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740886217/10000000000 : ℝ)*x 0 + (2736745293/5000000000 : ℝ)*x 1 + (5171088961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740886217/10000000000 : ℝ)^4699 ≤ (1336992815969/12500000000000 : ℝ)^3675 := by
    have hnat : (1740886217 : ℕ)^4699*12500000000000^3675 ≤ 1336992815969^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740886217 10000000000 1336992815969 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736745293/5000000000 : ℝ)^4699 ≤ (46273729496583/100000000000000 : ℝ)^3675 := by
    have hnat : (2736745293 : ℕ)^4699*100000000000000^3675 ≤ 46273729496583^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736745293 5000000000 46273729496583 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171088961/10000000000 : ℝ)^4699 ≤ (43030327964807/100000000000000 : ℝ)^3675 := by
    have hnat : (5171088961 : ℕ)^4699*100000000000000^3675 ≤ 43030327964807^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171088961 10000000000 43030327964807 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740886217/10000000000 : ℝ), (2736745293/5000000000 : ℝ), (5171088961/10000000000 : ℝ)] ![(1336992815969/12500000000000 : ℝ), (46273729496583/100000000000000 : ℝ), (43030327964807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740886217/10000000000 : ℝ)|^4699 ≤ (1336992815969/12500000000000 : ℝ)^3675
        have hw : |(-1740886217/10000000000 : ℝ)|=(1740886217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736745293/5000000000 : ℝ)|^4699 ≤ (46273729496583/100000000000000 : ℝ)^3675
        have hw : |(2736745293/5000000000 : ℝ)|=(2736745293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171088961/10000000000 : ℝ)|^4699 ≤ (43030327964807/100000000000000 : ℝ)^3675
        have hw : |(5171088961/10000000000 : ℝ)|=(5171088961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071628371/2000000000 : ℝ)*x 0 + (-189722369/1000000000 : ℝ)*x 1 + (2585544397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071628371/2000000000 : ℝ)^4699 ≤ (9006102160521/20000000000000 : ℝ)^3675 := by
    have hnat : (1071628371 : ℕ)^4699*20000000000000^3675 ≤ 9006102160521^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071628371 2000000000 9006102160521 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189722369/1000000000 : ℝ)^4699 ≤ (5969581499729/50000000000000 : ℝ)^3675 := by
    have hnat : (189722369 : ℕ)^4699*50000000000000^3675 ≤ 5969581499729^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189722369 1000000000 5969581499729 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585544397/5000000000 : ℝ)^4699 ≤ (4303032618793/10000000000000 : ℝ)^3675 := by
    have hnat : (2585544397 : ℕ)^4699*10000000000000^3675 ≤ 4303032618793^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585544397 5000000000 4303032618793 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071628371/2000000000 : ℝ), (-189722369/1000000000 : ℝ), (2585544397/5000000000 : ℝ)] ![(9006102160521/20000000000000 : ℝ), (5969581499729/50000000000000 : ℝ), (4303032618793/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071628371/2000000000 : ℝ)|^4699 ≤ (9006102160521/20000000000000 : ℝ)^3675
        have hw : |(1071628371/2000000000 : ℝ)|=(1071628371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189722369/1000000000 : ℝ)|^4699 ≤ (5969581499729/50000000000000 : ℝ)^3675
        have hw : |(-189722369/1000000000 : ℝ)|=(189722369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585544397/5000000000 : ℝ)|^4699 ≤ (4303032618793/10000000000000 : ℝ)^3675
        have hw : |(2585544397/5000000000 : ℝ)|=(2585544397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358141673/10000000000 : ℝ)*x 0 + (5171089109/10000000000 : ℝ)*x 1 + (-379444703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358141673/10000000000 : ℝ)^4699 ≤ (2251525442343/5000000000000 : ℝ)^3675 := by
    have hnat : (5358141673 : ℕ)^4699*5000000000000^3675 ≤ 2251525442343^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358141673 10000000000 2251525442343 5000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171089109/10000000000 : ℝ)^4699 ≤ (10757582384881/25000000000000 : ℝ)^3675 := by
    have hnat : (5171089109 : ℕ)^4699*25000000000000^3675 ≤ 10757582384881^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171089109 10000000000 10757582384881 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379444703/2000000000 : ℝ)^4699 ≤ (2984790397833/25000000000000 : ℝ)^3675 := by
    have hnat : (379444703 : ℕ)^4699*25000000000000^3675 ≤ 2984790397833^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379444703 2000000000 2984790397833 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358141673/10000000000 : ℝ), (5171089109/10000000000 : ℝ), (-379444703/2000000000 : ℝ)] ![(2251525442343/5000000000000 : ℝ), (10757582384881/25000000000000 : ℝ), (2984790397833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358141673/10000000000 : ℝ)|^4699 ≤ (2251525442343/5000000000000 : ℝ)^3675
        have hw : |(5358141673/10000000000 : ℝ)|=(5358141673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171089109/10000000000 : ℝ)|^4699 ≤ (10757582384881/25000000000000 : ℝ)^3675
        have hw : |(5171089109/10000000000 : ℝ)|=(5171089109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379444703/2000000000 : ℝ)|^4699 ≤ (2984790397833/25000000000000 : ℝ)^3675
        have hw : |(-379444703/2000000000 : ℝ)|=(379444703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422382887/1000000000 : ℝ)*x 0 + (3871977993/10000000000 : ℝ)*x 1 + (4600425873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422382887/1000000000 : ℝ)^4699 ≤ (1661052387329/5000000000000 : ℝ)^3675 := by
    have hnat : (422382887 : ℕ)^4699*5000000000000^3675 ≤ 1661052387329^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422382887 1000000000 1661052387329 5000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3871977993/10000000000 : ℝ)^4699 ≤ (29724511241713/100000000000000 : ℝ)^3675 := by
    have hnat : (3871977993 : ℕ)^4699*100000000000000^3675 ≤ 29724511241713^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871977993 10000000000 29724511241713 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4600425873/10000000000 : ℝ)^4699 ≤ (18527220498683/50000000000000 : ℝ)^3675 := by
    have hnat : (4600425873 : ℕ)^4699*50000000000000^3675 ≤ 18527220498683^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4600425873 10000000000 18527220498683 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422382887/1000000000 : ℝ), (3871977993/10000000000 : ℝ), (4600425873/10000000000 : ℝ)] ![(1661052387329/5000000000000 : ℝ), (29724511241713/100000000000000 : ℝ), (18527220498683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422382887/1000000000 : ℝ)|^4699 ≤ (1661052387329/5000000000000 : ℝ)^3675
        have hw : |(422382887/1000000000 : ℝ)|=(422382887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3871977993/10000000000 : ℝ)|^4699 ≤ (29724511241713/100000000000000 : ℝ)^3675
        have hw : |(3871977993/10000000000 : ℝ)|=(3871977993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4600425873/10000000000 : ℝ)|^4699 ≤ (18527220498683/50000000000000 : ℝ)^3675
        have hw : |(4600425873/10000000000 : ℝ)|=(4600425873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-870486519/5000000000 : ℝ)*x 0 + (5173457913/10000000000 : ℝ)*x 1 + (5471095461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870486519/5000000000 : ℝ)^4699 ≤ (10696624590887/100000000000000 : ℝ)^3675 := by
    have hnat : (870486519 : ℕ)^4699*100000000000000^3675 ≤ 10696624590887^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870486519 5000000000 10696624590887 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173457913/10000000000 : ℝ)^4699 ≤ (21527767585801/50000000000000 : ℝ)^3675 := by
    have hnat : (5173457913 : ℕ)^4699*50000000000000^3675 ≤ 21527767585801^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173457913 10000000000 21527767585801 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471095461/10000000000 : ℝ)^4699 ≤ (11561960054729/25000000000000 : ℝ)^3675 := by
    have hnat : (5471095461 : ℕ)^4699*25000000000000^3675 ≤ 11561960054729^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471095461 10000000000 11561960054729 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-870486519/5000000000 : ℝ), (5173457913/10000000000 : ℝ), (5471095461/10000000000 : ℝ)] ![(10696624590887/100000000000000 : ℝ), (21527767585801/50000000000000 : ℝ), (11561960054729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-870486519/5000000000 : ℝ)|^4699 ≤ (10696624590887/100000000000000 : ℝ)^3675
        have hw : |(-870486519/5000000000 : ℝ)|=(870486519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173457913/10000000000 : ℝ)|^4699 ≤ (21527767585801/50000000000000 : ℝ)^3675
        have hw : |(5173457913/10000000000 : ℝ)|=(5173457913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471095461/10000000000 : ℝ)|^4699 ≤ (11561960054729/25000000000000 : ℝ)^3675
        have hw : |(5471095461/10000000000 : ℝ)|=(5471095461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527804719/1000000000 : ℝ)*x 0 + (-798608557/5000000000 : ℝ)*x 1 + (547109557/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527804719/1000000000 : ℝ)^4699 ≤ (22085812245337/50000000000000 : ℝ)^3675 := by
    have hnat : (527804719 : ℕ)^4699*50000000000000^3675 ≤ 22085812245337^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527804719 1000000000 22085812245337 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (798608557/5000000000 : ℝ)^4699 ≤ (9580534098163/100000000000000 : ℝ)^3675 := by
    have hnat : (798608557 : ℕ)^4699*100000000000000^3675 ≤ 9580534098163^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798608557 5000000000 9580534098163 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547109557/1000000000 : ℝ)^4699 ≤ (23123920698521/50000000000000 : ℝ)^3675 := by
    have hnat : (547109557 : ℕ)^4699*50000000000000^3675 ≤ 23123920698521^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547109557 1000000000 23123920698521 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527804719/1000000000 : ℝ), (-798608557/5000000000 : ℝ), (547109557/1000000000 : ℝ)] ![(22085812245337/50000000000000 : ℝ), (9580534098163/100000000000000 : ℝ), (23123920698521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527804719/1000000000 : ℝ)|^4699 ≤ (22085812245337/50000000000000 : ℝ)^3675
        have hw : |(527804719/1000000000 : ℝ)|=(527804719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-798608557/5000000000 : ℝ)|^4699 ≤ (9580534098163/100000000000000 : ℝ)^3675
        have hw : |(-798608557/5000000000 : ℝ)|=(798608557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547109557/1000000000 : ℝ)|^4699 ≤ (23123920698521/50000000000000 : ℝ)^3675
        have hw : |(547109557/1000000000 : ℝ)|=(547109557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329877959/625000000 : ℝ)*x 0 + (1094219061/2000000000 : ℝ)*x 1 + (-199652159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329877959/625000000 : ℝ)^4699 ≤ (8834325227721/20000000000000 : ℝ)^3675 := by
    have hnat : (329877959 : ℕ)^4699*20000000000000^3675 ≤ 8834325227721^3675*625000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329877959 625000000 8834325227721 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094219061/2000000000 : ℝ)^4699 ≤ (46247838532791/100000000000000 : ℝ)^3675 := by
    have hnat : (1094219061 : ℕ)^4699*100000000000000^3675 ≤ 46247838532791^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094219061 2000000000 46247838532791 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199652159/1250000000 : ℝ)^4699 ≤ (9580535309963/100000000000000 : ℝ)^3675 := by
    have hnat : (199652159 : ℕ)^4699*100000000000000^3675 ≤ 9580535309963^3675*1250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199652159 1250000000 9580535309963 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329877959/625000000 : ℝ), (1094219061/2000000000 : ℝ), (-199652159/1250000000 : ℝ)] ![(8834325227721/20000000000000 : ℝ), (46247838532791/100000000000000 : ℝ), (9580535309963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329877959/625000000 : ℝ)|^4699 ≤ (8834325227721/20000000000000 : ℝ)^3675
        have hw : |(329877959/625000000 : ℝ)|=(329877959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094219061/2000000000 : ℝ)|^4699 ≤ (46247838532791/100000000000000 : ℝ)^3675
        have hw : |(1094219061/2000000000 : ℝ)|=(1094219061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199652159/1250000000 : ℝ)|^4699 ≤ (9580535309963/100000000000000 : ℝ)^3675
        have hw : |(-199652159/1250000000 : ℝ)|=(199652159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s2_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66000603/156250000 : ℝ)*x 0 + (918944013/2000000000 : ℝ)*x 1 + (15147451/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66000603/156250000 : ℝ)^4699 ≤ (33223156870551/100000000000000 : ℝ)^3675 := by
    have hnat : (66000603 : ℕ)^4699*100000000000000^3675 ≤ 33223156870551^3675*156250000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66000603 156250000 33223156870551 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918944013/2000000000 : ℝ)^4699 ≤ (18497843838791/50000000000000 : ℝ)^3675 := by
    have hnat : (918944013 : ℕ)^4699*50000000000000^3675 ≤ 18497843838791^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918944013 2000000000 18497843838791 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15147451/39062500 : ℝ)^4699 ≤ (29781155442233/100000000000000 : ℝ)^3675 := by
    have hnat : (15147451 : ℕ)^4699*100000000000000^3675 ≤ 29781155442233^3675*39062500^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15147451 39062500 29781155442233 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66000603/156250000 : ℝ), (918944013/2000000000 : ℝ), (15147451/39062500 : ℝ)] ![(33223156870551/100000000000000 : ℝ), (18497843838791/50000000000000 : ℝ), (29781155442233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66000603/156250000 : ℝ)|^4699 ≤ (33223156870551/100000000000000 : ℝ)^3675
        have hw : |(66000603/156250000 : ℝ)|=(66000603/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918944013/2000000000 : ℝ)|^4699 ≤ (18497843838791/50000000000000 : ℝ)^3675
        have hw : |(918944013/2000000000 : ℝ)|=(918944013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15147451/39062500 : ℝ)|^4699 ≤ (29781155442233/100000000000000 : ℝ)^3675
        have hw : |(15147451/39062500 : ℝ)|=(15147451/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10157/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8281/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/6250 : ℝ) ^ (4695/1024 : ℝ) ≤ (1483631297806513/100000000000000000000 : ℝ) := by
    have hpowers : (553/6250 : ℝ)^4695 ≤ (1483631297806513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (553 : ℕ)^4695*100000000000000000000^1024 ≤ 1483631297806513^1024*6250^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 6250 1483631297806513 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/6250 : ℝ)) (X := (1483631297806513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18039/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (38883305427235547/100000000000000000000 : ℝ) := by
    have hpowers : (18039/100000 : ℝ)^4695 ≤ (38883305427235547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18039 : ℕ)^4695*100000000000000000000^1024 ≤ 38883305427235547^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18039 100000 38883305427235547 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18039/100000 : ℝ)) (X := (38883305427235547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001483631297806513/50000000000000000000 : ℝ) ≤ (2500016179135521/2500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50001483631297806513/50000000000000000000 : ℝ)^1024 ≤ (2500016179135521/2500000000000000 : ℝ)^4695 := by
      have hnat : (50001483631297806513 : ℕ)^1024*2500000000000000^4695 ≤ 2500016179135521^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001483631297806513 50000000000000000000 2500016179135521 2500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016179135521/2500000000000000 : ℝ)) (X := (50001483631297806513/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002018346836252103/5000000000000000000 : ℝ) ≤ (5000440140803251/5000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (5002018346836252103/5000000000000000000 : ℝ)^1024 ≤ (5000440140803251/5000000000000000 : ℝ)^4695 := by
      have hnat : (5002018346836252103 : ℕ)^1024*5000000000000000^4695 ≤ 5000440140803251^4695*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002018346836252103 5000000000000000000 5000440140803251 5000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000440140803251/5000000000000000 : ℝ)) (X := (5002018346836252103/5000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038883305427235547/50000000000000000000 : ℝ) ≤ (250042396166773/250000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50038883305427235547/50000000000000000000 : ℝ)^1024 ≤ (250042396166773/250000000000000 : ℝ)^4695 := by
      have hnat : (50038883305427235547 : ℕ)^1024*250000000000000^4695 ≤ 250042396166773^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038883305427235547 50000000000000000000 250042396166773 250000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250042396166773/250000000000000 : ℝ)) (X := (50038883305427235547/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1483631297806513/100000000000000000000 : ℝ) ≤ ((252461985083402069/252500000000000000 : ℝ)+2*(31367887093/35350000000000 : ℝ)*(553/6250 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (252461985083402069/252500000000000000 : ℝ)+2*(31367887093/35350000000000 : ℝ)*(553/6250 : ℝ)=(2500016179135521/2500000000000000 : ℝ) by norm_num, show 1+2*(1483631297806513/100000000000000000000 : ℝ)=(50001483631297806513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38883305427235547/100000000000000000000 : ℝ)+(1483631297806513/100000000000000000000 : ℝ) ≤ ((252461985083402069/252500000000000000 : ℝ)+(31367887093/35350000000000 : ℝ)*((18039/100000 : ℝ)+(553/6250 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (252461985083402069/252500000000000000 : ℝ)+(31367887093/35350000000000 : ℝ)*((18039/100000 : ℝ)+(553/6250 : ℝ))=(5000440140803251/5000000000000000 : ℝ) by norm_num, show 1+(38883305427235547/100000000000000000000 : ℝ)+(1483631297806513/100000000000000000000 : ℝ)=(5002018346836252103/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38883305427235547/100000000000000000000 : ℝ) ≤ ((252461985083402069/252500000000000000 : ℝ)+2*(31367887093/35350000000000 : ℝ)*(18039/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (252461985083402069/252500000000000000 : ℝ)+2*(31367887093/35350000000000 : ℝ)*(18039/100000 : ℝ)=(250042396166773/250000000000000 : ℝ) by norm_num, show 1+2*(38883305427235547/100000000000000000000 : ℝ)=(50038883305427235547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (252461985083402069/252500000000000000 : ℝ)*(X 1 0+X 2 0)+(31367887093/35350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (553/6250 : ℝ)) (hi := (18039/100000 : ℝ)) (c := (252461985083402069/252500000000000000 : ℝ)) (alpha := (31367887093/35350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (252461985083402069/252500000000000000 : ℝ)*(X 0 1+X 2 1)+(31367887093/35350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (553/6250 : ℝ)) (hi := (18039/100000 : ℝ)) (c := (252461985083402069/252500000000000000 : ℝ)) (alpha := (31367887093/35350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (252461985083402069/252500000000000000 : ℝ)*(X 0 2+X 1 2)+(31367887093/35350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (553/6250 : ℝ)) (hi := (18039/100000 : ℝ)) (c := (252461985083402069/252500000000000000 : ℝ)) (alpha := (31367887093/35350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1740886217/10000000000 : ℝ)*X 0 0+(2736745293/5000000000 : ℝ)*X 0 1+(5171088961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071628371/2000000000 : ℝ)*X 1 0+(-189722369/1000000000 : ℝ)*X 1 1+(2585544397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358141673/10000000000 : ℝ)*X 2 0+(5171089109/10000000000 : ℝ)*X 2 1+(-379444703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((422382887/1000000000 : ℝ)*X 0 0+(3871977993/10000000000 : ℝ)*X 0 1+(4600425873/10000000000 : ℝ)*X 0 2+(422382887/1000000000 : ℝ)*X 1 0+(3871977993/10000000000 : ℝ)*X 1 1+(4600425873/10000000000 : ℝ)*X 1 2+(422382887/1000000000 : ℝ)*X 2 0+(3871977993/10000000000 : ℝ)*X 2 1+(4600425873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-870486519/5000000000 : ℝ)*X 0 0+(5173457913/10000000000 : ℝ)*X 0 1+(5471095461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527804719/1000000000 : ℝ)*X 1 0+(-798608557/5000000000 : ℝ)*X 1 1+(547109557/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329877959/625000000 : ℝ)*X 2 0+(1094219061/2000000000 : ℝ)*X 2 1+(-199652159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((66000603/156250000 : ℝ)*X 0 0+(918944013/2000000000 : ℝ)*X 0 1+(15147451/39062500 : ℝ)*X 0 2+(66000603/156250000 : ℝ)*X 1 0+(918944013/2000000000 : ℝ)*X 1 1+(15147451/39062500 : ℝ)*X 1 2+(66000603/156250000 : ℝ)*X 2 0+(918944013/2000000000 : ℝ)*X 2 1+(15147451/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11709913183117462601735409/4418750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374801807/100000000000000 : ℝ)*(base19) + (242830579/100000000000000 : ℝ)*(base23) + (5263547/50000000000000 : ℝ)*(lower2) + (891407/6250000000000 : ℝ)*(upper3) + (6549757/6250000000000 : ℝ)*(upper5) + (233982496546041/10000000000000 : ℝ)*(major0) + (233982496546041/10000000000000 : ℝ)*(major1) + (233982496546041/10000000000000 : ℝ)*(major2) + (826715634595049/25000000000000 : ℝ)*(sp0) + (826716470051851/25000000000000 : ℝ)*(sp1) + (3306866012178631/100000000000000 : ℝ)*(sp2) + (1372783091488707/100000000000000 : ℝ)*(sp3) + (3716629013/100000000000000 : ℝ)*(sp4) + (496087859/100000000000000 : ℝ)*(sp7) + (686391793788283/50000000000000 : ℝ)*(f.failure) + (330686625500921/10000000000000 : ℝ)*(f.sum) + (720321982073/176750000000000000000000000 : ℝ)*base66 + (15509273853336803/17675000000000000000000000000000 : ℝ)*base67 + (62317262338438197/17675000000000000000000000000000 : ℝ)*base70 + (180256188018888197/17675000000000000000000000000000 : ℝ)*base72 + (85891409883/70700000000000000000000000 : ℝ)*base74 + (232322560585663197/17675000000000000000000000000000 : ℝ)*base76 + (194889236438913197/17675000000000000000000000000000 : ℝ)*base78 + (101880388476113197/17675000000000000000000000000000 : ℝ)*base80 + (1124483942199/353500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (45008739/5000000000000000000000 : ℝ)*base89 + (45008739/5000000000000000000000 : ℝ)*base91 + (45008739/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526054062800416173874785129/44187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (653734543/50000000000000 : ℝ)*(base19) + (1715949933/100000000000000 : ℝ)*(base23) + (57015557/25000000000000 : ℝ)*(upper3) + (18150669/12500000000000 : ℝ)*(lower4) + (173820477/100000000000000 : ℝ)*(upper5) + (1188635555629107/50000000000000 : ℝ)*(major0) + (1188635555629107/50000000000000 : ℝ)*(major1) + (1188635555629107/50000000000000 : ℝ)*(major2) + (333908891/2500000000000 : ℝ)*(sp1) + (15685172091/100000000000000 : ℝ)*(sp2) + (3359788451848417/100000000000000 : ℝ)*(sp4) + (335977378802369/10000000000000 : ℝ)*(sp5) + (1679885525363197/50000000000000 : ℝ)*(sp6) + (1394753373833253/100000000000000 : ℝ)*(sp7) + (1394753373833253/100000000000000 : ℝ)*(f.failure) + (3359788451848417/100000000000000 : ℝ)*(f.sum) + (4922423376873/1767500000000000000000000000 : ℝ)*base66 + (744607899654743319/88375000000000000000000000000000 : ℝ)*base68 + (678122895701368319/88375000000000000000000000000000 : ℝ)*base70 + (604343333700993319/88375000000000000000000000000000 : ℝ)*base72 + (902047244829/3535000000000000000000000000 : ℝ)*base73 + (394263829408993319/88375000000000000000000000000000 : ℝ)*base76 + (1000157502782618319/88375000000000000000000000000000 : ℝ)*base78 + (1735173524801743319/88375000000000000000000000000000 : ℝ)*base80 + (15274727484579/3535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (144178749/10000000000000000000000 : ℝ)*base89 + (144178749/10000000000000000000000 : ℝ)*base91 + (144178749/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1595_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1595_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1595_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1595_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1595_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

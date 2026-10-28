-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:01.487797+00:00
-- url     : https://prove2.me/submissions/761f32c1-b750-4c07-b407-0c8ca920e591

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
theorem support_rectangle_w1228_s0_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-372977517/2000000000 : ℝ)*x 0 + (1508666561/2500000000 : ℝ)*x 1 + (2395625807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372977517/2000000000 : ℝ)^8421 ≤ (543554032737/5000000000000 : ℝ)^6373 := by
    have hnat : (372977517 : ℕ)^8421*5000000000000^6373 ≤ 543554032737^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372977517 2000000000 543554032737 5000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1508666561/2500000000 : ℝ)^8421 ≤ (25652809104329/50000000000000 : ℝ)^6373 := by
    have hnat : (1508666561 : ℕ)^8421*50000000000000^6373 ≤ 25652809104329^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508666561 2500000000 25652809104329 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395625807/5000000000 : ℝ)^8421 ≤ (7564660222331/20000000000000 : ℝ)^6373 := by
    have hnat : (2395625807 : ℕ)^8421*20000000000000^6373 ≤ 7564660222331^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395625807 5000000000 7564660222331 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372977517/2000000000 : ℝ), (1508666561/2500000000 : ℝ), (2395625807/5000000000 : ℝ)] ![(543554032737/5000000000000 : ℝ), (25652809104329/50000000000000 : ℝ), (7564660222331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372977517/2000000000 : ℝ)|^8421 ≤ (543554032737/5000000000000 : ℝ)^6373
        have hw : |(-372977517/2000000000 : ℝ)|=(372977517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1508666561/2500000000 : ℝ)|^8421 ≤ (25652809104329/50000000000000 : ℝ)^6373
        have hw : |(1508666561/2500000000 : ℝ)|=(1508666561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395625807/5000000000 : ℝ)|^8421 ≤ (7564660222331/20000000000000 : ℝ)^6373
        have hw : |(2395625807/5000000000 : ℝ)|=(2395625807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5511948233/10000000000 : ℝ)*x 0 + (-20608773/80000000 : ℝ)*x 1 + (4791251567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511948233/10000000000 : ℝ)^8421 ≤ (4551683481133/10000000000000 : ℝ)^6373 := by
    have hnat : (5511948233 : ℕ)^8421*10000000000000^6373 ≤ 4551683481133^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511948233 10000000000 4551683481133 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20608773/80000000 : ℝ)^8421 ≤ (260310383597/1562500000000 : ℝ)^6373 := by
    have hnat : (20608773 : ℕ)^8421*1562500000000^6373 ≤ 260310383597^6373*80000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20608773 80000000 260310383597 1562500000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791251567/10000000000 : ℝ)^8421 ≤ (37823300621393/100000000000000 : ℝ)^6373 := by
    have hnat : (4791251567 : ℕ)^8421*100000000000000^6373 ≤ 37823300621393^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791251567 10000000000 37823300621393 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511948233/10000000000 : ℝ), (-20608773/80000000 : ℝ), (4791251567/10000000000 : ℝ)] ![(4551683481133/10000000000000 : ℝ), (260310383597/1562500000000 : ℝ), (37823300621393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511948233/10000000000 : ℝ)|^8421 ≤ (4551683481133/10000000000000 : ℝ)^6373
        have hw : |(5511948233/10000000000 : ℝ)|=(5511948233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20608773/80000000 : ℝ)|^8421 ≤ (260310383597/1562500000000 : ℝ)^6373
        have hw : |(-20608773/80000000 : ℝ)|=(20608773/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791251567/10000000000 : ℝ)|^8421 ≤ (37823300621393/100000000000000 : ℝ)^6373
        have hw : |(4791251567/10000000000 : ℝ)|=(4791251567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755974091/5000000000 : ℝ)*x 0 + (2395625813/5000000000 : ℝ)*x 1 + (-1288048309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755974091/5000000000 : ℝ)^8421 ≤ (1137920856371/2500000000000 : ℝ)^6373 := by
    have hnat : (2755974091 : ℕ)^8421*2500000000000^6373 ≤ 1137920856371^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755974091 5000000000 1137920856371 2500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2395625813/5000000000 : ℝ)^8421 ≤ (9455825309207/25000000000000 : ℝ)^6373 := by
    have hnat : (2395625813 : ℕ)^8421*25000000000000^6373 ≤ 9455825309207^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395625813 5000000000 9455825309207 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288048309/5000000000 : ℝ)^8421 ≤ (1665986449039/10000000000000 : ℝ)^6373 := by
    have hnat : (1288048309 : ℕ)^8421*10000000000000^6373 ≤ 1665986449039^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288048309 5000000000 1665986449039 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755974091/5000000000 : ℝ), (2395625813/5000000000 : ℝ), (-1288048309/5000000000 : ℝ)] ![(1137920856371/2500000000000 : ℝ), (9455825309207/25000000000000 : ℝ), (1665986449039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755974091/5000000000 : ℝ)|^8421 ≤ (1137920856371/2500000000000 : ℝ)^6373
        have hw : |(2755974091/5000000000 : ℝ)|=(2755974091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2395625813/5000000000 : ℝ)|^8421 ≤ (9455825309207/25000000000000 : ℝ)^6373
        have hw : |(2395625813/5000000000 : ℝ)|=(2395625813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288048309/5000000000 : ℝ)|^8421 ≤ (1665986449039/10000000000000 : ℝ)^6373
        have hw : |(-1288048309/5000000000 : ℝ)|=(1288048309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4194123307/10000000000 : ℝ)*x 0 + (3117424501/10000000000 : ℝ)*x 1 + (5632961891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194123307/10000000000 : ℝ)^8421 ≤ (15861519463779/50000000000000 : ℝ)^6373 := by
    have hnat : (4194123307 : ℕ)^8421*50000000000000^6373 ≤ 15861519463779^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194123307 10000000000 15861519463779 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117424501/10000000000 : ℝ)^8421 ≤ (21435043829861/100000000000000 : ℝ)^6373 := by
    have hnat : (3117424501 : ℕ)^8421*100000000000000^6373 ≤ 21435043829861^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117424501 10000000000 21435043829861 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5632961891/10000000000 : ℝ)^8421 ≤ (46841917227841/100000000000000 : ℝ)^6373 := by
    have hnat : (5632961891 : ℕ)^8421*100000000000000^6373 ≤ 46841917227841^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632961891 10000000000 46841917227841 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194123307/10000000000 : ℝ), (3117424501/10000000000 : ℝ), (5632961891/10000000000 : ℝ)] ![(15861519463779/50000000000000 : ℝ), (21435043829861/100000000000000 : ℝ), (46841917227841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194123307/10000000000 : ℝ)|^8421 ≤ (15861519463779/50000000000000 : ℝ)^6373
        have hw : |(4194123307/10000000000 : ℝ)|=(4194123307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117424501/10000000000 : ℝ)|^8421 ≤ (21435043829861/100000000000000 : ℝ)^6373
        have hw : |(3117424501/10000000000 : ℝ)|=(3117424501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5632961891/10000000000 : ℝ)|^8421 ≤ (46841917227841/100000000000000 : ℝ)^6373
        have hw : |(5632961891/10000000000 : ℝ)|=(5632961891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869784881/10000000000 : ℝ)*x 0 + (4823279319/10000000000 : ℝ)*x 1 + (6001506867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869784881/10000000000 : ℝ)^8421 ≤ (545440934413/5000000000000 : ℝ)^6373 := by
    have hnat : (1869784881 : ℕ)^8421*5000000000000^6373 ≤ 545440934413^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869784881 10000000000 545440934413 5000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823279319/10000000000 : ℝ)^8421 ≤ (1907887183239/5000000000000 : ℝ)^6373 := by
    have hnat : (4823279319 : ℕ)^8421*5000000000000^6373 ≤ 1907887183239^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823279319 10000000000 1907887183239 5000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6001506867/10000000000 : ℝ)^8421 ≤ (25466718819411/50000000000000 : ℝ)^6373 := by
    have hnat : (6001506867 : ℕ)^8421*50000000000000^6373 ≤ 25466718819411^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6001506867 10000000000 25466718819411 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869784881/10000000000 : ℝ), (4823279319/10000000000 : ℝ), (6001506867/10000000000 : ℝ)] ![(545440934413/5000000000000 : ℝ), (1907887183239/5000000000000 : ℝ), (25466718819411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869784881/10000000000 : ℝ)|^8421 ≤ (545440934413/5000000000000 : ℝ)^6373
        have hw : |(-1869784881/10000000000 : ℝ)|=(1869784881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823279319/10000000000 : ℝ)|^8421 ≤ (1907887183239/5000000000000 : ℝ)^6373
        have hw : |(4823279319/10000000000 : ℝ)|=(4823279319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6001506867/10000000000 : ℝ)|^8421 ≤ (25466718819411/50000000000000 : ℝ)^6373
        have hw : |(6001506867/10000000000 : ℝ)|=(6001506867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173692507/10000000000 : ℝ)*x 0 + (-170730217/1250000000 : ℝ)*x 1 + (6001506789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173692507/10000000000 : ℝ)^8421 ≤ (20931425576199/50000000000000 : ℝ)^6373 := by
    have hnat : (5173692507 : ℕ)^8421*50000000000000^6373 ≤ 20931425576199^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173692507 10000000000 20931425576199 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170730217/1250000000 : ℝ)^8421 ≤ (7203712074843/100000000000000 : ℝ)^6373 := by
    have hnat : (170730217 : ℕ)^8421*100000000000000^6373 ≤ 7203712074843^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170730217 1250000000 7203712074843 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6001506789/10000000000 : ℝ)^8421 ≤ (25466718382063/50000000000000 : ℝ)^6373 := by
    have hnat : (6001506789 : ℕ)^8421*50000000000000^6373 ≤ 25466718382063^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6001506789 10000000000 25466718382063 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173692507/10000000000 : ℝ), (-170730217/1250000000 : ℝ), (6001506789/10000000000 : ℝ)] ![(20931425576199/50000000000000 : ℝ), (7203712074843/100000000000000 : ℝ), (25466718382063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173692507/10000000000 : ℝ)|^8421 ≤ (20931425576199/50000000000000 : ℝ)^6373
        have hw : |(5173692507/10000000000 : ℝ)|=(5173692507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170730217/1250000000 : ℝ)|^8421 ≤ (7203712074843/100000000000000 : ℝ)^6373
        have hw : |(-170730217/1250000000 : ℝ)|=(170730217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6001506789/10000000000 : ℝ)|^8421 ≤ (25466718382063/50000000000000 : ℝ)^6373
        have hw : |(6001506789/10000000000 : ℝ)|=(6001506789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173692483/10000000000 : ℝ)*x 0 + (1500376717/2500000000 : ℝ)*x 1 + (-273168329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173692483/10000000000 : ℝ)^8421 ≤ (10465712723949/25000000000000 : ℝ)^6373 := by
    have hnat : (5173692483 : ℕ)^8421*25000000000000^6373 ≤ 10465712723949^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173692483 10000000000 10465712723949 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500376717/2500000000 : ℝ)^8421 ≤ (12733359412509/25000000000000 : ℝ)^6373 := by
    have hnat : (1500376717 : ℕ)^8421*25000000000000^6373 ≤ 12733359412509^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500376717 2500000000 12733359412509 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273168329/2000000000 : ℝ)^8421 ≤ (7203711440657/100000000000000 : ℝ)^6373 := by
    have hnat : (273168329 : ℕ)^8421*100000000000000^6373 ≤ 7203711440657^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273168329 2000000000 7203711440657 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173692483/10000000000 : ℝ), (1500376717/2500000000 : ℝ), (-273168329/2000000000 : ℝ)] ![(10465712723949/25000000000000 : ℝ), (12733359412509/25000000000000 : ℝ), (7203711440657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173692483/10000000000 : ℝ)|^8421 ≤ (10465712723949/25000000000000 : ℝ)^6373
        have hw : |(5173692483/10000000000 : ℝ)|=(5173692483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500376717/2500000000 : ℝ)|^8421 ≤ (12733359412509/25000000000000 : ℝ)^6373
        have hw : |(1500376717/2500000000 : ℝ)|=(1500376717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273168329/2000000000 : ℝ)|^8421 ≤ (7203711440657/100000000000000 : ℝ)^6373
        have hw : |(-273168329/2000000000 : ℝ)|=(273168329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s0_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4204030647/10000000000 : ℝ)*x 0 + (5568166567/10000000000 : ℝ)*x 1 + (796127323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204030647/10000000000 : ℝ)^8421 ≤ (6364418727207/20000000000000 : ℝ)^6373 := by
    have hnat : (4204030647 : ℕ)^8421*20000000000000^6373 ≤ 6364418727207^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204030647 10000000000 6364418727207 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5568166567/10000000000 : ℝ)^8421 ≤ (9226253455601/20000000000000 : ℝ)^6373 := by
    have hnat : (5568166567 : ℕ)^8421*20000000000000^6373 ≤ 9226253455601^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5568166567 10000000000 9226253455601 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796127323/2500000000 : ℝ)^8421 ≤ (11023319530697/50000000000000 : ℝ)^6373 := by
    have hnat : (796127323 : ℕ)^8421*50000000000000^6373 ≤ 11023319530697^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796127323 2500000000 11023319530697 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204030647/10000000000 : ℝ), (5568166567/10000000000 : ℝ), (796127323/2500000000 : ℝ)] ![(6364418727207/20000000000000 : ℝ), (9226253455601/20000000000000 : ℝ), (11023319530697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204030647/10000000000 : ℝ)|^8421 ≤ (6364418727207/20000000000000 : ℝ)^6373
        have hw : |(4204030647/10000000000 : ℝ)|=(4204030647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5568166567/10000000000 : ℝ)|^8421 ≤ (9226253455601/20000000000000 : ℝ)^6373
        have hw : |(5568166567/10000000000 : ℝ)|=(5568166567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796127323/2500000000 : ℝ)|^8421 ≤ (11023319530697/50000000000000 : ℝ)^6373
        have hw : |(796127323/2500000000 : ℝ)|=(796127323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (381/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27489/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2105/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2105 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2105*1^512 ≤ 0^512*1^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2105/512 : ℝ) ≤ (231173501038749939/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2105 ≤ (231173501038749939/10000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2105*10000000000000000000^512 ≤ 231173501038749939^512*5^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 231173501038749939 10000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (231173501038749939/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2105 := by
      have hnat : (1 : ℕ)^512*1^2105 ≤ 1^2105*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10231173501038749939/10000000000000000000 : ℝ) ≤ (9820061653977/9765625000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (10231173501038749939/10000000000000000000 : ℝ)^512 ≤ (9820061653977/9765625000000 : ℝ)^2105 := by
      have hnat : (10231173501038749939 : ℕ)^512*9765625000000^2105 ≤ 9820061653977^2105*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10231173501038749939 10000000000000000000 9820061653977 9765625000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9820061653977/9765625000000 : ℝ)) (X := (10231173501038749939/10000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5231173501038749939/5000000000000000000 : ℝ) ≤ (4937249153977/4882812500000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (5231173501038749939/5000000000000000000 : ℝ)^512 ≤ (4937249153977/4882812500000 : ℝ)^2105 := by
      have hnat : (5231173501038749939 : ℕ)^512*4882812500000^2105 ≤ 4937249153977^2105*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231173501038749939 5000000000000000000 4937249153977 4882812500000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4937249153977/4882812500000 : ℝ)) (X := (5231173501038749939/5000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54436653977/3906250000000 : ℝ)*(0 : ℝ))^(2105/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(54436653977/3906250000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231173501038749939/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54436653977/3906250000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (1 : ℝ)+(54436653977/3906250000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(9820061653977/9765625000000 : ℝ) by norm_num, show 1+(231173501038749939/10000000000000000000 : ℝ)+(0 : ℝ)=(10231173501038749939/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231173501038749939/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54436653977/3906250000000 : ℝ)*(2/5 : ℝ))^(2105/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(54436653977/3906250000000 : ℝ)*(2/5 : ℝ)=(4937249153977/4882812500000 : ℝ) by norm_num, show 1+2*(231173501038749939/10000000000000000000 : ℝ)=(5231173501038749939/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54436653977/3906250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54436653977/3906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54436653977/3906250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54436653977/3906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54436653977/3906250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54436653977/3906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-372977517/2000000000 : ℝ)*X 0 0+(1508666561/2500000000 : ℝ)*X 0 1+(2395625807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5511948233/10000000000 : ℝ)*X 1 0+(-20608773/80000000 : ℝ)*X 1 1+(4791251567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755974091/5000000000 : ℝ)*X 2 0+(2395625813/5000000000 : ℝ)*X 2 1+(-1288048309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194123307/10000000000 : ℝ)*X 0 0+(3117424501/10000000000 : ℝ)*X 0 1+(5632961891/10000000000 : ℝ)*X 0 2+(4194123307/10000000000 : ℝ)*X 1 0+(3117424501/10000000000 : ℝ)*X 1 1+(5632961891/10000000000 : ℝ)*X 1 2+(4194123307/10000000000 : ℝ)*X 2 0+(3117424501/10000000000 : ℝ)*X 2 1+(5632961891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1869784881/10000000000 : ℝ)*X 0 0+(4823279319/10000000000 : ℝ)*X 0 1+(6001506867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173692507/10000000000 : ℝ)*X 1 0+(-170730217/1250000000 : ℝ)*X 1 1+(6001506789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173692483/10000000000 : ℝ)*X 2 0+(1500376717/2500000000 : ℝ)*X 2 1+(-273168329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204030647/10000000000 : ℝ)*X 0 0+(5568166567/10000000000 : ℝ)*X 0 1+(796127323/2500000000 : ℝ)*X 0 2+(4204030647/10000000000 : ℝ)*X 1 0+(5568166567/10000000000 : ℝ)*X 1 1+(796127323/2500000000 : ℝ)*X 1 2+(4204030647/10000000000 : ℝ)*X 2 0+(5568166567/10000000000 : ℝ)*X 2 1+(796127323/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4110694799356369883007/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19506157/25000000000000 : ℝ)*(base1) + (1606194603/100000000000000 : ℝ)*(base19) + (11919127/800000000000 : ℝ)*(base23) + (27215589/25000000000000 : ℝ)*(base24) + (363682821/100000000000000 : ℝ)*(upper3) + (150222497200573/25000000000000 : ℝ)*(major0) + (150222497200573/25000000000000 : ℝ)*(major1) + (150222497200573/25000000000000 : ℝ)*(major2) + (80424239533883/10000000000000 : ℝ)*(sp0) + (100530534849617/12500000000000 : ℝ)*(sp1) + (201061071559577/25000000000000 : ℝ)*(sp2) + (99382751750841/25000000000000 : ℝ)*(sp3) + (3567677337/100000000000000 : ℝ)*(sp4) + (348543499/12500000000000 : ℝ)*(sp7) + (24845867085999/6250000000000 : ℝ)*(f.failure) + (804245884991539/100000000000000 : ℝ)*(f.sum) + (4312791646081/3125000000000000000000000000 : ℝ)*base66 + (11366954537103/3125000000000000000000000000 : ℝ)*base68 + (34601126212103/3125000000000000000000000000 : ℝ)*base70 + (6201251766307/781250000000000000000000000 : ℝ)*base72 + (97507054489/781250000000000000000000000 : ℝ)*base74 + (2341417422557/781250000000000000000000000 : ℝ)*base76 + (5145268928807/781250000000000000000000000 : ℝ)*base78 + (386432627443/781250000000000000000000000 : ℝ)*base79 + (3491598316989/781250000000000000000000000 : ℝ)*base82 + (1819397/156250000000000000000 : ℝ)*base89 + (1819397/156250000000000000000 : ℝ)*base91 + (1819397/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6265146664263029997207/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1734797/2500000000000 : ℝ)*(base1) + (1883574703/100000000000000 : ℝ)*(base19) + (939322409/50000000000000 : ℝ)*(base23) + (107037623/50000000000000 : ℝ)*(upper3) + (239840447/100000000000000 : ℝ)*(upper5) + (158532030879793/25000000000000 : ℝ)*(major0) + (158532030879793/25000000000000 : ℝ)*(major1) + (158532030879793/25000000000000 : ℝ)*(major2) + (2027692641/50000000000000 : ℝ)*(sp1) + (404020131/10000000000000 : ℝ)*(sp2) + (106091581549279/12500000000000 : ℝ)*(sp4) + (424363322021183/50000000000000 : ℝ)*(sp5) + (848726664156223/100000000000000 : ℝ)*(sp6) + (209761663665591/50000000000000 : ℝ)*(sp7) + (209761698361531/50000000000000 : ℝ)*(f.failure) + (848732583002351/100000000000000 : ℝ)*(f.sum) + (1101128310727/1562500000000000000000000000 : ℝ)*base65 + (5568195372551/1562500000000000000000000000 : ℝ)*base67 + (697966982897/195312500000000000000000000 : ℝ)*base69 + (5136769091301/1562500000000000000000000000 : ℝ)*base71 + (278734162669/195312500000000000000000000 : ℝ)*base73 + (6085095647213/781250000000000000000000000 : ℝ)*base75 + (17703438616977/3125000000000000000000000000 : ℝ)*base77 + (17093536597551/1562500000000000000000000000 : ℝ)*base79 + (4235574224579/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4568807/1250000000000000000000 : ℝ)*base90 + (4568807/1250000000000000000000 : ℝ)*base92 + (4568807/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1228_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s1_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063313597/10000000000 : ℝ)*x 0 + (709892899/1250000000 : ℝ)*x 1 + (5019759553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063313597/10000000000 : ℝ)^8421 ≤ (194140831681/1562500000000 : ℝ)^6373 := by
    have hnat : (2063313597 : ℕ)^8421*1562500000000^6373 ≤ 194140831681^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063313597 10000000000 194140831681 1562500000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709892899/1250000000 : ℝ)^8421 ≤ (47350023348187/100000000000000 : ℝ)^6373 := by
    have hnat : (709892899 : ℕ)^8421*100000000000000^6373 ≤ 47350023348187^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709892899 1250000000 47350023348187 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019759553/10000000000 : ℝ)^8421 ≤ (1257030106403/3125000000000 : ℝ)^6373 := by
    have hnat : (5019759553 : ℕ)^8421*3125000000000^6373 ≤ 1257030106403^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019759553 10000000000 1257030106403 3125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063313597/10000000000 : ℝ), (709892899/1250000000 : ℝ), (5019759553/10000000000 : ℝ)] ![(194140831681/1562500000000 : ℝ), (47350023348187/100000000000000 : ℝ), (1257030106403/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063313597/10000000000 : ℝ)|^8421 ≤ (194140831681/1562500000000 : ℝ)^6373
        have hw : |(-2063313597/10000000000 : ℝ)|=(2063313597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709892899/1250000000 : ℝ)|^8421 ≤ (47350023348187/100000000000000 : ℝ)^6373
        have hw : |(709892899/1250000000 : ℝ)|=(709892899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019759553/10000000000 : ℝ)|^8421 ≤ (1257030106403/3125000000000 : ℝ)^6373
        have hw : |(5019759553/10000000000 : ℝ)|=(5019759553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287521/9765625 : ℝ)*x 0 + (-2417635029/10000000000 : ℝ)*x 1 + (1254939901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287521/9765625 : ℝ)^8421 ≤ (44455704093103/100000000000000 : ℝ)^6373 := by
    have hnat : (5287521 : ℕ)^8421*100000000000000^6373 ≤ 44455704093103^6373*9765625^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287521 9765625 44455704093103 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417635029/10000000000 : ℝ)^8421 ≤ (15319331954537/100000000000000 : ℝ)^6373 := by
    have hnat : (2417635029 : ℕ)^8421*100000000000000^6373 ≤ 15319331954537^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417635029 10000000000 15319331954537 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254939901/2500000000 : ℝ)^8421 ≤ (40224963944907/100000000000000 : ℝ)^6373 := by
    have hnat : (1254939901 : ℕ)^8421*100000000000000^6373 ≤ 40224963944907^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254939901 2500000000 40224963944907 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287521/9765625 : ℝ), (-2417635029/10000000000 : ℝ), (1254939901/2500000000 : ℝ)] ![(44455704093103/100000000000000 : ℝ), (15319331954537/100000000000000 : ℝ), (40224963944907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287521/9765625 : ℝ)|^8421 ≤ (44455704093103/100000000000000 : ℝ)^6373
        have hw : |(5287521/9765625 : ℝ)|=(5287521/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2417635029/10000000000 : ℝ)|^8421 ≤ (15319331954537/100000000000000 : ℝ)^6373
        have hw : |(-2417635029/10000000000 : ℝ)|=(2417635029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254939901/2500000000 : ℝ)|^8421 ≤ (40224963944907/100000000000000 : ℝ)^6373
        have hw : |(1254939901/2500000000 : ℝ)|=(1254939901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2707210781/5000000000 : ℝ)*x 0 + (200790383/400000000 : ℝ)*x 1 + (-2417634989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707210781/5000000000 : ℝ)^8421 ≤ (44455704722353/100000000000000 : ℝ)^6373 := by
    have hnat : (2707210781 : ℕ)^8421*100000000000000^6373 ≤ 44455704722353^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707210781 5000000000 44455704722353 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200790383/400000000 : ℝ)^8421 ≤ (20112481818921/50000000000000 : ℝ)^6373 := by
    have hnat : (200790383 : ℕ)^8421*50000000000000^6373 ≤ 20112481818921^6373*400000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200790383 400000000 20112481818921 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417634989/10000000000 : ℝ)^8421 ≤ (7659665809813/50000000000000 : ℝ)^6373 := by
    have hnat : (2417634989 : ℕ)^8421*50000000000000^6373 ≤ 7659665809813^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417634989 10000000000 7659665809813 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707210781/5000000000 : ℝ), (200790383/400000000 : ℝ), (-2417634989/10000000000 : ℝ)] ![(44455704722353/100000000000000 : ℝ), (20112481818921/50000000000000 : ℝ), (7659665809813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707210781/5000000000 : ℝ)|^8421 ≤ (44455704722353/100000000000000 : ℝ)^6373
        have hw : |(2707210781/5000000000 : ℝ)|=(2707210781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200790383/400000000 : ℝ)|^8421 ≤ (20112481818921/50000000000000 : ℝ)^6373
        have hw : |(200790383/400000000 : ℝ)|=(200790383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2417634989/10000000000 : ℝ)|^8421 ≤ (7659665809813/50000000000000 : ℝ)^6373
        have hw : |(-2417634989/10000000000 : ℝ)|=(2417634989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155033669/5000000000 : ℝ)*x 0 + (738579817/2000000000 : ℝ)*x 1 + (1256722729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155033669/5000000000 : ℝ)^8421 ≤ (128464594601/390625000000 : ℝ)^6373 := by
    have hnat : (2155033669 : ℕ)^8421*390625000000^6373 ≤ 128464594601^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155033669 5000000000 128464594601 390625000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738579817/2000000000 : ℝ)^8421 ≤ (13406286512871/50000000000000 : ℝ)^6373 := by
    have hnat : (738579817 : ℕ)^8421*50000000000000^6373 ≤ 13406286512871^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738579817 2000000000 13406286512871 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256722729/2500000000 : ℝ)^8421 ≤ (40300490734127/100000000000000 : ℝ)^6373 := by
    have hnat : (1256722729 : ℕ)^8421*100000000000000^6373 ≤ 40300490734127^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256722729 2500000000 40300490734127 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155033669/5000000000 : ℝ), (738579817/2000000000 : ℝ), (1256722729/2500000000 : ℝ)] ![(128464594601/390625000000 : ℝ), (13406286512871/50000000000000 : ℝ), (40300490734127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155033669/5000000000 : ℝ)|^8421 ≤ (128464594601/390625000000 : ℝ)^6373
        have hw : |(2155033669/5000000000 : ℝ)|=(2155033669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(738579817/2000000000 : ℝ)|^8421 ≤ (13406286512871/50000000000000 : ℝ)^6373
        have hw : |(738579817/2000000000 : ℝ)|=(738579817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256722729/2500000000 : ℝ)|^8421 ≤ (40300490734127/100000000000000 : ℝ)^6373
        have hw : |(1256722729/2500000000 : ℝ)|=(1256722729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064007517/10000000000 : ℝ)*x 0 + (78569831/156250000 : ℝ)*x 1 + (2835133227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064007517/10000000000 : ℝ)^8421 ≤ (1553816884117/12500000000000 : ℝ)^6373 := by
    have hnat : (2064007517 : ℕ)^8421*12500000000000^6373 ≤ 1553816884117^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064007517 10000000000 1553816884117 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78569831/156250000 : ℝ)^8421 ≤ (8063442123781/20000000000000 : ℝ)^6373 := by
    have hnat : (78569831 : ℕ)^8421*20000000000000^6373 ≤ 8063442123781^6373*156250000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78569831 156250000 8063442123781 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835133227/5000000000 : ℝ)^8421 ≤ (47252254295907/100000000000000 : ℝ)^6373 := by
    have hnat : (2835133227 : ℕ)^8421*100000000000000^6373 ≤ 47252254295907^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835133227 5000000000 47252254295907 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064007517/10000000000 : ℝ), (78569831/156250000 : ℝ), (2835133227/5000000000 : ℝ)] ![(1553816884117/12500000000000 : ℝ), (8063442123781/20000000000000 : ℝ), (47252254295907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064007517/10000000000 : ℝ)|^8421 ≤ (1553816884117/12500000000000 : ℝ)^6373
        have hw : |(-2064007517/10000000000 : ℝ)|=(2064007517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78569831/156250000 : ℝ)|^8421 ≤ (8063442123781/20000000000000 : ℝ)^6373
        have hw : |(78569831/156250000 : ℝ)|=(78569831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835133227/5000000000 : ℝ)|^8421 ≤ (47252254295907/100000000000000 : ℝ)^6373
        have hw : |(2835133227/5000000000 : ℝ)|=(2835133227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622328567/5000000000 : ℝ)*x 0 + (-883563737/5000000000 : ℝ)*x 1 + (226810673/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622328567/5000000000 : ℝ)^8421 ≤ (21311626372201/50000000000000 : ℝ)^6373 := by
    have hnat : (2622328567 : ℕ)^8421*50000000000000^6373 ≤ 21311626372201^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622328567 5000000000 21311626372201 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883563737/5000000000 : ℝ)^8421 ≤ (5062244428611/50000000000000 : ℝ)^6373 := by
    have hnat : (883563737 : ℕ)^8421*50000000000000^6373 ≤ 5062244428611^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883563737 5000000000 5062244428611 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226810673/400000000 : ℝ)^8421 ≤ (47252258381101/100000000000000 : ℝ)^6373 := by
    have hnat : (226810673 : ℕ)^8421*100000000000000^6373 ≤ 47252258381101^6373*400000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226810673 400000000 47252258381101 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622328567/5000000000 : ℝ), (-883563737/5000000000 : ℝ), (226810673/400000000 : ℝ)] ![(21311626372201/50000000000000 : ℝ), (5062244428611/50000000000000 : ℝ), (47252258381101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622328567/5000000000 : ℝ)|^8421 ≤ (21311626372201/50000000000000 : ℝ)^6373
        have hw : |(2622328567/5000000000 : ℝ)|=(2622328567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883563737/5000000000 : ℝ)|^8421 ≤ (5062244428611/50000000000000 : ℝ)^6373
        have hw : |(-883563737/5000000000 : ℝ)|=(883563737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226810673/400000000 : ℝ)|^8421 ≤ (47252258381101/100000000000000 : ℝ)^6373
        have hw : |(226810673/400000000 : ℝ)|=(226810673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327791089/625000000 : ℝ)*x 0 + (5670267569/10000000000 : ℝ)*x 1 + (-1767125981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327791089/625000000 : ℝ)^8421 ≤ (42623255858607/100000000000000 : ℝ)^6373 := by
    have hnat : (327791089 : ℕ)^8421*100000000000000^6373 ≤ 42623255858607^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327791089 625000000 42623255858607 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5670267569/10000000000 : ℝ)^8421 ≤ (47252266573513/100000000000000 : ℝ)^6373 := by
    have hnat : (5670267569 : ℕ)^8421*100000000000000^6373 ≤ 47252266573513^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670267569 10000000000 47252266573513 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767125981/10000000000 : ℝ)^8421 ≤ (10124477554457/100000000000000 : ℝ)^6373 := by
    have hnat : (1767125981 : ℕ)^8421*100000000000000^6373 ≤ 10124477554457^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767125981 10000000000 10124477554457 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327791089/625000000 : ℝ), (5670267569/10000000000 : ℝ), (-1767125981/10000000000 : ℝ)] ![(42623255858607/100000000000000 : ℝ), (47252266573513/100000000000000 : ℝ), (10124477554457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327791089/625000000 : ℝ)|^8421 ≤ (42623255858607/100000000000000 : ℝ)^6373
        have hw : |(327791089/625000000 : ℝ)|=(327791089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5670267569/10000000000 : ℝ)|^8421 ≤ (47252266573513/100000000000000 : ℝ)^6373
        have hw : |(5670267569/10000000000 : ℝ)|=(5670267569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1767125981/10000000000 : ℝ)|^8421 ≤ (10124477554457/100000000000000 : ℝ)^6373
        have hw : |(-1767125981/10000000000 : ℝ)|=(1767125981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s1_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (431146939/1000000000 : ℝ)*x 0 + (2504635667/5000000000 : ℝ)*x 1 + (3710855777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431146939/1000000000 : ℝ)^8421 ≤ (16450536424529/50000000000000 : ℝ)^6373 := by
    have hnat : (431146939 : ℕ)^8421*50000000000000^6373 ≤ 16450536424529^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431146939 1000000000 16450536424529 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504635667/5000000000 : ℝ)^8421 ≤ (20056973348481/50000000000000 : ℝ)^6373 := by
    have hnat : (2504635667 : ℕ)^8421*50000000000000^6373 ≤ 20056973348481^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504635667 5000000000 20056973348481 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3710855777/10000000000 : ℝ)^8421 ≤ (2698498044149/10000000000000 : ℝ)^6373 := by
    have hnat : (3710855777 : ℕ)^8421*10000000000000^6373 ≤ 2698498044149^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710855777 10000000000 2698498044149 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431146939/1000000000 : ℝ), (2504635667/5000000000 : ℝ), (3710855777/10000000000 : ℝ)] ![(16450536424529/50000000000000 : ℝ), (20056973348481/50000000000000 : ℝ), (2698498044149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431146939/1000000000 : ℝ)|^8421 ≤ (16450536424529/50000000000000 : ℝ)^6373
        have hw : |(431146939/1000000000 : ℝ)|=(431146939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504635667/5000000000 : ℝ)|^8421 ≤ (20056973348481/50000000000000 : ℝ)^6373
        have hw : |(2504635667/5000000000 : ℝ)|=(2504635667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3710855777/10000000000 : ℝ)|^8421 ≤ (2698498044149/10000000000000 : ℝ)^6373
        have hw : |(3710855777/10000000000 : ℝ)|=(3710855777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6117/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (381/50000 : ℝ) ^ (2105/512 : ℝ) ≤ (97947173519/50000000000000000000 : ℝ) := by
    have hpowers : (381/50000 : ℝ)^2105 ≤ (97947173519/50000000000000000000 : ℝ)^512 := by
      have hnat : (381 : ℕ)^2105*50000000000000000000^512 ≤ 97947173519^512*50000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 50000 97947173519 50000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/50000 : ℝ)) (X := (97947173519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27489/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (247268267527218561/50000000000000000000 : ℝ) := by
    have hpowers : (27489/100000 : ℝ)^2105 ≤ (247268267527218561/50000000000000000000 : ℝ)^512 := by
      have hnat : (27489 : ℕ)^2105*50000000000000000000^512 ≤ 247268267527218561^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27489 100000 247268267527218561 50000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27489/100000 : ℝ)) (X := (247268267527218561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000097947173519/25000000000000000000 : ℝ) ≤ (10000000009529493/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25000000097947173519/25000000000000000000 : ℝ)^512 ≤ (10000000009529493/10000000000000000 : ℝ)^2105 := by
      have hnat : (25000000097947173519 : ℕ)^512*10000000000000000^2105 ≤ 10000000009529493^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000097947173519 25000000000000000000 10000000009529493 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000009529493/10000000000000000 : ℝ)) (X := (25000000097947173519/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (628090854568429901/625000000000000000 : ℝ) ≤ (2503001548307591/2500000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (628090854568429901/625000000000000000 : ℝ)^512 ≤ (2503001548307591/2500000000000000 : ℝ)^2105 := by
      have hnat : (628090854568429901 : ℕ)^512*2500000000000000^2105 ≤ 2503001548307591^2105*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        628090854568429901 625000000000000000 2503001548307591 2500000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503001548307591/2500000000000000 : ℝ)) (X := (628090854568429901/625000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25247268267527218561/25000000000000000000 : ℝ) ≤ (2004802475386247/2000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25247268267527218561/25000000000000000000 : ℝ)^512 ≤ (2004802475386247/2000000000000000 : ℝ)^2105 := by
      have hnat : (25247268267527218561 : ℕ)^512*2000000000000000^2105 ≤ 2004802475386247^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25247268267527218561 25000000000000000000 2004802475386247 2000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004802475386247/2000000000000000 : ℝ)) (X := (25247268267527218561/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(97947173519/50000000000000000000 : ℝ) ≤ ((89083900943578210669/89090000000000000000 : ℝ)+2*(12006183700871/2672700000000000 : ℝ)*(381/50000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (89083900943578210669/89090000000000000000 : ℝ)+2*(12006183700871/2672700000000000 : ℝ)*(381/50000 : ℝ)=(10000000009529493/10000000000000000 : ℝ) by norm_num, show 1+2*(97947173519/50000000000000000000 : ℝ)=(25000000097947173519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(247268267527218561/50000000000000000000 : ℝ)+(97947173519/50000000000000000000 : ℝ) ≤ ((89083900943578210669/89090000000000000000 : ℝ)+(12006183700871/2672700000000000 : ℝ)*((27489/100000 : ℝ)+(381/50000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (89083900943578210669/89090000000000000000 : ℝ)+(12006183700871/2672700000000000 : ℝ)*((27489/100000 : ℝ)+(381/50000 : ℝ))=(2503001548307591/2500000000000000 : ℝ) by norm_num, show 1+(247268267527218561/50000000000000000000 : ℝ)+(97947173519/50000000000000000000 : ℝ)=(628090854568429901/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(247268267527218561/50000000000000000000 : ℝ) ≤ ((89083900943578210669/89090000000000000000 : ℝ)+2*(12006183700871/2672700000000000 : ℝ)*(27489/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (89083900943578210669/89090000000000000000 : ℝ)+2*(12006183700871/2672700000000000 : ℝ)*(27489/100000 : ℝ)=(2004802475386247/2000000000000000 : ℝ) by norm_num, show 1+2*(247268267527218561/50000000000000000000 : ℝ)=(25247268267527218561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89083900943578210669/89090000000000000000 : ℝ)*(X 1 0+X 2 0)+(12006183700871/2672700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (381/50000 : ℝ)) (hi := (27489/100000 : ℝ)) (c := (89083900943578210669/89090000000000000000 : ℝ)) (alpha := (12006183700871/2672700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89083900943578210669/89090000000000000000 : ℝ)*(X 0 1+X 2 1)+(12006183700871/2672700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (381/50000 : ℝ)) (hi := (27489/100000 : ℝ)) (c := (89083900943578210669/89090000000000000000 : ℝ)) (alpha := (12006183700871/2672700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89083900943578210669/89090000000000000000 : ℝ)*(X 0 2+X 1 2)+(12006183700871/2672700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (381/50000 : ℝ)) (hi := (27489/100000 : ℝ)) (c := (89083900943578210669/89090000000000000000 : ℝ)) (alpha := (12006183700871/2672700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063313597/10000000000 : ℝ)*X 0 0+(709892899/1250000000 : ℝ)*X 0 1+(5019759553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5287521/9765625 : ℝ)*X 1 0+(-2417635029/10000000000 : ℝ)*X 1 1+(1254939901/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707210781/5000000000 : ℝ)*X 2 0+(200790383/400000000 : ℝ)*X 2 1+(-2417634989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155033669/5000000000 : ℝ)*X 0 0+(738579817/2000000000 : ℝ)*X 0 1+(1256722729/2500000000 : ℝ)*X 0 2+(2155033669/5000000000 : ℝ)*X 1 0+(738579817/2000000000 : ℝ)*X 1 1+(1256722729/2500000000 : ℝ)*X 1 2+(2155033669/5000000000 : ℝ)*X 2 0+(738579817/2000000000 : ℝ)*X 2 1+(1256722729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064007517/10000000000 : ℝ)*X 0 0+(78569831/156250000 : ℝ)*X 0 1+(2835133227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622328567/5000000000 : ℝ)*X 1 0+(-883563737/5000000000 : ℝ)*X 1 1+(226810673/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327791089/625000000 : ℝ)*X 2 0+(5670267569/10000000000 : ℝ)*X 2 1+(-1767125981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431146939/1000000000 : ℝ)*X 0 0+(2504635667/5000000000 : ℝ)*X 0 1+(3710855777/10000000000 : ℝ)*X 0 2+(431146939/1000000000 : ℝ)*X 1 0+(2504635667/5000000000 : ℝ)*X 1 1+(3710855777/10000000000 : ℝ)*X 1 2+(431146939/1000000000 : ℝ)*X 2 0+(2504635667/5000000000 : ℝ)*X 2 1+(3710855777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26309541112617640726643463/3775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8031109/10000000000000 : ℝ)*(base1) + (763350993/50000000000000 : ℝ)*(base19) + (96434239/6250000000000 : ℝ)*(base23) + (1042201/625000000000 : ℝ)*(upper3) + (46406879/25000000000000 : ℝ)*(upper5) + (56655580136777/5000000000000 : ℝ)*(major0) + (56655580136777/5000000000000 : ℝ)*(major1) + (56655580136777/5000000000000 : ℝ)*(major2) + (1516575971770351/100000000000000 : ℝ)*(sp0) + (758291494419561/50000000000000 : ℝ)*(sp1) + (379145743148321/25000000000000 : ℝ)*(sp2) + (149926810646897/20000000000000 : ℝ)*(sp3) + (8624081847/100000000000000 : ℝ)*(sp4) + (2162035281/50000000000000 : ℝ)*(sp7) + (93704807202017/12500000000000 : ℝ)*(f.failure) + (379146128885277/25000000000000 : ℝ)*(f.sum) + (2025034701133/1336350000000000000000000000 : ℝ)*base66 + (9480377698739828561/1336350000000000000000000000000000 : ℝ)*base68 + (8263002140102528561/1336350000000000000000000000000000 : ℝ)*base70 + (6440059072488578561/1336350000000000000000000000000000 : ℝ)*base72 + (133194466423097/26727000000000000000000000000 : ℝ)*base74 + (3080040890810978561/1336350000000000000000000000000000 : ℝ)*base76 + (3490347241350578561/1336350000000000000000000000000000 : ℝ)*base78 + (8060226606770828561/1336350000000000000000000000000000 : ℝ)*base80 + (77006727033049/13363500000000000000000000000 : ℝ)*base82 + (1287749/312500000000000000000 : ℝ)*base90 + (1287749/312500000000000000000 : ℝ)*base92 + (1287749/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143706507165411911282470473/18875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1154202277/50000000000000 : ℝ)*(base19) + (2731472871/100000000000000 : ℝ)*(base23) + (41819789/50000000000000 : ℝ)*(upper2) + (22487481/6250000000000 : ℝ)*(upper3) + (180950293/100000000000000 : ℝ)*(upper5) + (291036654540433/25000000000000 : ℝ)*(major0) + (291036654540433/25000000000000 : ℝ)*(major1) + (291036654540433/25000000000000 : ℝ)*(major2) + (214443193/2000000000000 : ℝ)*(sp1) + (16203884147/100000000000000 : ℝ)*(sp2) + (779061265254213/50000000000000 : ℝ)*(sp4) + (779054749972111/50000000000000 : ℝ)*(sp5) + (97381474696963/6250000000000 : ℝ)*(sp6) + (154034090405741/20000000000000 : ℝ)*(sp7) + (154034090405741/20000000000000 : ℝ)*(f.failure) + (779061265254213/50000000000000 : ℝ)*(f.sum) + (15314075502499/16704375000000000000000000000 : ℝ)*base65 + (1300817813957239031/6681750000000000000000000000000000 : ℝ)*base67 + (23971104652820989031/6681750000000000000000000000000000 : ℝ)*base69 + (27974721661760239031/6681750000000000000000000000000000 : ℝ)*base71 + (42170684234663/33408750000000000000000000000 : ℝ)*base73 + (20271604454935489031/6681750000000000000000000000000000 : ℝ)*base75 + (19672398338118739031/6681750000000000000000000000000000 : ℝ)*base77 + (44547106381204489031/6681750000000000000000000000000000 : ℝ)*base79 + (113980224204391/66817500000000000000000000000 : ℝ)*base81 + (4430177/500000000000000000000 : ℝ)*base90 + (4430177/500000000000000000000 : ℝ)*base92 + (4430177/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1228_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s2_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112060731/10000000000 : ℝ)*x 0 + (2747603691/5000000000 : ℝ)*x 1 + (323288747/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112060731/10000000000 : ℝ)^8421 ≤ (6407180312627/50000000000000 : ℝ)^6373 := by
    have hnat : (2112060731 : ℕ)^8421*50000000000000^6373 ≤ 6407180312627^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112060731 10000000000 6407180312627 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747603691/5000000000 : ℝ)^8421 ≤ (4533425528907/10000000000000 : ℝ)^6373 := by
    have hnat : (2747603691 : ℕ)^8421*10000000000000^6373 ≤ 4533425528907^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747603691 5000000000 4533425528907 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323288747/625000000 : ℝ)^8421 ≤ (8370276813417/20000000000000 : ℝ)^6373 := by
    have hnat : (323288747 : ℕ)^8421*20000000000000^6373 ≤ 8370276813417^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323288747 625000000 8370276813417 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112060731/10000000000 : ℝ), (2747603691/5000000000 : ℝ), (323288747/625000000 : ℝ)] ![(6407180312627/50000000000000 : ℝ), (4533425528907/10000000000000 : ℝ), (8370276813417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112060731/10000000000 : ℝ)|^8421 ≤ (6407180312627/50000000000000 : ℝ)^6373
        have hw : |(-2112060731/10000000000 : ℝ)|=(2112060731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747603691/5000000000 : ℝ)|^8421 ≤ (4533425528907/10000000000000 : ℝ)^6373
        have hw : |(2747603691/5000000000 : ℝ)|=(2747603691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323288747/625000000 : ℝ)|^8421 ≤ (8370276813417/20000000000000 : ℝ)^6373
        have hw : |(323288747/625000000 : ℝ)|=(323288747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685130227/5000000000 : ℝ)*x 0 + (-56981031/250000000 : ℝ)*x 1 + (5172619893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685130227/5000000000 : ℝ)^8421 ≤ (879544477413/2000000000000 : ℝ)^6373 := by
    have hnat : (2685130227 : ℕ)^8421*2000000000000^6373 ≤ 879544477413^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685130227 5000000000 879544477413 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56981031/250000000 : ℝ)^8421 ≤ (14171392683057/100000000000000 : ℝ)^6373 := by
    have hnat : (56981031 : ℕ)^8421*100000000000000^6373 ≤ 14171392683057^6373*250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56981031 250000000 14171392683057 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172619893/10000000000 : ℝ)^8421 ≤ (8370276687263/20000000000000 : ℝ)^6373 := by
    have hnat : (5172619893 : ℕ)^8421*20000000000000^6373 ≤ 8370276687263^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172619893 10000000000 8370276687263 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685130227/5000000000 : ℝ), (-56981031/250000000 : ℝ), (5172619893/10000000000 : ℝ)] ![(879544477413/2000000000000 : ℝ), (14171392683057/100000000000000 : ℝ), (8370276687263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685130227/5000000000 : ℝ)|^8421 ≤ (879544477413/2000000000000 : ℝ)^6373
        have hw : |(2685130227/5000000000 : ℝ)|=(2685130227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56981031/250000000 : ℝ)|^8421 ≤ (14171392683057/100000000000000 : ℝ)^6373
        have hw : |(-56981031/250000000 : ℝ)|=(56981031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172619893/10000000000 : ℝ)|^8421 ≤ (8370276687263/20000000000000 : ℝ)^6373
        have hw : |(5172619893/10000000000 : ℝ)|=(5172619893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074052053/2000000000 : ℝ)*x 0 + (5172620059/10000000000 : ℝ)*x 1 + (-2279241273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074052053/2000000000 : ℝ)^8421 ≤ (43977221825553/100000000000000 : ℝ)^6373 := by
    have hnat : (1074052053 : ℕ)^8421*100000000000000^6373 ≤ 43977221825553^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074052053 2000000000 43977221825553 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172620059/10000000000 : ℝ)^8421 ≤ (2615711575689/6250000000000 : ℝ)^6373 := by
    have hnat : (5172620059 : ℕ)^8421*6250000000000^6373 ≤ 2615711575689^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172620059 10000000000 2615711575689 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279241273/10000000000 : ℝ)^8421 ≤ (14171392954173/100000000000000 : ℝ)^6373 := by
    have hnat : (2279241273 : ℕ)^8421*100000000000000^6373 ≤ 14171392954173^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279241273 10000000000 14171392954173 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074052053/2000000000 : ℝ), (5172620059/10000000000 : ℝ), (-2279241273/10000000000 : ℝ)] ![(43977221825553/100000000000000 : ℝ), (2615711575689/6250000000000 : ℝ), (14171392954173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074052053/2000000000 : ℝ)|^8421 ≤ (43977221825553/100000000000000 : ℝ)^6373
        have hw : |(1074052053/2000000000 : ℝ)|=(1074052053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172620059/10000000000 : ℝ)|^8421 ≤ (2615711575689/6250000000000 : ℝ)^6373
        have hw : |(5172620059/10000000000 : ℝ)|=(5172620059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279241273/10000000000 : ℝ)|^8421 ≤ (14171392954173/100000000000000 : ℝ)^6373
        have hw : |(-2279241273/10000000000 : ℝ)|=(2279241273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2171854391/5000000000 : ℝ)*x 0 + (402930653/1000000000 : ℝ)*x 1 + (4681929597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171854391/5000000000 : ℝ)^8421 ≤ (33226543587891/100000000000000 : ℝ)^6373 := by
    have hnat : (2171854391 : ℕ)^8421*100000000000000^6373 ≤ 33226543587891^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171854391 5000000000 33226543587891 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402930653/1000000000 : ℝ)^8421 ≤ (3008630190341/10000000000000 : ℝ)^6373 := by
    have hnat : (402930653 : ℕ)^8421*10000000000000^6373 ≤ 3008630190341^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402930653 1000000000 3008630190341 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4681929597/10000000000 : ℝ)^8421 ≤ (36687154501793/100000000000000 : ℝ)^6373 := by
    have hnat : (4681929597 : ℕ)^8421*100000000000000^6373 ≤ 36687154501793^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4681929597 10000000000 36687154501793 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171854391/5000000000 : ℝ), (402930653/1000000000 : ℝ), (4681929597/10000000000 : ℝ)] ![(33226543587891/100000000000000 : ℝ), (3008630190341/10000000000000 : ℝ), (36687154501793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171854391/5000000000 : ℝ)|^8421 ≤ (33226543587891/100000000000000 : ℝ)^6373
        have hw : |(2171854391/5000000000 : ℝ)|=(2171854391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402930653/1000000000 : ℝ)|^8421 ≤ (3008630190341/10000000000000 : ℝ)^6373
        have hw : |(402930653/1000000000 : ℝ)|=(402930653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4681929597/10000000000 : ℝ)|^8421 ≤ (36687154501793/100000000000000 : ℝ)^6373
        have hw : |(4681929597/10000000000 : ℝ)|=(4681929597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422428427/2000000000 : ℝ)*x 0 + (1293678527/2500000000 : ℝ)*x 1 + (2746546707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422428427/2000000000 : ℝ)^8421 ≤ (12815013242767/100000000000000 : ℝ)^6373 := by
    have hnat : (422428427 : ℕ)^8421*100000000000000^6373 ≤ 12815013242767^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422428427 2000000000 12815013242767 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293678527/2500000000 : ℝ)^8421 ≤ (41873774179889/100000000000000 : ℝ)^6373 := by
    have hnat : (1293678527 : ℕ)^8421*100000000000000^6373 ≤ 41873774179889^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293678527 2500000000 41873774179889 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746546707/5000000000 : ℝ)^8421 ≤ (11327803142709/25000000000000 : ℝ)^6373 := by
    have hnat : (2746546707 : ℕ)^8421*25000000000000^6373 ≤ 11327803142709^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746546707 5000000000 11327803142709 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422428427/2000000000 : ℝ), (1293678527/2500000000 : ℝ), (2746546707/5000000000 : ℝ)] ![(12815013242767/100000000000000 : ℝ), (41873774179889/100000000000000 : ℝ), (11327803142709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422428427/2000000000 : ℝ)|^8421 ≤ (12815013242767/100000000000000 : ℝ)^6373
        have hw : |(-422428427/2000000000 : ℝ)|=(422428427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293678527/2500000000 : ℝ)|^8421 ≤ (41873774179889/100000000000000 : ℝ)^6373
        have hw : |(1293678527/2500000000 : ℝ)|=(1293678527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746546707/5000000000 : ℝ)|^8421 ≤ (11327803142709/25000000000000 : ℝ)^6373
        have hw : |(2746546707/5000000000 : ℝ)|=(2746546707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211518089/400000000 : ℝ)*x 0 + (-1958767541/10000000000 : ℝ)*x 1 + (5493093453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211518089/400000000 : ℝ)^8421 ≤ (538609982881/1250000000000 : ℝ)^6373 := by
    have hnat : (211518089 : ℕ)^8421*1250000000000^6373 ≤ 538609982881^6373*400000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211518089 400000000 538609982881 1250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958767541/10000000000 : ℝ)^8421 ≤ (724999272899/6250000000000 : ℝ)^6373 := by
    have hnat : (1958767541 : ℕ)^8421*6250000000000^6373 ≤ 724999272899^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958767541 10000000000 724999272899 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493093453/10000000000 : ℝ)^8421 ≤ (22655606497959/50000000000000 : ℝ)^6373 := by
    have hnat : (5493093453 : ℕ)^8421*50000000000000^6373 ≤ 22655606497959^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493093453 10000000000 22655606497959 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211518089/400000000 : ℝ), (-1958767541/10000000000 : ℝ), (5493093453/10000000000 : ℝ)] ![(538609982881/1250000000000 : ℝ), (724999272899/6250000000000 : ℝ), (22655606497959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211518089/400000000 : ℝ)|^8421 ≤ (538609982881/1250000000000 : ℝ)^6373
        have hw : |(211518089/400000000 : ℝ)|=(211518089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1958767541/10000000000 : ℝ)|^8421 ≤ (724999272899/6250000000000 : ℝ)^6373
        have hw : |(-1958767541/10000000000 : ℝ)|=(1958767541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493093453/10000000000 : ℝ)|^8421 ≤ (22655606497959/50000000000000 : ℝ)^6373
        have hw : |(5493093453/10000000000 : ℝ)|=(5493093453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321988101/2500000000 : ℝ)*x 0 + (549309351/1000000000 : ℝ)*x 1 + (-979383607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321988101/2500000000 : ℝ)^8421 ≤ (21544400278891/50000000000000 : ℝ)^6373 := by
    have hnat : (1321988101 : ℕ)^8421*50000000000000^6373 ≤ 21544400278891^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321988101 2500000000 21544400278891 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549309351/1000000000 : ℝ)^8421 ≤ (5663901702149/12500000000000 : ℝ)^6373 := by
    have hnat : (549309351 : ℕ)^8421*12500000000000^6373 ≤ 5663901702149^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549309351 1000000000 5663901702149 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979383607/5000000000 : ℝ)^8421 ≤ (231999716151/2000000000000 : ℝ)^6373 := by
    have hnat : (979383607 : ℕ)^8421*2000000000000^6373 ≤ 231999716151^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979383607 5000000000 231999716151 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321988101/2500000000 : ℝ), (549309351/1000000000 : ℝ), (-979383607/5000000000 : ℝ)] ![(21544400278891/50000000000000 : ℝ), (5663901702149/12500000000000 : ℝ), (231999716151/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321988101/2500000000 : ℝ)|^8421 ≤ (21544400278891/50000000000000 : ℝ)^6373
        have hw : |(1321988101/2500000000 : ℝ)|=(1321988101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549309351/1000000000 : ℝ)|^8421 ≤ (5663901702149/12500000000000 : ℝ)^6373
        have hw : |(549309351/1000000000 : ℝ)|=(549309351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979383607/5000000000 : ℝ)|^8421 ≤ (231999716151/2000000000000 : ℝ)^6373
        have hw : |(-979383607/5000000000 : ℝ)|=(979383607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s2_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2171936463/5000000000 : ℝ)*x 0 + (935538617/2000000000 : ℝ)*x 1 + (4033582891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171936463/5000000000 : ℝ)^8421 ≤ (1038381333913/3125000000000 : ℝ)^6373 := by
    have hnat : (2171936463 : ℕ)^8421*3125000000000^6373 ≤ 1038381333913^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171936463 5000000000 1038381333913 3125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935538617/2000000000 : ℝ)^8421 ≤ (366432959609/1000000000000 : ℝ)^6373 := by
    have hnat : (935538617 : ℕ)^8421*1000000000000^6373 ≤ 366432959609^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935538617 2000000000 366432959609 1000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033582891/10000000000 : ℝ)^8421 ≤ (30128501339407/100000000000000 : ℝ)^6373 := by
    have hnat : (4033582891 : ℕ)^8421*100000000000000^6373 ≤ 30128501339407^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033582891 10000000000 30128501339407 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171936463/5000000000 : ℝ), (935538617/2000000000 : ℝ), (4033582891/10000000000 : ℝ)] ![(1038381333913/3125000000000 : ℝ), (366432959609/1000000000000 : ℝ), (30128501339407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171936463/5000000000 : ℝ)|^8421 ≤ (1038381333913/3125000000000 : ℝ)^6373
        have hw : |(2171936463/5000000000 : ℝ)|=(2171936463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935538617/2000000000 : ℝ)|^8421 ≤ (366432959609/1000000000000 : ℝ)^6373
        have hw : |(935538617/2000000000 : ℝ)|=(935538617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033582891/10000000000 : ℝ)|^8421 ≤ (30128501339407/100000000000000 : ℝ)^6373
        have hw : |(4033582891/10000000000 : ℝ)|=(4033582891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4721/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (813/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6117/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (2051594480201/200000000000000000 : ℝ) := by
    have hpowers : (6117/100000 : ℝ)^2105 ≤ (2051594480201/200000000000000000 : ℝ)^512 := by
      have hnat : (6117 : ℕ)^2105*200000000000000000^512 ≤ 2051594480201^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6117 100000 2051594480201 200000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6117/100000 : ℝ)) (X := (2051594480201/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20059/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (16922889809458713/12500000000000000000 : ℝ) := by
    have hpowers : (20059/100000 : ℝ)^2105 ≤ (16922889809458713/12500000000000000000 : ℝ)^512 := by
      have hnat : (20059 : ℕ)^2105*12500000000000000000^512 ≤ 16922889809458713^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20059 100000 16922889809458713 12500000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20059/100000 : ℝ)) (X := (16922889809458713/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (100002051594480201/100000000000000000 : ℝ) ≤ (10000049900628013/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (100002051594480201/100000000000000000 : ℝ)^512 ≤ (10000049900628013/10000000000000000 : ℝ)^2105 := by
      have hnat : (100002051594480201 : ℕ)^512*10000000000000000^2105 ≤ 10000049900628013^2105*100000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002051594480201 100000000000000000 10000049900628013 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049900628013/10000000000000000 : ℝ)) (X := (100002051594480201/100000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25034102228928942551/25000000000000000000 : ℝ) ≤ (10003316168406299/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25034102228928942551/25000000000000000000 : ℝ)^512 ≤ (10003316168406299/10000000000000000 : ℝ)^2105 := by
      have hnat : (25034102228928942551 : ℕ)^512*10000000000000000^2105 ≤ 10003316168406299^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034102228928942551 25000000000000000000 10003316168406299 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003316168406299/10000000000000000 : ℝ)) (X := (25034102228928942551/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266922889809458713/6250000000000000000 : ℝ) ≤ (2001316487236917/2000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (6266922889809458713/6250000000000000000 : ℝ)^512 ≤ (2001316487236917/2000000000000000 : ℝ)^2105 := by
      have hnat : (6266922889809458713 : ℕ)^512*2000000000000000^2105 ≤ 2001316487236917^2105*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266922889809458713 6250000000000000000 2001316487236917 2000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001316487236917/2000000000000000 : ℝ)) (X := (6266922889809458713/6250000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2051594480201/200000000000000000 : ℝ) ≤ ((69690368097278103161/69710000000000000000 : ℝ)+2*(1633133889143/697100000000000 : ℝ)*(6117/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (69690368097278103161/69710000000000000000 : ℝ)+2*(1633133889143/697100000000000 : ℝ)*(6117/100000 : ℝ)=(10000049900628013/10000000000000000 : ℝ) by norm_num, show 1+2*(2051594480201/200000000000000000 : ℝ)=(100002051594480201/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16922889809458713/12500000000000000000 : ℝ)+(2051594480201/200000000000000000 : ℝ) ≤ ((69690368097278103161/69710000000000000000 : ℝ)+(1633133889143/697100000000000 : ℝ)*((20059/100000 : ℝ)+(6117/100000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (69690368097278103161/69710000000000000000 : ℝ)+(1633133889143/697100000000000 : ℝ)*((20059/100000 : ℝ)+(6117/100000 : ℝ))=(10003316168406299/10000000000000000 : ℝ) by norm_num, show 1+(16922889809458713/12500000000000000000 : ℝ)+(2051594480201/200000000000000000 : ℝ)=(25034102228928942551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16922889809458713/12500000000000000000 : ℝ) ≤ ((69690368097278103161/69710000000000000000 : ℝ)+2*(1633133889143/697100000000000 : ℝ)*(20059/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (69690368097278103161/69710000000000000000 : ℝ)+2*(1633133889143/697100000000000 : ℝ)*(20059/100000 : ℝ)=(2001316487236917/2000000000000000 : ℝ) by norm_num, show 1+2*(16922889809458713/12500000000000000000 : ℝ)=(6266922889809458713/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69690368097278103161/69710000000000000000 : ℝ)*(X 1 0+X 2 0)+(1633133889143/697100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (6117/100000 : ℝ)) (hi := (20059/100000 : ℝ)) (c := (69690368097278103161/69710000000000000000 : ℝ)) (alpha := (1633133889143/697100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69690368097278103161/69710000000000000000 : ℝ)*(X 0 1+X 2 1)+(1633133889143/697100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (6117/100000 : ℝ)) (hi := (20059/100000 : ℝ)) (c := (69690368097278103161/69710000000000000000 : ℝ)) (alpha := (1633133889143/697100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69690368097278103161/69710000000000000000 : ℝ)*(X 0 2+X 1 2)+(1633133889143/697100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (6117/100000 : ℝ)) (hi := (20059/100000 : ℝ)) (c := (69690368097278103161/69710000000000000000 : ℝ)) (alpha := (1633133889143/697100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2112060731/10000000000 : ℝ)*X 0 0+(2747603691/5000000000 : ℝ)*X 0 1+(323288747/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685130227/5000000000 : ℝ)*X 1 0+(-56981031/250000000 : ℝ)*X 1 1+(5172619893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074052053/2000000000 : ℝ)*X 2 0+(5172620059/10000000000 : ℝ)*X 2 1+(-2279241273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171854391/5000000000 : ℝ)*X 0 0+(402930653/1000000000 : ℝ)*X 0 1+(4681929597/10000000000 : ℝ)*X 0 2+(2171854391/5000000000 : ℝ)*X 1 0+(402930653/1000000000 : ℝ)*X 1 1+(4681929597/10000000000 : ℝ)*X 1 2+(2171854391/5000000000 : ℝ)*X 2 0+(402930653/1000000000 : ℝ)*X 2 1+(4681929597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422428427/2000000000 : ℝ)*X 0 0+(1293678527/2500000000 : ℝ)*X 0 1+(2746546707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211518089/400000000 : ℝ)*X 1 0+(-1958767541/10000000000 : ℝ)*X 1 1+(5493093453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321988101/2500000000 : ℝ)*X 2 0+(549309351/1000000000 : ℝ)*X 2 1+(-979383607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171936463/5000000000 : ℝ)*X 0 0+(935538617/2000000000 : ℝ)*X 0 1+(4033582891/10000000000 : ℝ)*X 0 2+(2171936463/5000000000 : ℝ)*X 1 0+(935538617/2000000000 : ℝ)*X 1 1+(4033582891/10000000000 : ℝ)*X 1 2+(2171936463/5000000000 : ℝ)*X 2 0+(935538617/2000000000 : ℝ)*X 2 1+(4033582891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1350964193336381915538552273/348550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375559107/50000000000000 : ℝ)*(base19) + (145581697/25000000000000 : ℝ)*(base23) + (32056357/100000000000000 : ℝ)*(lower2) + (17525243/12500000000000 : ℝ)*(upper3) + (5522099/12500000000000 : ℝ)*(upper5) + (231611777526623/10000000000000 : ℝ)*(major0) + (231611777526623/10000000000000 : ℝ)*(major1) + (231611777526623/10000000000000 : ℝ)*(major2) + (61998862615457/2000000000000 : ℝ)*(sp0) + (1549974374204339/50000000000000 : ℝ)*(sp1) + (387493614650013/12500000000000 : ℝ)*(sp2) + (383070398685829/25000000000000 : ℝ)*(sp3) + (6368754043/100000000000000 : ℝ)*(sp4) + (540882967/12500000000000 : ℝ)*(sp7) + (1532285921807053/100000000000000 : ℝ)*(f.failure) + (774987374881723/25000000000000 : ℝ)*(f.sum) + (736650055021/278840000000000000000000000 : ℝ)*base66 + (3250433395740455303/697100000000000000000000000000000 : ℝ)*base67 + (6708046575273855303/697100000000000000000000000000000 : ℝ)*base69 + (5366204341160855303/697100000000000000000000000000000 : ℝ)*base71 + (1218117289729/3485500000000000000000000000 : ℝ)*base73 + (5427086669684655303/697100000000000000000000000000000 : ℝ)*base75 + (2109877536030055303/697100000000000000000000000000000 : ℝ)*base77 + (6953450350837255303/697100000000000000000000000000000 : ℝ)*base79 + (7648398722611/3485500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18416959/2500000000000000000000 : ℝ)*base89 + (18416959/2500000000000000000000 : ℝ)*base91 + (18416959/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (616258852518209085020387823/217843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (932474709/100000000000000 : ℝ)*(base19) + (248948691/20000000000000 : ℝ)*(base23) + (29823461/50000000000000 : ℝ)*(upper2) + (145955821/100000000000000 : ℝ)*(upper3) + (1365067/2500000000000 : ℝ)*(upper5) + (146669883989731/6250000000000 : ℝ)*(major0) + (146669883989731/6250000000000 : ℝ)*(major1) + (146669883989731/6250000000000 : ℝ)*(major2) + (4470748673/50000000000000 : ℝ)*(sp1) + (14926033327/100000000000000 : ℝ)*(sp2) + (1570452914353201/50000000000000 : ℝ)*(sp4) + (785223988683587/25000000000000 : ℝ)*(sp5) + (3140889657929621/100000000000000 : ℝ)*(sp6) + (310506072933643/20000000000000 : ℝ)*(sp7) + (310506072933643/20000000000000 : ℝ)*(f.failure) + (1570452914353201/50000000000000 : ℝ)*(f.sum) + (22885495655643/8713750000000000000000000000 : ℝ)*base66 + (2404977339225877191/435687500000000000000000000000000 : ℝ)*base67 + (2052535211210752191/435687500000000000000000000000000 : ℝ)*base69 + (3002389797104935309/435687500000000000000000000000000 : ℝ)*base72 + (214204434068743/34855000000000000000000000000 : ℝ)*base73 + (1220998983375122809/435687500000000000000000000000000 : ℝ)*base76 + (1051961139698997809/435687500000000000000000000000000 : ℝ)*base78 + (1897544158147685309/435687500000000000000000000000000 : ℝ)*base80 + (9077711451033/2178437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (670729/500000000000000000000 : ℝ)*base89 + (670729/500000000000000000000 : ℝ)*base91 + (670729/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (813/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1228_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (813/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1228_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1228_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1228_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (813/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

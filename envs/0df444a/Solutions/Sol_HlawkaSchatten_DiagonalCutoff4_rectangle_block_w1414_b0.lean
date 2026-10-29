-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:29.613745+00:00
-- url     : https://prove2.me/submissions/6f2aeb08-b33c-4c15-b93c-933aac5cefcc

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
theorem support_rectangle_w1414_s0_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-353467513/2000000000 : ℝ)*x 0 + (5966395641/10000000000 : ℝ)*x 1 + (2413897301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353467513/2000000000 : ℝ)^2187 ≤ (10405104038097/100000000000000 : ℝ)^1675 := by
    have hnat : (353467513 : ℕ)^2187*100000000000000^1675 ≤ 10405104038097^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353467513 2000000000 10405104038097 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5966395641/10000000000 : ℝ)^2187 ≤ (10190220418963/20000000000000 : ℝ)^1675 := by
    have hnat : (5966395641 : ℕ)^2187*20000000000000^1675 ≤ 10190220418963^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966395641 10000000000 10190220418963 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2413897301/5000000000 : ℝ)^2187 ≤ (38643793849357/100000000000000 : ℝ)^1675 := by
    have hnat : (2413897301 : ℕ)^2187*100000000000000^1675 ≤ 38643793849357^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413897301 5000000000 38643793849357 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353467513/2000000000 : ℝ), (5966395641/10000000000 : ℝ), (2413897301/5000000000 : ℝ)] ![(10405104038097/100000000000000 : ℝ), (10190220418963/20000000000000 : ℝ), (38643793849357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353467513/2000000000 : ℝ)|^2187 ≤ (10405104038097/100000000000000 : ℝ)^1675
        have hw : |(-353467513/2000000000 : ℝ)|=(353467513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5966395641/10000000000 : ℝ)|^2187 ≤ (10190220418963/20000000000000 : ℝ)^1675
        have hw : |(5966395641/10000000000 : ℝ)|=(5966395641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2413897301/5000000000 : ℝ)|^2187 ≤ (38643793849357/100000000000000 : ℝ)^1675
        have hw : |(2413897301/5000000000 : ℝ)|=(2413897301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2746884437/5000000000 : ℝ)*x 0 + (-150700069/625000000 : ℝ)*x 1 + (4827794937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746884437/5000000000 : ℝ)^2187 ≤ (5718289660361/12500000000000 : ℝ)^1675 := by
    have hnat : (2746884437 : ℕ)^2187*12500000000000^1675 ≤ 5718289660361^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746884437 5000000000 5718289660361 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150700069/625000000 : ℝ)^2187 ≤ (15609885349289/100000000000000 : ℝ)^1675 := by
    have hnat : (150700069 : ℕ)^2187*100000000000000^1675 ≤ 15609885349289^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150700069 625000000 15609885349289 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4827794937/10000000000 : ℝ)^2187 ≤ (38643797350499/100000000000000 : ℝ)^1675 := by
    have hnat : (4827794937 : ℕ)^2187*100000000000000^1675 ≤ 38643797350499^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827794937 10000000000 38643797350499 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746884437/5000000000 : ℝ), (-150700069/625000000 : ℝ), (4827794937/10000000000 : ℝ)] ![(5718289660361/12500000000000 : ℝ), (15609885349289/100000000000000 : ℝ), (38643797350499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746884437/5000000000 : ℝ)|^2187 ≤ (5718289660361/12500000000000 : ℝ)^1675
        have hw : |(2746884437/5000000000 : ℝ)|=(2746884437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150700069/625000000 : ℝ)|^2187 ≤ (15609885349289/100000000000000 : ℝ)^1675
        have hw : |(-150700069/625000000 : ℝ)|=(150700069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4827794937/10000000000 : ℝ)|^2187 ≤ (38643797350499/100000000000000 : ℝ)^1675
        have hw : |(4827794937/10000000000 : ℝ)|=(4827794937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5493769141/10000000000 : ℝ)*x 0 + (1206948699/2500000000 : ℝ)*x 1 + (-482240187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5493769141/10000000000 : ℝ)^2187 ≤ (2287316009289/5000000000000 : ℝ)^1675 := by
    have hnat : (5493769141 : ℕ)^2187*5000000000000^1675 ≤ 2287316009289^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493769141 10000000000 2287316009289 5000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206948699/2500000000 : ℝ)^2187 ≤ (9660948969221/25000000000000 : ℝ)^1675 := by
    have hnat : (1206948699 : ℕ)^2187*25000000000000^1675 ≤ 9660948969221^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206948699 2500000000 9660948969221 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482240187/2000000000 : ℝ)^2187 ≤ (15609883920767/100000000000000 : ℝ)^1675 := by
    have hnat : (482240187 : ℕ)^2187*100000000000000^1675 ≤ 15609883920767^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482240187 2000000000 15609883920767 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5493769141/10000000000 : ℝ), (1206948699/2500000000 : ℝ), (-482240187/2000000000 : ℝ)] ![(2287316009289/5000000000000 : ℝ), (9660948969221/25000000000000 : ℝ), (15609883920767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5493769141/10000000000 : ℝ)|^2187 ≤ (2287316009289/5000000000000 : ℝ)^1675
        have hw : |(5493769141/10000000000 : ℝ)|=(5493769141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206948699/2500000000 : ℝ)|^2187 ≤ (9660948969221/25000000000000 : ℝ)^1675
        have hw : |(1206948699/2500000000 : ℝ)|=(1206948699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482240187/2000000000 : ℝ)|^2187 ≤ (15609883920767/100000000000000 : ℝ)^1675
        have hw : |(-482240187/2000000000 : ℝ)|=(482240187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4168159973/10000000000 : ℝ)*x 0 + (3103757443/10000000000 : ℝ)*x 1 + (5553402013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4168159973/10000000000 : ℝ)^2187 ≤ (1594931947557/5000000000000 : ℝ)^1675 := by
    have hnat : (4168159973 : ℕ)^2187*5000000000000^1675 ≤ 1594931947557^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168159973 10000000000 1594931947557 5000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103757443/10000000000 : ℝ)^2187 ≤ (10852812002883/50000000000000 : ℝ)^1675 := by
    have hnat : (3103757443 : ℕ)^2187*50000000000000^1675 ≤ 10852812002883^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103757443 10000000000 10852812002883 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5553402013/10000000000 : ℝ)^2187 ≤ (2899733564149/6250000000000 : ℝ)^1675 := by
    have hnat : (5553402013 : ℕ)^2187*6250000000000^1675 ≤ 2899733564149^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553402013 10000000000 2899733564149 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4168159973/10000000000 : ℝ), (3103757443/10000000000 : ℝ), (5553402013/10000000000 : ℝ)] ![(1594931947557/5000000000000 : ℝ), (10852812002883/50000000000000 : ℝ), (2899733564149/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4168159973/10000000000 : ℝ)|^2187 ≤ (1594931947557/5000000000000 : ℝ)^1675
        have hw : |(4168159973/10000000000 : ℝ)|=(4168159973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103757443/10000000000 : ℝ)|^2187 ≤ (10852812002883/50000000000000 : ℝ)^1675
        have hw : |(3103757443/10000000000 : ℝ)|=(3103757443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5553402013/10000000000 : ℝ)|^2187 ≤ (2899733564149/6250000000000 : ℝ)^1675
        have hw : |(5553402013/10000000000 : ℝ)|=(5553402013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-442856939/2500000000 : ℝ)*x 0 + (607119961/1250000000 : ℝ)*x 1 + (5936189053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442856939/2500000000 : ℝ)^2187 ≤ (2087311348371/20000000000000 : ℝ)^1675 := by
    have hnat : (442856939 : ℕ)^2187*20000000000000^1675 ≤ 2087311348371^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442856939 2500000000 2087311348371 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607119961/1250000000 : ℝ)^2187 ≤ (486861052239/1250000000000 : ℝ)^1675 := by
    have hnat : (607119961 : ℕ)^2187*1250000000000^1675 ≤ 486861052239^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607119961 1250000000 486861052239 1250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5936189053/10000000000 : ℝ)^2187 ≤ (25307279530201/50000000000000 : ℝ)^1675 := by
    have hnat : (5936189053 : ℕ)^2187*50000000000000^1675 ≤ 25307279530201^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5936189053 10000000000 25307279530201 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442856939/2500000000 : ℝ), (607119961/1250000000 : ℝ), (5936189053/10000000000 : ℝ)] ![(2087311348371/20000000000000 : ℝ), (486861052239/1250000000000 : ℝ), (25307279530201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442856939/2500000000 : ℝ)|^2187 ≤ (2087311348371/20000000000000 : ℝ)^1675
        have hw : |(-442856939/2500000000 : ℝ)|=(442856939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(607119961/1250000000 : ℝ)|^2187 ≤ (486861052239/1250000000000 : ℝ)^1675
        have hw : |(607119961/1250000000 : ℝ)|=(607119961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5936189053/10000000000 : ℝ)|^2187 ≤ (25307279530201/50000000000000 : ℝ)^1675
        have hw : |(5936189053/10000000000 : ℝ)|=(5936189053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2591534971/5000000000 : ℝ)*x 0 + (-26056129/200000000 : ℝ)*x 1 + (5936189151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591534971/5000000000 : ℝ)^2187 ≤ (42397908210913/100000000000000 : ℝ)^1675 := by
    have hnat : (2591534971 : ℕ)^2187*100000000000000^1675 ≤ 42397908210913^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591534971 5000000000 42397908210913 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26056129/200000000 : ℝ)^2187 ≤ (6987531615399/100000000000000 : ℝ)^1675 := by
    have hnat : (26056129 : ℕ)^2187*100000000000000^1675 ≤ 6987531615399^1675*200000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26056129 200000000 6987531615399 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5936189151/10000000000 : ℝ)^2187 ≤ (50614560151409/100000000000000 : ℝ)^1675 := by
    have hnat : (5936189151 : ℕ)^2187*100000000000000^1675 ≤ 50614560151409^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5936189151 10000000000 50614560151409 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591534971/5000000000 : ℝ), (-26056129/200000000 : ℝ), (5936189151/10000000000 : ℝ)] ![(42397908210913/100000000000000 : ℝ), (6987531615399/100000000000000 : ℝ), (50614560151409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591534971/5000000000 : ℝ)|^2187 ≤ (42397908210913/100000000000000 : ℝ)^1675
        have hw : |(2591534971/5000000000 : ℝ)|=(2591534971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26056129/200000000 : ℝ)|^2187 ≤ (6987531615399/100000000000000 : ℝ)^1675
        have hw : |(-26056129/200000000 : ℝ)|=(26056129/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5936189151/10000000000 : ℝ)|^2187 ≤ (50614560151409/100000000000000 : ℝ)^1675
        have hw : |(5936189151/10000000000 : ℝ)|=(5936189151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183069961/10000000000 : ℝ)*x 0 + (5936188957/10000000000 : ℝ)*x 1 + (-1302806731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183069961/10000000000 : ℝ)^2187 ≤ (21198954206921/50000000000000 : ℝ)^1675 := by
    have hnat : (5183069961 : ℕ)^2187*50000000000000^1675 ≤ 21198954206921^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183069961 10000000000 21198954206921 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5936188957/10000000000 : ℝ)^2187 ≤ (50614557991659/100000000000000 : ℝ)^1675 := by
    have hnat : (5936188957 : ℕ)^2187*100000000000000^1675 ≤ 50614557991659^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5936188957 10000000000 50614557991659 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302806731/10000000000 : ℝ)^2187 ≤ (3493766791607/50000000000000 : ℝ)^1675 := by
    have hnat : (1302806731 : ℕ)^2187*50000000000000^1675 ≤ 3493766791607^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302806731 10000000000 3493766791607 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183069961/10000000000 : ℝ), (5936188957/10000000000 : ℝ), (-1302806731/10000000000 : ℝ)] ![(21198954206921/50000000000000 : ℝ), (50614557991659/100000000000000 : ℝ), (3493766791607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183069961/10000000000 : ℝ)|^2187 ≤ (21198954206921/50000000000000 : ℝ)^1675
        have hw : |(5183069961/10000000000 : ℝ)|=(5183069961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5936188957/10000000000 : ℝ)|^2187 ≤ (50614557991659/100000000000000 : ℝ)^1675
        have hw : |(5936188957/10000000000 : ℝ)|=(5936188957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302806731/10000000000 : ℝ)|^2187 ≤ (3493766791607/50000000000000 : ℝ)^1675
        have hw : |(-1302806731/10000000000 : ℝ)|=(1302806731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s0_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1044240423/2500000000 : ℝ)*x 0 + (686331839/1250000000 : ℝ)*x 1 + (316874569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044240423/2500000000 : ℝ)^2187 ≤ (31986615985267/100000000000000 : ℝ)^1675 := by
    have hnat : (1044240423 : ℕ)^2187*100000000000000^1675 ≤ 31986615985267^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044240423 2500000000 31986615985267 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686331839/1250000000 : ℝ)^2187 ≤ (5714057780723/12500000000000 : ℝ)^1675 := by
    have hnat : (686331839 : ℕ)^2187*12500000000000^1675 ≤ 5714057780723^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686331839 1250000000 5714057780723 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316874569/1000000000 : ℝ)^2187 ≤ (5575230436959/25000000000000 : ℝ)^1675 := by
    have hnat : (316874569 : ℕ)^2187*25000000000000^1675 ≤ 5575230436959^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316874569 1000000000 5575230436959 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044240423/2500000000 : ℝ), (686331839/1250000000 : ℝ), (316874569/1000000000 : ℝ)] ![(31986615985267/100000000000000 : ℝ), (5714057780723/12500000000000 : ℝ), (5575230436959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044240423/2500000000 : ℝ)|^2187 ≤ (31986615985267/100000000000000 : ℝ)^1675
        have hw : |(1044240423/2500000000 : ℝ)|=(1044240423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686331839/1250000000 : ℝ)|^2187 ≤ (5714057780723/12500000000000 : ℝ)^1675
        have hw : |(686331839/1250000000 : ℝ)|=(686331839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316874569/1000000000 : ℝ)|^2187 ≤ (5575230436959/25000000000000 : ℝ)^1675
        have hw : |(316874569/1000000000 : ℝ)|=(316874569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1941/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13181/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4373/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4373 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4373*1^1024 ≤ 0^1024*1^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4373/1024 : ℝ) ≤ (249749195000056303/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4373 ≤ (249749195000056303/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4373*12500000000000000000^1024 ≤ 249749195000056303^1024*5^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 249749195000056303 12500000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (249749195000056303/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4373 := by
      have hnat : (1 : ℕ)^1024*1^4373 ≤ 1^4373*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12749749195000056303/12500000000000000000 : ℝ) ≤ (5023216031566081/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (12749749195000056303/12500000000000000000 : ℝ)^1024 ≤ (5023216031566081/5000000000000000 : ℝ)^4373 := by
      have hnat : (12749749195000056303 : ℕ)^1024*5000000000000000^4373 ≤ 5023216031566081^4373*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12749749195000056303 12500000000000000000 5023216031566081 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023216031566081/5000000000000000 : ℝ)) (X := (12749749195000056303/12500000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6499749195000056303/6250000000000000000 : ℝ) ≤ (2523216031566081/2500000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (6499749195000056303/6250000000000000000 : ℝ)^1024 ≤ (2523216031566081/2500000000000000 : ℝ)^4373 := by
      have hnat : (6499749195000056303 : ℕ)^1024*2500000000000000^4373 ≤ 2523216031566081^4373*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6499749195000056303 6250000000000000000 2523216031566081 2500000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523216031566081/2500000000000000 : ℝ)) (X := (6499749195000056303/6250000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23216031566081/2000000000000000 : ℝ)*(0 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23216031566081/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(249749195000056303/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23216031566081/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (1 : ℝ)+(23216031566081/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5023216031566081/5000000000000000 : ℝ) by norm_num, show 1+(249749195000056303/12500000000000000000 : ℝ)+(0 : ℝ)=(12749749195000056303/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(249749195000056303/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23216031566081/2000000000000000 : ℝ)*(2/5 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23216031566081/2000000000000000 : ℝ)*(2/5 : ℝ)=(2523216031566081/2500000000000000 : ℝ) by norm_num, show 1+2*(249749195000056303/12500000000000000000 : ℝ)=(6499749195000056303/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23216031566081/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23216031566081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23216031566081/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23216031566081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23216031566081/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23216031566081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-353467513/2000000000 : ℝ)*X 0 0+(5966395641/10000000000 : ℝ)*X 0 1+(2413897301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2746884437/5000000000 : ℝ)*X 1 0+(-150700069/625000000 : ℝ)*X 1 1+(4827794937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5493769141/10000000000 : ℝ)*X 2 0+(1206948699/2500000000 : ℝ)*X 2 1+(-482240187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4168159973/10000000000 : ℝ)*X 0 0+(3103757443/10000000000 : ℝ)*X 0 1+(5553402013/10000000000 : ℝ)*X 0 2+(4168159973/10000000000 : ℝ)*X 1 0+(3103757443/10000000000 : ℝ)*X 1 1+(5553402013/10000000000 : ℝ)*X 1 2+(4168159973/10000000000 : ℝ)*X 2 0+(3103757443/10000000000 : ℝ)*X 2 1+(5553402013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442856939/2500000000 : ℝ)*X 0 0+(607119961/1250000000 : ℝ)*X 0 1+(5936189053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591534971/5000000000 : ℝ)*X 1 0+(-26056129/200000000 : ℝ)*X 1 1+(5936189151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183069961/10000000000 : ℝ)*X 2 0+(5936188957/10000000000 : ℝ)*X 2 1+(-1302806731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044240423/2500000000 : ℝ)*X 0 0+(686331839/1250000000 : ℝ)*X 0 1+(316874569/1000000000 : ℝ)*X 0 2+(1044240423/2500000000 : ℝ)*X 1 0+(686331839/1250000000 : ℝ)*X 1 1+(316874569/1000000000 : ℝ)*X 1 2+(1044240423/2500000000 : ℝ)*X 2 0+(686331839/1250000000 : ℝ)*X 2 1+(316874569/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153036087075727469259153/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1444313813/100000000000000 : ℝ)*(base19) + (1477097541/100000000000000 : ℝ)*(base23) + (164930503/100000000000000 : ℝ)*(upper3) + (1359861/25000000000000 : ℝ)*(upper4) + (8563633/4000000000000 : ℝ)*(upper5) + (643254381872629/100000000000000 : ℝ)*(major0) + (643254381872629/100000000000000 : ℝ)*(major1) + (643254381872629/100000000000000 : ℝ)*(major2) + (878275598008643/100000000000000 : ℝ)*(sp0) + (878279670870013/100000000000000 : ℝ)*(sp1) + (175655927617257/20000000000000 : ℝ)*(sp2) + (204112477520429/50000000000000 : ℝ)*(sp3) + (5517175183/100000000000000 : ℝ)*(sp4) + (38898007/1562500000000 : ℝ)*(sp7) + (204113722256653/50000000000000 : ℝ)*(f.failure) + (439140557591913/50000000000000 : ℝ)*(f.sum) + (86488182003051/100000000000000000000000000000 : ℝ)*base66 + (930154511296949/200000000000000000000000000000 : ℝ)*base67 + (2332497726896949/200000000000000000000000000000 : ℝ)*base69 + (996657496296949/200000000000000000000000000000 : ℝ)*base71 + (36071666896949/100000000000000000000000000000 : ℝ)*base73 + (1989716247696949/200000000000000000000000000000 : ℝ)*base75 + (1214866331696949/200000000000000000000000000000 : ℝ)*base77 + (1173869552696949/200000000000000000000000000000 : ℝ)*base79 + (548108358796949/100000000000000000000000000000 : ℝ)*base81 + (49094809/5000000000000000000000 : ℝ)*base90 + (49094809/5000000000000000000000 : ℝ)*base92 + (49094809/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63815255160618637075227/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180650829/12500000000000 : ℝ)*(base19) + (145691893/10000000000000 : ℝ)*(base23) + (89375877/50000000000000 : ℝ)*(base32) + (28176193/12500000000000 : ℝ)*(upper3) + (111279511/100000000000000 : ℝ)*(upper5) + (67863316878711/10000000000000 : ℝ)*(major0) + (67863316878711/10000000000000 : ℝ)*(major1) + (67863316878711/10000000000000 : ℝ)*(major2) + (836741197/25000000000000 : ℝ)*(sp1) + (54463801/1562500000000 : ℝ)*(sp2) + (115823287551939/12500000000000 : ℝ)*(sp4) + (231645377061023/25000000000000 : ℝ)*(sp5) + (463290678906659/50000000000000 : ℝ)*(sp6) + (86135929137887/20000000000000 : ℝ)*(sp7) + (430679824441189/100000000000000 : ℝ)*(f.failure) + (115823287551939/12500000000000 : ℝ)*(f.sum) + (5754329121591/10000000000000000000000000000 : ℝ)*base65 + (92006900918409/20000000000000000000000000000 : ℝ)*base68 + (73686552881591/20000000000000000000000000000 : ℝ)*base69 + (9038249318409/20000000000000000000000000000 : ℝ)*base72 + (24548425078409/10000000000000000000000000000 : ℝ)*base74 + (31123870641591/20000000000000000000000000000 : ℝ)*base75 + (8917641761591/20000000000000000000000000000 : ℝ)*base77 + (31781765198409/20000000000000000000000000000 : ℝ)*base80 + (23775160081591/10000000000000000000000000000 : ℝ)*base81 + (2438383/10000000000000000000000 : ℝ)*base89 + (2438383/10000000000000000000000 : ℝ)*base91 + (2438383/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1414_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1941/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13181/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1414_s1_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-970912509/5000000000 : ℝ)*x 0 + (1402823569/2500000000 : ℝ)*x 1 + (5071060419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (970912509/5000000000 : ℝ)^2187 ≤ (5883098322971/50000000000000 : ℝ)^1675 := by
    have hnat : (970912509 : ℕ)^2187*50000000000000^1675 ≤ 5883098322971^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970912509 5000000000 5883098322971 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402823569/2500000000 : ℝ)^2187 ≤ (5878530113783/12500000000000 : ℝ)^1675 := by
    have hnat : (1402823569 : ℕ)^2187*12500000000000^1675 ≤ 5878530113783^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402823569 2500000000 5878530113783 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071060419/10000000000 : ℝ)^2187 ≤ (10301390608431/25000000000000 : ℝ)^1675 := by
    have hnat : (5071060419 : ℕ)^2187*25000000000000^1675 ≤ 10301390608431^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071060419 10000000000 10301390608431 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-970912509/5000000000 : ℝ), (1402823569/2500000000 : ℝ), (5071060419/10000000000 : ℝ)] ![(5883098322971/50000000000000 : ℝ), (5878530113783/12500000000000 : ℝ), (10301390608431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-970912509/5000000000 : ℝ)|^2187 ≤ (5883098322971/50000000000000 : ℝ)^1675
        have hw : |(-970912509/5000000000 : ℝ)|=(970912509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402823569/2500000000 : ℝ)|^2187 ≤ (5878530113783/12500000000000 : ℝ)^1675
        have hw : |(1402823569/2500000000 : ℝ)|=(1402823569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071060419/10000000000 : ℝ)|^2187 ≤ (10301390608431/25000000000000 : ℝ)^1675
        have hw : |(5071060419/10000000000 : ℝ)|=(5071060419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1349580301/2500000000 : ℝ)*x 0 + (-1114210973/5000000000 : ℝ)*x 1 + (5071057599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349580301/2500000000 : ℝ)^2187 ≤ (44711352340681/100000000000000 : ℝ)^1675 := by
    have hnat : (1349580301 : ℕ)^2187*100000000000000^1675 ≤ 44711352340681^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349580301 2500000000 44711352340681 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114210973/5000000000 : ℝ)^2187 ≤ (3520778783913/25000000000000 : ℝ)^1675 := by
    have hnat : (1114210973 : ℕ)^2187*25000000000000^1675 ≤ 3520778783913^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114210973 5000000000 3520778783913 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071057599/10000000000 : ℝ)^2187 ≤ (10301383128801/25000000000000 : ℝ)^1675 := by
    have hnat : (5071057599 : ℕ)^2187*25000000000000^1675 ≤ 10301383128801^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071057599 10000000000 10301383128801 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349580301/2500000000 : ℝ), (-1114210973/5000000000 : ℝ), (5071057599/10000000000 : ℝ)] ![(44711352340681/100000000000000 : ℝ), (3520778783913/25000000000000 : ℝ), (10301383128801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349580301/2500000000 : ℝ)|^2187 ≤ (44711352340681/100000000000000 : ℝ)^1675
        have hw : |(1349580301/2500000000 : ℝ)|=(1349580301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114210973/5000000000 : ℝ)|^2187 ≤ (3520778783913/25000000000000 : ℝ)^1675
        have hw : |(-1114210973/5000000000 : ℝ)|=(1114210973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071057599/10000000000 : ℝ)|^2187 ≤ (10301383128801/25000000000000 : ℝ)^1675
        have hw : |(5071057599/10000000000 : ℝ)|=(5071057599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1349579867/2500000000 : ℝ)*x 0 + (1267765091/2500000000 : ℝ)*x 1 + (-1114210333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349579867/2500000000 : ℝ)^2187 ≤ (44711333567289/100000000000000 : ℝ)^1675 := by
    have hnat : (1349579867 : ℕ)^2187*100000000000000^1675 ≤ 44711333567289^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349579867 2500000000 44711333567289 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267765091/2500000000 : ℝ)^2187 ≤ (41205561850207/100000000000000 : ℝ)^1675 := by
    have hnat : (1267765091 : ℕ)^2187*100000000000000^1675 ≤ 41205561850207^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267765091 2500000000 41205561850207 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114210333/5000000000 : ℝ)^2187 ≤ (563324182947/4000000000000 : ℝ)^1675 := by
    have hnat : (1114210333 : ℕ)^2187*4000000000000^1675 ≤ 563324182947^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114210333 5000000000 563324182947 4000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349579867/2500000000 : ℝ), (1267765091/2500000000 : ℝ), (-1114210333/5000000000 : ℝ)] ![(44711333567289/100000000000000 : ℝ), (41205561850207/100000000000000 : ℝ), (563324182947/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349579867/2500000000 : ℝ)|^2187 ≤ (44711333567289/100000000000000 : ℝ)^1675
        have hw : |(1349579867/2500000000 : ℝ)|=(1349579867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267765091/2500000000 : ℝ)|^2187 ≤ (41205561850207/100000000000000 : ℝ)^1675
        have hw : |(1267765091/2500000000 : ℝ)|=(1267765091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114210333/5000000000 : ℝ)|^2187 ≤ (563324182947/4000000000000 : ℝ)^1675
        have hw : |(-1114210333/5000000000 : ℝ)|=(1114210333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133730103/312500000 : ℝ)*x 0 + (186683173/500000000 : ℝ)*x 1 + (4895958373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133730103/312500000 : ℝ)^2187 ≤ (8253577392391/25000000000000 : ℝ)^1675 := by
    have hnat : (133730103 : ℕ)^2187*25000000000000^1675 ≤ 8253577392391^1675*312500000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133730103 312500000 8253577392391 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186683173/500000000 : ℝ)^2187 ≤ (27627973089599/100000000000000 : ℝ)^1675 := by
    have hnat : (186683173 : ℕ)^2187*100000000000000^1675 ≤ 27627973089599^1675*500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186683173 500000000 27627973089599 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895958373/10000000000 : ℝ)^2187 ≤ (19678858665067/50000000000000 : ℝ)^1675 := by
    have hnat : (4895958373 : ℕ)^2187*50000000000000^1675 ≤ 19678858665067^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895958373 10000000000 19678858665067 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133730103/312500000 : ℝ), (186683173/500000000 : ℝ), (4895958373/10000000000 : ℝ)] ![(8253577392391/25000000000000 : ℝ), (27627973089599/100000000000000 : ℝ), (19678858665067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133730103/312500000 : ℝ)|^2187 ≤ (8253577392391/25000000000000 : ℝ)^1675
        have hw : |(133730103/312500000 : ℝ)|=(133730103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186683173/500000000 : ℝ)|^2187 ≤ (27627973089599/100000000000000 : ℝ)^1675
        have hw : |(186683173/500000000 : ℝ)|=(186683173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895958373/10000000000 : ℝ)|^2187 ≤ (19678858665067/50000000000000 : ℝ)^1675
        have hw : |(4895958373/10000000000 : ℝ)|=(4895958373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-194224341/1000000000 : ℝ)*x 0 + (1269367047/2500000000 : ℝ)*x 1 + (5604776891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194224341/1000000000 : ℝ)^2187 ≤ (1176950687201/10000000000000 : ℝ)^1675 := by
    have hnat : (194224341 : ℕ)^2187*10000000000000^1675 ≤ 1176950687201^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194224341 1000000000 1176950687201 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269367047/2500000000 : ℝ)^2187 ≤ (20636779088041/50000000000000 : ℝ)^1675 := by
    have hnat : (1269367047 : ℕ)^2187*50000000000000^1675 ≤ 20636779088041^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269367047 2500000000 20636779088041 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5604776891/10000000000 : ℝ)^2187 ≤ (23478467468171/50000000000000 : ℝ)^1675 := by
    have hnat : (5604776891 : ℕ)^2187*50000000000000^1675 ≤ 23478467468171^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604776891 10000000000 23478467468171 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194224341/1000000000 : ℝ), (1269367047/2500000000 : ℝ), (5604776891/10000000000 : ℝ)] ![(1176950687201/10000000000000 : ℝ), (20636779088041/50000000000000 : ℝ), (23478467468171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194224341/1000000000 : ℝ)|^2187 ≤ (1176950687201/10000000000000 : ℝ)^1675
        have hw : |(-194224341/1000000000 : ℝ)|=(194224341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269367047/2500000000 : ℝ)|^2187 ≤ (20636779088041/50000000000000 : ℝ)^1675
        have hw : |(1269367047/2500000000 : ℝ)|=(1269367047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5604776891/10000000000 : ℝ)|^2187 ≤ (23478467468171/50000000000000 : ℝ)^1675
        have hw : |(5604776891/10000000000 : ℝ)|=(5604776891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5257329591/10000000000 : ℝ)*x 0 + (-847351529/5000000000 : ℝ)*x 1 + (560477667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257329591/10000000000 : ℝ)^2187 ≤ (21596384474769/50000000000000 : ℝ)^1675 := by
    have hnat : (5257329591 : ℕ)^2187*50000000000000^1675 ≤ 21596384474769^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257329591 10000000000 21596384474769 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847351529/5000000000 : ℝ)^2187 ≤ (2462574629349/25000000000000 : ℝ)^1675 := by
    have hnat : (847351529 : ℕ)^2187*25000000000000^1675 ≤ 2462574629349^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847351529 5000000000 2462574629349 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560477667/1000000000 : ℝ)^2187 ≤ (9391386503767/20000000000000 : ℝ)^1675 := by
    have hnat : (560477667 : ℕ)^2187*20000000000000^1675 ≤ 9391386503767^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560477667 1000000000 9391386503767 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257329591/10000000000 : ℝ), (-847351529/5000000000 : ℝ), (560477667/1000000000 : ℝ)] ![(21596384474769/50000000000000 : ℝ), (2462574629349/25000000000000 : ℝ), (9391386503767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257329591/10000000000 : ℝ)|^2187 ≤ (21596384474769/50000000000000 : ℝ)^1675
        have hw : |(5257329591/10000000000 : ℝ)|=(5257329591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-847351529/5000000000 : ℝ)|^2187 ≤ (2462574629349/25000000000000 : ℝ)^1675
        have hw : |(-847351529/5000000000 : ℝ)|=(847351529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560477667/1000000000 : ℝ)|^2187 ≤ (9391386503767/20000000000000 : ℝ)^1675
        have hw : |(560477667/1000000000 : ℝ)|=(560477667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5257330277/10000000000 : ℝ)*x 0 + (2802388601/5000000000 : ℝ)*x 1 + (-1694701321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257330277/10000000000 : ℝ)^2187 ≤ (21596388154143/50000000000000 : ℝ)^1675 := by
    have hnat : (5257330277 : ℕ)^2187*50000000000000^1675 ≤ 21596388154143^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257330277 10000000000 21596388154143 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802388601/5000000000 : ℝ)^2187 ≤ (46956938338353/100000000000000 : ℝ)^1675 := by
    have hnat : (2802388601 : ℕ)^2187*100000000000000^1675 ≤ 46956938338353^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802388601 5000000000 46956938338353 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694701321/10000000000 : ℝ)^2187 ≤ (2462571333787/25000000000000 : ℝ)^1675 := by
    have hnat : (1694701321 : ℕ)^2187*25000000000000^1675 ≤ 2462571333787^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694701321 10000000000 2462571333787 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257330277/10000000000 : ℝ), (2802388601/5000000000 : ℝ), (-1694701321/10000000000 : ℝ)] ![(21596388154143/50000000000000 : ℝ), (46956938338353/100000000000000 : ℝ), (2462571333787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257330277/10000000000 : ℝ)|^2187 ≤ (21596388154143/50000000000000 : ℝ)^1675
        have hw : |(5257330277/10000000000 : ℝ)|=(5257330277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802388601/5000000000 : ℝ)|^2187 ≤ (46956938338353/100000000000000 : ℝ)^1675
        have hw : |(2802388601/5000000000 : ℝ)|=(2802388601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1694701321/10000000000 : ℝ)|^2187 ≤ (2462571333787/25000000000000 : ℝ)^1675
        have hw : |(-1694701321/10000000000 : ℝ)|=(1694701321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s1_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (856052877/2000000000 : ℝ)*x 0 + (1220541921/2500000000 : ℝ)*x 1 + (46846141/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856052877/2000000000 : ℝ)^2187 ≤ (33023386493523/100000000000000 : ℝ)^1675 := by
    have hnat : (856052877 : ℕ)^2187*100000000000000^1675 ≤ 33023386493523^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856052877 2000000000 33023386493523 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220541921/2500000000 : ℝ)^2187 ≤ (39213031834721/100000000000000 : ℝ)^1675 := by
    have hnat : (1220541921 : ℕ)^2187*100000000000000^1675 ≤ 39213031834721^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220541921 2500000000 39213031834721 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46846141/125000000 : ℝ)^2187 ≤ (13881790824859/50000000000000 : ℝ)^1675 := by
    have hnat : (46846141 : ℕ)^2187*50000000000000^1675 ≤ 13881790824859^1675*125000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46846141 125000000 13881790824859 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856052877/2000000000 : ℝ), (1220541921/2500000000 : ℝ), (46846141/125000000 : ℝ)] ![(33023386493523/100000000000000 : ℝ), (39213031834721/100000000000000 : ℝ), (13881790824859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856052877/2000000000 : ℝ)|^2187 ≤ (33023386493523/100000000000000 : ℝ)^1675
        have hw : |(856052877/2000000000 : ℝ)|=(856052877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220541921/2500000000 : ℝ)|^2187 ≤ (39213031834721/100000000000000 : ℝ)^1675
        have hw : |(1220541921/2500000000 : ℝ)|=(1220541921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46846141/125000000 : ℝ)|^2187 ≤ (13881790824859/50000000000000 : ℝ)^1675
        have hw : |(46846141/125000000 : ℝ)|=(46846141/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1941/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (2443259963123/50000000000000000000 : ℝ) := by
    have hpowers : (1941/100000 : ℝ)^4373 ≤ (2443259963123/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1941 : ℕ)^4373*50000000000000000000^1024 ≤ 2443259963123^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1941 100000 2443259963123 50000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1941/100000 : ℝ)) (X := (2443259963123/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13181/50000 : ℝ) ^ (4373/1024 : ℝ) ≤ (168365672247621127/50000000000000000000 : ℝ) := by
    have hpowers : (13181/50000 : ℝ)^4373 ≤ (168365672247621127/50000000000000000000 : ℝ)^1024 := by
      have hnat : (13181 : ℕ)^4373*50000000000000000000^1024 ≤ 168365672247621127^1024*50000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13181 50000 168365672247621127 50000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13181/50000 : ℝ)) (X := (168365672247621127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002443259963123/25000000000000000000 : ℝ) ≤ (10000000228849587/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (25000002443259963123/25000000000000000000 : ℝ)^1024 ≤ (10000000228849587/10000000000000000 : ℝ)^4373 := by
      have hnat : (25000002443259963123 : ℕ)^1024*10000000000000000^4373 ≤ 10000000228849587^4373*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002443259963123 25000000000000000000 10000000228849587 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000228849587/10000000000000000 : ℝ)) (X := (25000002443259963123/25000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (200673472462030337/200000000000000000 : ℝ) ≤ (10007875009456443/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (200673472462030337/200000000000000000 : ℝ)^1024 ≤ (10007875009456443/10000000000000000 : ℝ)^4373 := by
      have hnat : (200673472462030337 : ℕ)^1024*10000000000000000^4373 ≤ 10007875009456443^4373*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200673472462030337 200000000000000000 10007875009456443 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007875009456443/10000000000000000 : ℝ)) (X := (200673472462030337/200000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25168365672247621127/25000000000000000000 : ℝ) ≤ (10015749790063299/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (25168365672247621127/25000000000000000000 : ℝ)^1024 ≤ (10015749790063299/10000000000000000 : ℝ)^4373 := by
      have hnat : (25168365672247621127 : ℕ)^1024*10000000000000000^4373 ≤ 10015749790063299^4373*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25168365672247621127 25000000000000000000 10015749790063299 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015749790063299/10000000000000000 : ℝ)) (X := (25168365672247621127/25000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2443259963123/50000000000000000000 : ℝ) ≤ ((48835887138083989827/48842000000000000000 : ℝ)+2*(984347575857/305262500000000 : ℝ)*(1941/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (48835887138083989827/48842000000000000000 : ℝ)+2*(984347575857/305262500000000 : ℝ)*(1941/100000 : ℝ)=(10000000228849587/10000000000000000 : ℝ) by norm_num, show 1+2*(2443259963123/50000000000000000000 : ℝ)=(25000002443259963123/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(168365672247621127/50000000000000000000 : ℝ)+(2443259963123/50000000000000000000 : ℝ) ≤ ((48835887138083989827/48842000000000000000 : ℝ)+(984347575857/305262500000000 : ℝ)*((13181/50000 : ℝ)+(1941/100000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (48835887138083989827/48842000000000000000 : ℝ)+(984347575857/305262500000000 : ℝ)*((13181/50000 : ℝ)+(1941/100000 : ℝ))=(10007875009456443/10000000000000000 : ℝ) by norm_num, show 1+(168365672247621127/50000000000000000000 : ℝ)+(2443259963123/50000000000000000000 : ℝ)=(200673472462030337/200000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(168365672247621127/50000000000000000000 : ℝ) ≤ ((48835887138083989827/48842000000000000000 : ℝ)+2*(984347575857/305262500000000 : ℝ)*(13181/50000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (48835887138083989827/48842000000000000000 : ℝ)+2*(984347575857/305262500000000 : ℝ)*(13181/50000 : ℝ)=(10015749790063299/10000000000000000 : ℝ) by norm_num, show 1+2*(168365672247621127/50000000000000000000 : ℝ)=(25168365672247621127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48835887138083989827/48842000000000000000 : ℝ)*(X 1 0+X 2 0)+(984347575857/305262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (1941/100000 : ℝ)) (hi := (13181/50000 : ℝ)) (c := (48835887138083989827/48842000000000000000 : ℝ)) (alpha := (984347575857/305262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48835887138083989827/48842000000000000000 : ℝ)*(X 0 1+X 2 1)+(984347575857/305262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (1941/100000 : ℝ)) (hi := (13181/50000 : ℝ)) (c := (48835887138083989827/48842000000000000000 : ℝ)) (alpha := (984347575857/305262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48835887138083989827/48842000000000000000 : ℝ)*(X 0 2+X 1 2)+(984347575857/305262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (1941/100000 : ℝ)) (hi := (13181/50000 : ℝ)) (c := (48835887138083989827/48842000000000000000 : ℝ)) (alpha := (984347575857/305262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-970912509/5000000000 : ℝ)*X 0 0+(1402823569/2500000000 : ℝ)*X 0 1+(5071060419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1349580301/2500000000 : ℝ)*X 1 0+(-1114210973/5000000000 : ℝ)*X 1 1+(5071057599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1349579867/2500000000 : ℝ)*X 2 0+(1267765091/2500000000 : ℝ)*X 2 1+(-1114210333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((133730103/312500000 : ℝ)*X 0 0+(186683173/500000000 : ℝ)*X 0 1+(4895958373/10000000000 : ℝ)*X 0 2+(133730103/312500000 : ℝ)*X 1 0+(186683173/500000000 : ℝ)*X 1 1+(4895958373/10000000000 : ℝ)*X 1 2+(133730103/312500000 : ℝ)*X 2 0+(186683173/500000000 : ℝ)*X 2 1+(4895958373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-194224341/1000000000 : ℝ)*X 0 0+(1269367047/2500000000 : ℝ)*X 0 1+(5604776891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257329591/10000000000 : ℝ)*X 1 0+(-847351529/5000000000 : ℝ)*X 1 1+(560477667/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257330277/10000000000 : ℝ)*X 2 0+(2802388601/5000000000 : ℝ)*X 2 1+(-1694701321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((856052877/2000000000 : ℝ)*X 0 0+(1220541921/2500000000 : ℝ)*X 0 1+(46846141/125000000 : ℝ)*X 0 2+(856052877/2000000000 : ℝ)*X 1 0+(1220541921/2500000000 : ℝ)*X 1 1+(46846141/125000000 : ℝ)*X 1 2+(856052877/2000000000 : ℝ)*X 2 0+(1220541921/2500000000 : ℝ)*X 2 1+(46846141/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1832474862731280577176070353/610525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106406771/100000000000000 : ℝ)*(base1) + (312219/31250000000 : ℝ)*(base19) + (403274781/100000000000000 : ℝ)*(base23) + (440807151/100000000000000 : ℝ)*(upper5) + (338927145973629/25000000000000 : ℝ)*(major0) + (338927145973629/25000000000000 : ℝ)*(major1) + (338927145973629/25000000000000 : ℝ)*(major2) + (1851046119857297/100000000000000 : ℝ)*(sp0) + (185104344979139/10000000000000 : ℝ)*(sp1) + (925522011996397/50000000000000 : ℝ)*(sp2) + (215092582288923/25000000000000 : ℝ)*(sp3) + (1527889/97656250000 : ℝ)*(sp5) + (1586182951/100000000000000 : ℝ)*(sp6) + (618726909/100000000000000 : ℝ)*(sp7) + (215092763572343/25000000000000 : ℝ)*(f.failure) + (925523006725263/50000000000000 : ℝ)*(f.sum) + (306675288967659/122105000000000000000000000000 : ℝ)*base66 + (6469232801494352183/1221050000000000000000000000000000 : ℝ)*base67 + (1216110821891802183/1221050000000000000000000000000000 : ℝ)*base69 + (11896902760115102183/1221050000000000000000000000000000 : ℝ)*base71 + (856315093457/15263125000000000000000000000 : ℝ)*base73 + (7387216582150452183/1221050000000000000000000000000000 : ℝ)*base75 + (5323664732627952183/1221050000000000000000000000000000 : ℝ)*base77 + (1526461296821052183/1221050000000000000000000000000000 : ℝ)*base79 + (269182107414209/122105000000000000000000000000 : ℝ)*base82 + (5267621/2500000000000000000000 : ℝ)*base89 + (5267621/2500000000000000000000 : ℝ)*base91 + (5267621/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1688769864702817593738790779/488420000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30740437/12500000000000 : ℝ)*(base1) + (19418597/2000000000000 : ℝ)*(base19) + (1348122531/100000000000000 : ℝ)*(base23) + (40829033/100000000000000 : ℝ)*(upper3) + (235829283/100000000000000 : ℝ)*(upper5) + (277788936039459/20000000000000 : ℝ)*(major0) + (277788936039459/20000000000000 : ℝ)*(major1) + (277788936039459/20000000000000 : ℝ)*(major2) + (3862906379/100000000000000 : ℝ)*(sp1) + (8700784691/100000000000000 : ℝ)*(sp2) + (7407913550701/390625000000 : ℝ)*(sp4) + (189642078921973/10000000000000 : ℝ)*(sp5) + (948207787074369/50000000000000 : ℝ)*(sp6) + (881463376161191/100000000000000 : ℝ)*(sp7) + (881463622084687/100000000000000 : ℝ)*(f.failure) + (47410640576399/2500000000000 : ℝ)*(f.sum) + (31972484051829/24421000000000000000000000000 : ℝ)*base65 + (721655308019816407/976840000000000000000000000000000 : ℝ)*base68 + (707492476216823593/976840000000000000000000000000000 : ℝ)*base69 + (1700694967376407/976840000000000000000000000000000 : ℝ)*base72 + (10025977121867/12210500000000000000000000000 : ℝ)*base73 + (1763777090683823593/976840000000000000000000000000000 : ℝ)*base75 + (7755674989152496407/976840000000000000000000000000000 : ℝ)*base78 + (6252535961904296407/976840000000000000000000000000000 : ℝ)*base80 + (10742526575201/3052625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (80287789/10000000000000000000000 : ℝ)*base89 + (80287789/10000000000000000000000 : ℝ)*base91 + (80287789/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1414_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1414_s2_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-988044799/5000000000 : ℝ)*x 0 + (5461589339/10000000000 : ℝ)*x 1 + (5198728223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988044799/5000000000 : ℝ)^2187 ≤ (2407601941233/20000000000000 : ℝ)^1675 := by
    have hnat : (988044799 : ℕ)^2187*20000000000000^1675 ≤ 2407601941233^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988044799 5000000000 2407601941233 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461589339/10000000000 : ℝ)^2187 ≤ (45396766730463/100000000000000 : ℝ)^1675 := by
    have hnat : (5461589339 : ℕ)^2187*100000000000000^1675 ≤ 45396766730463^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461589339 10000000000 45396766730463 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198728223/10000000000 : ℝ)^2187 ≤ (8513044709617/20000000000000 : ℝ)^1675 := by
    have hnat : (5198728223 : ℕ)^2187*20000000000000^1675 ≤ 8513044709617^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198728223 10000000000 8513044709617 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988044799/5000000000 : ℝ), (5461589339/10000000000 : ℝ), (5198728223/10000000000 : ℝ)] ![(2407601941233/20000000000000 : ℝ), (45396766730463/100000000000000 : ℝ), (8513044709617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988044799/5000000000 : ℝ)|^2187 ≤ (2407601941233/20000000000000 : ℝ)^1675
        have hw : |(-988044799/5000000000 : ℝ)|=(988044799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461589339/10000000000 : ℝ)|^2187 ≤ (45396766730463/100000000000000 : ℝ)^1675
        have hw : |(5461589339/10000000000 : ℝ)|=(5461589339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198728223/10000000000 : ℝ)|^2187 ≤ (8513044709617/20000000000000 : ℝ)^1675
        have hw : |(5198728223/10000000000 : ℝ)|=(5198728223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1340274809/2500000000 : ℝ)*x 0 + (-2111421519/10000000000 : ℝ)*x 1 + (649841023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340274809/2500000000 : ℝ)^2187 ≤ (8861850528907/20000000000000 : ℝ)^1675 := by
    have hnat : (1340274809 : ℕ)^2187*20000000000000^1675 ≤ 8861850528907^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340274809 2500000000 8861850528907 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111421519/10000000000 : ℝ)^2187 ≤ (3281381053493/25000000000000 : ℝ)^1675 := by
    have hnat : (2111421519 : ℕ)^2187*25000000000000^1675 ≤ 3281381053493^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111421519 10000000000 3281381053493 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649841023/1250000000 : ℝ)^2187 ≤ (42565223131161/100000000000000 : ℝ)^1675 := by
    have hnat : (649841023 : ℕ)^2187*100000000000000^1675 ≤ 42565223131161^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649841023 1250000000 42565223131161 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340274809/2500000000 : ℝ), (-2111421519/10000000000 : ℝ), (649841023/1250000000 : ℝ)] ![(8861850528907/20000000000000 : ℝ), (3281381053493/25000000000000 : ℝ), (42565223131161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340274809/2500000000 : ℝ)|^2187 ≤ (8861850528907/20000000000000 : ℝ)^1675
        have hw : |(1340274809/2500000000 : ℝ)|=(1340274809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111421519/10000000000 : ℝ)|^2187 ≤ (3281381053493/25000000000000 : ℝ)^1675
        have hw : |(-2111421519/10000000000 : ℝ)|=(2111421519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649841023/1250000000 : ℝ)|^2187 ≤ (42565223131161/100000000000000 : ℝ)^1675
        have hw : |(649841023/1250000000 : ℝ)|=(649841023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361098951/10000000000 : ℝ)*x 0 + (1039745701/2000000000 : ℝ)*x 1 + (-84456859/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361098951/10000000000 : ℝ)^2187 ≤ (44309249569009/100000000000000 : ℝ)^1675 := by
    have hnat : (5361098951 : ℕ)^2187*100000000000000^1675 ≤ 44309249569009^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361098951 10000000000 44309249569009 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039745701/2000000000 : ℝ)^2187 ≤ (21282613281381/50000000000000 : ℝ)^1675 := by
    have hnat : (1039745701 : ℕ)^2187*50000000000000^1675 ≤ 21282613281381^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039745701 2000000000 21282613281381 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84456859/400000000 : ℝ)^2187 ≤ (328138096421/2500000000000 : ℝ)^1675 := by
    have hnat : (84456859 : ℕ)^2187*2500000000000^1675 ≤ 328138096421^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84456859 400000000 328138096421 2500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361098951/10000000000 : ℝ), (1039745701/2000000000 : ℝ), (-84456859/400000000 : ℝ)] ![(44309249569009/100000000000000 : ℝ), (21282613281381/50000000000000 : ℝ), (328138096421/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361098951/10000000000 : ℝ)|^2187 ≤ (44309249569009/100000000000000 : ℝ)^1675
        have hw : |(5361098951/10000000000 : ℝ)|=(5361098951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039745701/2000000000 : ℝ)|^2187 ≤ (21282613281381/50000000000000 : ℝ)^1675
        have hw : |(1039745701/2000000000 : ℝ)|=(1039745701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84456859/400000000 : ℝ)|^2187 ≤ (328138096421/2500000000000 : ℝ)^1675
        have hw : |(-84456859/400000000 : ℝ)|=(84456859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860702531/2000000000 : ℝ)*x 0 + (402913923/1000000000 : ℝ)*x 1 + (1148667981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860702531/2000000000 : ℝ)^2187 ≤ (1662888729259/5000000000000 : ℝ)^1675 := by
    have hnat : (860702531 : ℕ)^2187*5000000000000^1675 ≤ 1662888729259^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860702531 2000000000 1662888729259 5000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402913923/1000000000 : ℝ)^2187 ≤ (30516650438983/100000000000000 : ℝ)^1675 := by
    have hnat : (402913923 : ℕ)^2187*100000000000000^1675 ≤ 30516650438983^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402913923 1000000000 30516650438983 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148667981/2500000000 : ℝ)^2187 ≤ (36225574961581/100000000000000 : ℝ)^1675 := by
    have hnat : (1148667981 : ℕ)^2187*100000000000000^1675 ≤ 36225574961581^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148667981 2500000000 36225574961581 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860702531/2000000000 : ℝ), (402913923/1000000000 : ℝ), (1148667981/2500000000 : ℝ)] ![(1662888729259/5000000000000 : ℝ), (30516650438983/100000000000000 : ℝ), (36225574961581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860702531/2000000000 : ℝ)|^2187 ≤ (1662888729259/5000000000000 : ℝ)^1675
        have hw : |(860702531/2000000000 : ℝ)|=(860702531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402913923/1000000000 : ℝ)|^2187 ≤ (30516650438983/100000000000000 : ℝ)^1675
        have hw : |(402913923/1000000000 : ℝ)|=(402913923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1148667981/2500000000 : ℝ)|^2187 ≤ (36225574961581/100000000000000 : ℝ)^1675
        have hw : |(1148667981/2500000000 : ℝ)|=(1148667981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976137739/10000000000 : ℝ)*x 0 + (520025511/1000000000 : ℝ)*x 1 + (1365012471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976137739/10000000000 : ℝ)^2187 ≤ (752399538623/6250000000000 : ℝ)^1675 := by
    have hnat : (1976137739 : ℕ)^2187*6250000000000^1675 ≤ 752399538623^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976137739 10000000000 752399538623 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520025511/1000000000 : ℝ)^2187 ≤ (42581547231623/100000000000000 : ℝ)^1675 := by
    have hnat : (520025511 : ℕ)^2187*100000000000000^1675 ≤ 42581547231623^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520025511 1000000000 42581547231623 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365012471/2500000000 : ℝ)^2187 ≤ (22690030063981/50000000000000 : ℝ)^1675 := by
    have hnat : (1365012471 : ℕ)^2187*50000000000000^1675 ≤ 22690030063981^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365012471 2500000000 22690030063981 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976137739/10000000000 : ℝ), (520025511/1000000000 : ℝ), (1365012471/2500000000 : ℝ)] ![(752399538623/6250000000000 : ℝ), (42581547231623/100000000000000 : ℝ), (22690030063981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976137739/10000000000 : ℝ)|^2187 ≤ (752399538623/6250000000000 : ℝ)^1675
        have hw : |(-1976137739/10000000000 : ℝ)|=(1976137739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520025511/1000000000 : ℝ)|^2187 ≤ (42581547231623/100000000000000 : ℝ)^1675
        have hw : |(520025511/1000000000 : ℝ)|=(520025511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365012471/2500000000 : ℝ)|^2187 ≤ (22690030063981/50000000000000 : ℝ)^1675
        have hw : |(1365012471/2500000000 : ℝ)|=(1365012471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292844309/10000000000 : ℝ)*x 0 + (-925050233/5000000000 : ℝ)*x 1 + (2730024809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292844309/10000000000 : ℝ)^2187 ≤ (21787064695139/50000000000000 : ℝ)^1675 := by
    have hnat : (5292844309 : ℕ)^2187*50000000000000^1675 ≤ 21787064695139^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292844309 10000000000 21787064695139 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925050233/5000000000 : ℝ)^2187 ≤ (1380726669639/12500000000000 : ℝ)^1675 := by
    have hnat : (925050233 : ℕ)^2187*12500000000000^1675 ≤ 1380726669639^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925050233 5000000000 1380726669639 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730024809/5000000000 : ℝ)^2187 ≤ (45380057241379/100000000000000 : ℝ)^1675 := by
    have hnat : (2730024809 : ℕ)^2187*100000000000000^1675 ≤ 45380057241379^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730024809 5000000000 45380057241379 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292844309/10000000000 : ℝ), (-925050233/5000000000 : ℝ), (2730024809/5000000000 : ℝ)] ![(21787064695139/50000000000000 : ℝ), (1380726669639/12500000000000 : ℝ), (45380057241379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292844309/10000000000 : ℝ)|^2187 ≤ (21787064695139/50000000000000 : ℝ)^1675
        have hw : |(5292844309/10000000000 : ℝ)|=(5292844309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-925050233/5000000000 : ℝ)|^2187 ≤ (1380726669639/12500000000000 : ℝ)^1675
        have hw : |(-925050233/5000000000 : ℝ)|=(925050233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730024809/5000000000 : ℝ)|^2187 ≤ (45380057241379/100000000000000 : ℝ)^1675
        have hw : |(2730024809/5000000000 : ℝ)|=(2730024809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2646422883/5000000000 : ℝ)*x 0 + (2730024803/5000000000 : ℝ)*x 1 + (-925049237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646422883/5000000000 : ℝ)^2187 ≤ (4357414505177/10000000000000 : ℝ)^1675 := by
    have hnat : (2646422883 : ℕ)^2187*10000000000000^1675 ≤ 4357414505177^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646422883 5000000000 4357414505177 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730024803/5000000000 : ℝ)^2187 ≤ (45380057111157/100000000000000 : ℝ)^1675 := by
    have hnat : (2730024803 : ℕ)^2187*100000000000000^1675 ≤ 45380057111157^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730024803 5000000000 45380057111157 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925049237/5000000000 : ℝ)^2187 ≤ (11045797828751/100000000000000 : ℝ)^1675 := by
    have hnat : (925049237 : ℕ)^2187*100000000000000^1675 ≤ 11045797828751^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925049237 5000000000 11045797828751 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646422883/5000000000 : ℝ), (2730024803/5000000000 : ℝ), (-925049237/5000000000 : ℝ)] ![(4357414505177/10000000000000 : ℝ), (45380057111157/100000000000000 : ℝ), (11045797828751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646422883/5000000000 : ℝ)|^2187 ≤ (4357414505177/10000000000000 : ℝ)^1675
        have hw : |(2646422883/5000000000 : ℝ)|=(2646422883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730024803/5000000000 : ℝ)|^2187 ≤ (45380057111157/100000000000000 : ℝ)^1675
        have hw : |(2730024803/5000000000 : ℝ)|=(2730024803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-925049237/5000000000 : ℝ)|^2187 ≤ (11045797828751/100000000000000 : ℝ)^1675
        have hw : |(-925049237/5000000000 : ℝ)|=(925049237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s2_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268976083/625000000 : ℝ)*x 0 + (918277451/2000000000 : ℝ)*x 1 + (4032450863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268976083/625000000 : ℝ)^2187 ≤ (4157353846383/12500000000000 : ℝ)^1675 := by
    have hnat : (268976083 : ℕ)^2187*12500000000000^1675 ≤ 4157353846383^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268976083 625000000 4157353846383 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918277451/2000000000 : ℝ)^2187 ≤ (1447670617983/4000000000000 : ℝ)^1675 := by
    have hnat : (918277451 : ℕ)^2187*4000000000000^1675 ≤ 1447670617983^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918277451 2000000000 1447670617983 4000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032450863/10000000000 : ℝ)^2187 ≤ (763735093927/2500000000000 : ℝ)^1675 := by
    have hnat : (4032450863 : ℕ)^2187*2500000000000^1675 ≤ 763735093927^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032450863 10000000000 763735093927 2500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268976083/625000000 : ℝ), (918277451/2000000000 : ℝ), (4032450863/10000000000 : ℝ)] ![(4157353846383/12500000000000 : ℝ), (1447670617983/4000000000000 : ℝ), (763735093927/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268976083/625000000 : ℝ)|^2187 ≤ (4157353846383/12500000000000 : ℝ)^1675
        have hw : |(268976083/625000000 : ℝ)|=(268976083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918277451/2000000000 : ℝ)|^2187 ≤ (1447670617983/4000000000000 : ℝ)^1675
        have hw : |(918277451/2000000000 : ℝ)|=(918277451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032450863/10000000000 : ℝ)|^2187 ≤ (763735093927/2500000000000 : ℝ)^1675
        have hw : |(4032450863/10000000000 : ℝ)|=(4032450863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5143/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15847/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7527/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (797214373666031/50000000000000000000 : ℝ) := by
    have hpowers : (7527/100000 : ℝ)^4373 ≤ (797214373666031/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7527 : ℕ)^4373*50000000000000000000^1024 ≤ 797214373666031^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7527 100000 797214373666031 50000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7527/100000 : ℝ)) (X := (797214373666031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18947/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (410866633578207/500000000000000000 : ℝ) := by
    have hpowers : (18947/100000 : ℝ)^4373 ≤ (410866633578207/500000000000000000 : ℝ)^1024 := by
      have hnat : (18947 : ℕ)^4373*500000000000000000^1024 ≤ 410866633578207^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18947 100000 410866633578207 500000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18947/100000 : ℝ)) (X := (410866633578207/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000797214373666031/25000000000000000000 : ℝ) ≤ (10000074670711241/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (25000797214373666031/25000000000000000000 : ℝ)^1024 ≤ (10000074670711241/10000000000000000 : ℝ)^4373 := by
      have hnat : (25000797214373666031 : ℕ)^1024*10000000000000000^4373 ≤ 10000074670711241^4373*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000797214373666031 25000000000000000000 10000074670711241 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074670711241/10000000000000000 : ℝ)) (X := (25000797214373666031/25000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50041883877731486731/50000000000000000000 : ℝ) ≤ (5000980455988959/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50041883877731486731/50000000000000000000 : ℝ)^1024 ≤ (5000980455988959/5000000000000000 : ℝ)^4373 := by
      have hnat : (50041883877731486731 : ℕ)^1024*5000000000000000^4373 ≤ 5000980455988959^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041883877731486731 50000000000000000000 5000980455988959 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000980455988959/5000000000000000 : ℝ)) (X := (50041883877731486731/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250410866633578207/250000000000000000 : ℝ) ≤ (2000769430648919/2000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (250410866633578207/250000000000000000 : ℝ)^1024 ≤ (2000769430648919/2000000000000000 : ℝ)^4373 := by
      have hnat : (250410866633578207 : ℕ)^1024*2000000000000000^4373 ≤ 2000769430648919^4373*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250410866633578207 250000000000000000 2000769430648919 2000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000769430648919/2000000000000000 : ℝ)) (X := (250410866633578207/250000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(797214373666031/50000000000000000000 : ℝ) ≤ ((57086228631746908331/57100000000000000000 : ℝ)+2*(1886241266677/1142000000000000 : ℝ)*(7527/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (57086228631746908331/57100000000000000000 : ℝ)+2*(1886241266677/1142000000000000 : ℝ)*(7527/100000 : ℝ)=(10000074670711241/10000000000000000 : ℝ) by norm_num, show 1+2*(797214373666031/50000000000000000000 : ℝ)=(25000797214373666031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(410866633578207/500000000000000000 : ℝ)+(797214373666031/50000000000000000000 : ℝ) ≤ ((57086228631746908331/57100000000000000000 : ℝ)+(1886241266677/1142000000000000 : ℝ)*((18947/100000 : ℝ)+(7527/100000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (57086228631746908331/57100000000000000000 : ℝ)+(1886241266677/1142000000000000 : ℝ)*((18947/100000 : ℝ)+(7527/100000 : ℝ))=(5000980455988959/5000000000000000 : ℝ) by norm_num, show 1+(410866633578207/500000000000000000 : ℝ)+(797214373666031/50000000000000000000 : ℝ)=(50041883877731486731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(410866633578207/500000000000000000 : ℝ) ≤ ((57086228631746908331/57100000000000000000 : ℝ)+2*(1886241266677/1142000000000000 : ℝ)*(18947/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (57086228631746908331/57100000000000000000 : ℝ)+2*(1886241266677/1142000000000000 : ℝ)*(18947/100000 : ℝ)=(2000769430648919/2000000000000000 : ℝ) by norm_num, show 1+2*(410866633578207/500000000000000000 : ℝ)=(250410866633578207/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57086228631746908331/57100000000000000000 : ℝ)*(X 1 0+X 2 0)+(1886241266677/1142000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (7527/100000 : ℝ)) (hi := (18947/100000 : ℝ)) (c := (57086228631746908331/57100000000000000000 : ℝ)) (alpha := (1886241266677/1142000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57086228631746908331/57100000000000000000 : ℝ)*(X 0 1+X 2 1)+(1886241266677/1142000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (7527/100000 : ℝ)) (hi := (18947/100000 : ℝ)) (c := (57086228631746908331/57100000000000000000 : ℝ)) (alpha := (1886241266677/1142000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57086228631746908331/57100000000000000000 : ℝ)*(X 0 2+X 1 2)+(1886241266677/1142000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (7527/100000 : ℝ)) (hi := (18947/100000 : ℝ)) (c := (57086228631746908331/57100000000000000000 : ℝ)) (alpha := (1886241266677/1142000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-988044799/5000000000 : ℝ)*X 0 0+(5461589339/10000000000 : ℝ)*X 0 1+(5198728223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340274809/2500000000 : ℝ)*X 1 0+(-2111421519/10000000000 : ℝ)*X 1 1+(649841023/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361098951/10000000000 : ℝ)*X 2 0+(1039745701/2000000000 : ℝ)*X 2 1+(-84456859/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860702531/2000000000 : ℝ)*X 0 0+(402913923/1000000000 : ℝ)*X 0 1+(1148667981/2500000000 : ℝ)*X 0 2+(860702531/2000000000 : ℝ)*X 1 0+(402913923/1000000000 : ℝ)*X 1 1+(1148667981/2500000000 : ℝ)*X 1 2+(860702531/2000000000 : ℝ)*X 2 0+(402913923/1000000000 : ℝ)*X 2 1+(1148667981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1976137739/10000000000 : ℝ)*X 0 0+(520025511/1000000000 : ℝ)*X 0 1+(1365012471/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292844309/10000000000 : ℝ)*X 1 0+(-925050233/5000000000 : ℝ)*X 1 1+(2730024809/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646422883/5000000000 : ℝ)*X 2 0+(2730024803/5000000000 : ℝ)*X 2 1+(-925049237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((268976083/625000000 : ℝ)*X 0 0+(918277451/2000000000 : ℝ)*X 0 1+(4032450863/10000000000 : ℝ)*X 0 2+(268976083/625000000 : ℝ)*X 1 0+(918277451/2000000000 : ℝ)*X 1 1+(4032450863/10000000000 : ℝ)*X 1 2+(268976083/625000000 : ℝ)*X 2 0+(918277451/2000000000 : ℝ)*X 2 1+(4032450863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4956396288896061537311453721/713750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (975094533/100000000000000 : ℝ)*(base19) + (581839831/100000000000000 : ℝ)*(base23) + (20480973/20000000000000 : ℝ)*(lower2) + (52205661/25000000000000 : ℝ)*(upper3) + (27128849/50000000000000 : ℝ)*(upper5) + (696570857565299/25000000000000 : ℝ)*(major0) + (696570857565299/25000000000000 : ℝ)*(major1) + (696570857565299/25000000000000 : ℝ)*(major2) + (3804302913799919/100000000000000 : ℝ)*(sp0) + (1902155647685283/50000000000000 : ℝ)*(sp1) + (951077922156317/25000000000000 : ℝ)*(sp2) + (22103106850253/1250000000000 : ℝ)*(sp3) + (467833259/5000000000000 : ℝ)*(sp4) + (5810564949/100000000000000 : ℝ)*(sp7) + (1768254358585189/100000000000000 : ℝ)*(f.failure) + (3804312270465099/100000000000000 : ℝ)*(f.sum) + (12454468986673/14275000000000000000000000000 : ℝ)*base65 + (2166865705369244031/1427500000000000000000000000000000 : ℝ)*base68 + (9648995992939244031/1427500000000000000000000000000000 : ℝ)*base70 + (7866712628749244031/1427500000000000000000000000000000 : ℝ)*base72 + (14436805799037/3568750000000000000000000000 : ℝ)*base73 + (1686371139631744031/1427500000000000000000000000000000 : ℝ)*base76 + (9561735110579244031/1427500000000000000000000000000000 : ℝ)*base78 + (11547440706441744031/1427500000000000000000000000000000 : ℝ)*base80 + (24114455030249/7137500000000000000000000000 : ℝ)*base81 + (52793617/10000000000000000000000 : ℝ)*base90 + (52793617/10000000000000000000000 : ℝ)*base92 + (52793617/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6950849703079923147321275187/713750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620608507/50000000000000 : ℝ)*(base19) + (3450460881/100000000000000 : ℝ)*(base23) + (235620909/100000000000000 : ℝ)*(upper3) + (159133911/50000000000000 : ℝ)*(lower4) + (2923983/2000000000000 : ℝ)*(upper5) + (704788556764259/25000000000000 : ℝ)*(major0) + (704788556764259/25000000000000 : ℝ)*(major1) + (704788556764259/25000000000000 : ℝ)*(major2) + (2157275401/25000000000000 : ℝ)*(sp1) + (51150947737/100000000000000 : ℝ)*(sp2) + (481149129065961/12500000000000 : ℝ)*(sp4) + (384918316220907/10000000000000 : ℝ)*(sp5) + (384913843111907/10000000000000 : ℝ)*(sp6) + (223639387121241/12500000000000 : ℝ)*(sp7) + (223639387121241/12500000000000 : ℝ)*(f.failure) + (481149129065961/12500000000000 : ℝ)*(f.sum) + (70487175857543/14275000000000000000000000000 : ℝ)*base65 + (2937367928982708271/1427500000000000000000000000000000 : ℝ)*base68 + (11251150215377291729/1427500000000000000000000000000000 : ℝ)*base69 + (7011570141272291729/1427500000000000000000000000000000 : ℝ)*base71 + (33350340931743/14275000000000000000000000000 : ℝ)*base73 + (10036949160832708271/1427500000000000000000000000000000 : ℝ)*base76 + (8961333094085208271/1427500000000000000000000000000000 : ℝ)*base78 + (1026293631920208271/1427500000000000000000000000000000 : ℝ)*base80 + (27584310550967/3568750000000000000000000000 : ℝ)*base81 + (7829173/1250000000000000000000 : ℝ)*base90 + (7829173/1250000000000000000000 : ℝ)*base92 + (7829173/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1414_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1414_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1414_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1414_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1414_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

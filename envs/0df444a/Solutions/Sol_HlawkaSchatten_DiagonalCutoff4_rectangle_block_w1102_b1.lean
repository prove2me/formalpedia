-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:36.094097+00:00
-- url     : https://prove2.me/submissions/d74f5fd9-74e9-4be1-9536-7824e1320c40

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
theorem support_rectangle_w1102_s3_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090946717/5000000000 : ℝ)*x 0 + (5433448249/10000000000 : ℝ)*x 1 + (653520589/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090946717/5000000000 : ℝ)^8295 ≤ (2649161662269/20000000000000 : ℝ)^6247 := by
    have hnat : (1090946717 : ℕ)^8295*20000000000000^6247 ≤ 2649161662269^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090946717 5000000000 2649161662269 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433448249/10000000000 : ℝ)^8295 ≤ (44486004069581/100000000000000 : ℝ)^6247 := by
    have hnat : (5433448249 : ℕ)^8295*100000000000000^6247 ≤ 44486004069581^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433448249 10000000000 44486004069581 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653520589/1250000000 : ℝ)^8295 ≤ (132088086267/312500000000 : ℝ)^6247 := by
    have hnat : (653520589 : ℕ)^8295*312500000000^6247 ≤ 132088086267^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653520589 1250000000 132088086267 312500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090946717/5000000000 : ℝ), (5433448249/10000000000 : ℝ), (653520589/1250000000 : ℝ)] ![(2649161662269/20000000000000 : ℝ), (44486004069581/100000000000000 : ℝ), (132088086267/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090946717/5000000000 : ℝ)|^8295 ≤ (2649161662269/20000000000000 : ℝ)^6247
        have hw : |(-1090946717/5000000000 : ℝ)|=(1090946717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433448249/10000000000 : ℝ)|^8295 ≤ (44486004069581/100000000000000 : ℝ)^6247
        have hw : |(5433448249/10000000000 : ℝ)|=(5433448249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653520589/1250000000 : ℝ)|^8295 ≤ (132088086267/312500000000 : ℝ)^6247
        have hw : |(653520589/1250000000 : ℝ)|=(653520589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677388023/5000000000 : ℝ)*x 0 + (-2286922777/10000000000 : ℝ)*x 1 + (20422519/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677388023/5000000000 : ℝ)^8295 ≤ (43632749351439/100000000000000 : ℝ)^6247 := by
    have hnat : (2677388023 : ℕ)^8295*100000000000000^6247 ≤ 43632749351439^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677388023 5000000000 43632749351439 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286922777/10000000000 : ℝ)^8295 ≤ (2819812281107/20000000000000 : ℝ)^6247 := by
    have hnat : (2286922777 : ℕ)^8295*20000000000000^6247 ≤ 2819812281107^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286922777 10000000000 2819812281107 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20422519/39062500 : ℝ)^8295 ≤ (42268189237187/100000000000000 : ℝ)^6247 := by
    have hnat : (20422519 : ℕ)^8295*100000000000000^6247 ≤ 42268189237187^6247*39062500^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20422519 39062500 42268189237187 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677388023/5000000000 : ℝ), (-2286922777/10000000000 : ℝ), (20422519/39062500 : ℝ)] ![(43632749351439/100000000000000 : ℝ), (2819812281107/20000000000000 : ℝ), (42268189237187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677388023/5000000000 : ℝ)|^8295 ≤ (43632749351439/100000000000000 : ℝ)^6247
        have hw : |(2677388023/5000000000 : ℝ)|=(2677388023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286922777/10000000000 : ℝ)|^8295 ≤ (2819812281107/20000000000000 : ℝ)^6247
        have hw : |(-2286922777/10000000000 : ℝ)|=(2286922777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20422519/39062500 : ℝ)|^8295 ≤ (42268189237187/100000000000000 : ℝ)^6247
        have hw : |(20422519/39062500 : ℝ)|=(20422519/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535477619/1000000000 : ℝ)*x 0 + (32676031/62500000 : ℝ)*x 1 + (-114346123/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535477619/1000000000 : ℝ)^8295 ≤ (43632750909479/100000000000000 : ℝ)^6247 := by
    have hnat : (535477619 : ℕ)^8295*100000000000000^6247 ≤ 43632750909479^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535477619 1000000000 43632750909479 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32676031/62500000 : ℝ)^8295 ≤ (10567047566941/25000000000000 : ℝ)^6247 := by
    have hnat : (32676031 : ℕ)^8295*25000000000000^6247 ≤ 10567047566941^6247*62500000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32676031 62500000 10567047566941 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114346123/500000000 : ℝ)^8295 ≤ (7049529405251/50000000000000 : ℝ)^6247 := by
    have hnat : (114346123 : ℕ)^8295*50000000000000^6247 ≤ 7049529405251^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114346123 500000000 7049529405251 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535477619/1000000000 : ℝ), (32676031/62500000 : ℝ), (-114346123/500000000 : ℝ)] ![(43632750909479/100000000000000 : ℝ), (10567047566941/25000000000000 : ℝ), (7049529405251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535477619/1000000000 : ℝ)|^8295 ≤ (43632750909479/100000000000000 : ℝ)^6247
        have hw : |(535477619/1000000000 : ℝ)|=(535477619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32676031/62500000 : ℝ)|^8295 ≤ (10567047566941/25000000000000 : ℝ)^6247
        have hw : |(32676031/62500000 : ℝ)|=(32676031/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114346123/500000000 : ℝ)|^8295 ≤ (7049529405251/50000000000000 : ℝ)^6247
        have hw : |(-114346123/500000000 : ℝ)|=(114346123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218390479/500000000 : ℝ)*x 0 + (4169920577/10000000000 : ℝ)*x 1 + (4575124011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218390479/500000000 : ℝ)^8295 ≤ (2080696387383/6250000000000 : ℝ)^6247 := by
    have hnat : (218390479 : ℕ)^8295*6250000000000^6247 ≤ 2080696387383^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218390479 500000000 2080696387383 6250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169920577/10000000000 : ℝ)^8295 ≤ (7825849405869/25000000000000 : ℝ)^6247 := by
    have hnat : (4169920577 : ℕ)^8295*25000000000000^6247 ≤ 7825849405869^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169920577 10000000000 7825849405869 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575124011/10000000000 : ℝ)^8295 ≤ (35405460159253/100000000000000 : ℝ)^6247 := by
    have hnat : (4575124011 : ℕ)^8295*100000000000000^6247 ≤ 35405460159253^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575124011 10000000000 35405460159253 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218390479/500000000 : ℝ), (4169920577/10000000000 : ℝ), (4575124011/10000000000 : ℝ)] ![(2080696387383/6250000000000 : ℝ), (7825849405869/25000000000000 : ℝ), (35405460159253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218390479/500000000 : ℝ)|^8295 ≤ (2080696387383/6250000000000 : ℝ)^6247
        have hw : |(218390479/500000000 : ℝ)|=(218390479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169920577/10000000000 : ℝ)|^8295 ≤ (7825849405869/25000000000000 : ℝ)^6247
        have hw : |(4169920577/10000000000 : ℝ)|=(4169920577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575124011/10000000000 : ℝ)|^8295 ≤ (35405460159253/100000000000000 : ℝ)^6247
        have hw : |(4575124011/10000000000 : ℝ)|=(4575124011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090957073/5000000000 : ℝ)*x 0 + (1307246073/2500000000 : ℝ)*x 1 + (5432623553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090957073/5000000000 : ℝ)^8295 ≤ (662298763569/5000000000000 : ℝ)^6247 := by
    have hnat : (1090957073 : ℕ)^8295*5000000000000^6247 ≤ 662298763569^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090957073 5000000000 662298763569 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307246073/2500000000 : ℝ)^8295 ≤ (42276986168691/100000000000000 : ℝ)^6247 := by
    have hnat : (1307246073 : ℕ)^8295*100000000000000^6247 ≤ 42276986168691^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307246073 2500000000 42276986168691 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432623553/10000000000 : ℝ)^8295 ≤ (889540770849/2000000000000 : ℝ)^6247 := by
    have hnat : (5432623553 : ℕ)^8295*2000000000000^6247 ≤ 889540770849^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432623553 10000000000 889540770849 2000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090957073/5000000000 : ℝ), (1307246073/2500000000 : ℝ), (5432623553/10000000000 : ℝ)] ![(662298763569/5000000000000 : ℝ), (42276986168691/100000000000000 : ℝ), (889540770849/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090957073/5000000000 : ℝ)|^8295 ≤ (662298763569/5000000000000 : ℝ)^6247
        have hw : |(-1090957073/5000000000 : ℝ)|=(1090957073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307246073/2500000000 : ℝ)|^8295 ≤ (42276986168691/100000000000000 : ℝ)^6247
        have hw : |(1307246073/2500000000 : ℝ)|=(1307246073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432623553/10000000000 : ℝ)|^8295 ≤ (889540770849/2000000000000 : ℝ)^6247
        have hw : |(5432623553/10000000000 : ℝ)|=(5432623553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325730663/2500000000 : ℝ)*x 0 + (-2082464369/10000000000 : ℝ)*x 1 + (5432623613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325730663/2500000000 : ℝ)^8295 ≤ (21536301234193/50000000000000 : ℝ)^6247 := by
    have hnat : (1325730663 : ℕ)^8295*50000000000000^6247 ≤ 21536301234193^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325730663 2500000000 21536301234193 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082464369/10000000000 : ℝ)^8295 ≤ (2490071664283/20000000000000 : ℝ)^6247 := by
    have hnat : (2082464369 : ℕ)^8295*20000000000000^6247 ≤ 2490071664283^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082464369 10000000000 2490071664283 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432623613/10000000000 : ℝ)^8295 ≤ (5559629899339/12500000000000 : ℝ)^6247 := by
    have hnat : (5432623613 : ℕ)^8295*12500000000000^6247 ≤ 5559629899339^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432623613 10000000000 5559629899339 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325730663/2500000000 : ℝ), (-2082464369/10000000000 : ℝ), (5432623613/10000000000 : ℝ)] ![(21536301234193/50000000000000 : ℝ), (2490071664283/20000000000000 : ℝ), (5559629899339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325730663/2500000000 : ℝ)|^8295 ≤ (21536301234193/50000000000000 : ℝ)^6247
        have hw : |(1325730663/2500000000 : ℝ)|=(1325730663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082464369/10000000000 : ℝ)|^8295 ≤ (2490071664283/20000000000000 : ℝ)^6247
        have hw : |(-2082464369/10000000000 : ℝ)|=(2082464369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432623613/10000000000 : ℝ)|^8295 ≤ (5559629899339/12500000000000 : ℝ)^6247
        have hw : |(5432623613/10000000000 : ℝ)|=(5432623613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060584669/2000000000 : ℝ)*x 0 + (5432623993/10000000000 : ℝ)*x 1 + (-2082462907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060584669/2000000000 : ℝ)^8295 ≤ (43072609942573/100000000000000 : ℝ)^6247 := by
    have hnat : (1060584669 : ℕ)^8295*100000000000000^6247 ≤ 43072609942573^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060584669 2000000000 43072609942573 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432623993/10000000000 : ℝ)^8295 ≤ (11119260831427/25000000000000 : ℝ)^6247 := by
    have hnat : (5432623993 : ℕ)^8295*25000000000000^6247 ≤ 11119260831427^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432623993 10000000000 11119260831427 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082462907/10000000000 : ℝ)^8295 ≤ (12450346715043/100000000000000 : ℝ)^6247 := by
    have hnat : (2082462907 : ℕ)^8295*100000000000000^6247 ≤ 12450346715043^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082462907 10000000000 12450346715043 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060584669/2000000000 : ℝ), (5432623993/10000000000 : ℝ), (-2082462907/10000000000 : ℝ)] ![(43072609942573/100000000000000 : ℝ), (11119260831427/25000000000000 : ℝ), (12450346715043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060584669/2000000000 : ℝ)|^8295 ≤ (43072609942573/100000000000000 : ℝ)^6247
        have hw : |(1060584669/2000000000 : ℝ)|=(1060584669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432623993/10000000000 : ℝ)|^8295 ≤ (11119260831427/25000000000000 : ℝ)^6247
        have hw : |(5432623993/10000000000 : ℝ)|=(5432623993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082462907/10000000000 : ℝ)|^8295 ≤ (12450346715043/100000000000000 : ℝ)^6247
        have hw : |(-2082462907/10000000000 : ℝ)|=(2082462907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s3_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367848817/10000000000 : ℝ)*x 0 + (4573507057/10000000000 : ℝ)*x 1 + (4171547407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367848817/10000000000 : ℝ)^8295 ≤ (4161442413001/12500000000000 : ℝ)^6247 := by
    have hnat : (4367848817 : ℕ)^8295*12500000000000^6247 ≤ 4161442413001^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367848817 10000000000 4161442413001 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573507057/10000000000 : ℝ)^8295 ≤ (8847211438879/25000000000000 : ℝ)^6247 := by
    have hnat : (4573507057 : ℕ)^8295*25000000000000^6247 ≤ 8847211438879^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573507057 10000000000 8847211438879 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171547407/10000000000 : ℝ)^8295 ≤ (6263922984477/20000000000000 : ℝ)^6247 := by
    have hnat : (4171547407 : ℕ)^8295*20000000000000^6247 ≤ 6263922984477^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171547407 10000000000 6263922984477 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367848817/10000000000 : ℝ), (4573507057/10000000000 : ℝ), (4171547407/10000000000 : ℝ)] ![(4161442413001/12500000000000 : ℝ), (8847211438879/25000000000000 : ℝ), (6263922984477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367848817/10000000000 : ℝ)|^8295 ≤ (4161442413001/12500000000000 : ℝ)^6247
        have hw : |(4367848817/10000000000 : ℝ)|=(4367848817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573507057/10000000000 : ℝ)|^8295 ≤ (8847211438879/25000000000000 : ℝ)^6247
        have hw : |(4573507057/10000000000 : ℝ)|=(4573507057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171547407/10000000000 : ℝ)|^8295 ≤ (6263922984477/20000000000000 : ℝ)^6247
        have hw : |(4171547407/10000000000 : ℝ)|=(4171547407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (657/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1857/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (133/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1777/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (133/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1777/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (133/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1777/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (133/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1777/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (133/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1777/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (133/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1777/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1777/20000 : ℝ) ^ (4147/1024 : ℝ) ≤ (1381045379433679/25000000000000000000 : ℝ) := by
    have hpowers : (1777/20000 : ℝ)^4147 ≤ (1381045379433679/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1777 : ℕ)^4147*25000000000000000000^1024 ≤ 1381045379433679^1024*20000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1777 20000 1381045379433679 25000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1777/20000 : ℝ)) (X := (1381045379433679/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (133/800 : ℝ) ^ (4147/1024 : ℝ) ≤ (34930668557812891/50000000000000000000 : ℝ) := by
    have hpowers : (133/800 : ℝ)^4147 ≤ (34930668557812891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (133 : ℕ)^4147*50000000000000000000^1024 ≤ 34930668557812891^1024*800^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133 800 34930668557812891 50000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (133/800 : ℝ)) (X := (34930668557812891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501381045379433679/12500000000000000000 : ℝ) ≤ (5000136400447583/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (12501381045379433679/12500000000000000000 : ℝ)^1024 ≤ (5000136400447583/5000000000000000 : ℝ)^4147 := by
      have hnat : (12501381045379433679 : ℕ)^1024*5000000000000000^4147 ≤ 5000136400447583^4147*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501381045379433679 12500000000000000000 5000136400447583 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136400447583/5000000000000000 : ℝ)) (X := (12501381045379433679/12500000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037692759316680249/50000000000000000000 : ℝ) ≤ (2500465233112131/2500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50037692759316680249/50000000000000000000 : ℝ)^1024 ≤ (2500465233112131/2500000000000000 : ℝ)^4147 := by
      have hnat : (50037692759316680249 : ℕ)^1024*2500000000000000^4147 ≤ 2500465233112131^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037692759316680249 50000000000000000000 2500465233112131 2500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500465233112131/2500000000000000 : ℝ)) (X := (50037692759316680249/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034930668557812891/25000000000000000000 : ℝ) ≤ (5001724532000941/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25034930668557812891/25000000000000000000 : ℝ)^1024 ≤ (5001724532000941/5000000000000000 : ℝ)^4147 := by
      have hnat : (25034930668557812891 : ℕ)^1024*5000000000000000^4147 ≤ 5001724532000941^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034930668557812891 25000000000000000000 5001724532000941 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001724532000941/5000000000000000 : ℝ)) (X := (25034930668557812891/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1381045379433679/25000000000000000000 : ℝ) ≤ ((3868694519061270659/3870000000000000000 : ℝ)+2*(794065776679/387000000000000 : ℝ)*(1777/20000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (3868694519061270659/3870000000000000000 : ℝ)+2*(794065776679/387000000000000 : ℝ)*(1777/20000 : ℝ)=(5000136400447583/5000000000000000 : ℝ) by norm_num, show 1+2*(1381045379433679/25000000000000000000 : ℝ)=(12501381045379433679/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34930668557812891/50000000000000000000 : ℝ)+(1381045379433679/25000000000000000000 : ℝ) ≤ ((3868694519061270659/3870000000000000000 : ℝ)+(794065776679/387000000000000 : ℝ)*((133/800 : ℝ)+(1777/20000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (3868694519061270659/3870000000000000000 : ℝ)+(794065776679/387000000000000 : ℝ)*((133/800 : ℝ)+(1777/20000 : ℝ))=(2500465233112131/2500000000000000 : ℝ) by norm_num, show 1+(34930668557812891/50000000000000000000 : ℝ)+(1381045379433679/25000000000000000000 : ℝ)=(50037692759316680249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34930668557812891/50000000000000000000 : ℝ) ≤ ((3868694519061270659/3870000000000000000 : ℝ)+2*(794065776679/387000000000000 : ℝ)*(133/800 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (3868694519061270659/3870000000000000000 : ℝ)+2*(794065776679/387000000000000 : ℝ)*(133/800 : ℝ)=(5001724532000941/5000000000000000 : ℝ) by norm_num, show 1+2*(34930668557812891/50000000000000000000 : ℝ)=(25034930668557812891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3868694519061270659/3870000000000000000 : ℝ)*(X 1 0+X 2 0)+(794065776679/387000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (133/800 : ℝ)) (c := (3868694519061270659/3870000000000000000 : ℝ)) (alpha := (794065776679/387000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3868694519061270659/3870000000000000000 : ℝ)*(X 0 1+X 2 1)+(794065776679/387000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (133/800 : ℝ)) (c := (3868694519061270659/3870000000000000000 : ℝ)) (alpha := (794065776679/387000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3868694519061270659/3870000000000000000 : ℝ)*(X 0 2+X 1 2)+(794065776679/387000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (133/800 : ℝ)) (c := (3868694519061270659/3870000000000000000 : ℝ)) (alpha := (794065776679/387000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090946717/5000000000 : ℝ)*X 0 0+(5433448249/10000000000 : ℝ)*X 0 1+(653520589/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677388023/5000000000 : ℝ)*X 1 0+(-2286922777/10000000000 : ℝ)*X 1 1+(20422519/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535477619/1000000000 : ℝ)*X 2 0+(32676031/62500000 : ℝ)*X 2 1+(-114346123/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218390479/500000000 : ℝ)*X 0 0+(4169920577/10000000000 : ℝ)*X 0 1+(4575124011/10000000000 : ℝ)*X 0 2+(218390479/500000000 : ℝ)*X 1 0+(4169920577/10000000000 : ℝ)*X 1 1+(4575124011/10000000000 : ℝ)*X 1 2+(218390479/500000000 : ℝ)*X 2 0+(4169920577/10000000000 : ℝ)*X 2 1+(4575124011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090957073/5000000000 : ℝ)*X 0 0+(1307246073/2500000000 : ℝ)*X 0 1+(5432623553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325730663/2500000000 : ℝ)*X 1 0+(-2082464369/10000000000 : ℝ)*X 1 1+(5432623613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060584669/2000000000 : ℝ)*X 2 0+(5432623993/10000000000 : ℝ)*X 2 1+(-2082462907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367848817/10000000000 : ℝ)*X 0 0+(4573507057/10000000000 : ℝ)*X 0 1+(4171547407/10000000000 : ℝ)*X 0 2+(4367848817/10000000000 : ℝ)*X 1 0+(4573507057/10000000000 : ℝ)*X 1 1+(4171547407/10000000000 : ℝ)*X 1 2+(4367848817/10000000000 : ℝ)*X 2 0+(4573507057/10000000000 : ℝ)*X 2 1+(4171547407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100299155134362732801530763/10750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1197514577/50000000000000 : ℝ)*(base19) + (2239083611/100000000000000 : ℝ)*(base23) + (76826781/50000000000000 : ℝ)*(lower2) + (166301703/100000000000000 : ℝ)*(upper3) + (36494297/12500000000000 : ℝ)*(upper5) + (3669672176760429/100000000000000 : ℝ)*(major0) + (3669672176760429/100000000000000 : ℝ)*(major1) + (3669672176760429/100000000000000 : ℝ)*(major2) + (2435677369950171/50000000000000 : ℝ)*(sp0) + (2435701864943957/50000000000000 : ℝ)*(sp1) + (2435701942916729/50000000000000 : ℝ)*(sp2) + (1233958520894637/50000000000000 : ℝ)*(sp3) + (25692508363/50000000000000 : ℝ)*(sp4) + (10437904687/50000000000000 : ℝ)*(sp7) + (308492239699831/12500000000000 : ℝ)*(f.failure) + (1217851531229267/25000000000000 : ℝ)*(f.sum) + (6273366784401/2150000000000000000000000000 : ℝ)*base66 + (101804005142318079/43000000000000000000000000000000 : ℝ)*base67 + (423791546278318079/43000000000000000000000000000000 : ℝ)*base69 + (368294314034318079/43000000000000000000000000000000 : ℝ)*base71 + (7156868830001/2150000000000000000000000000 : ℝ)*base74 + (199100433576318079/43000000000000000000000000000000 : ℝ)*base75 + (237073064066318079/43000000000000000000000000000000 : ℝ)*base77 + (217495183647681921/43000000000000000000000000000000 : ℝ)*base80 + (11863410794899/2150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10062509/1250000000000000000000 : ℝ)*base90 + (10062509/1250000000000000000000 : ℝ)*base92 + (10062509/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62267202970955031692721937/16125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63116499/6250000000000 : ℝ)*(base19) + (338248427/12500000000000 : ℝ)*(base23) + (147442179/50000000000000 : ℝ)*(upper2) + (243917451/100000000000000 : ℝ)*(upper3) + (30843351/25000000000000 : ℝ)*(upper5) + (924807276320443/25000000000000 : ℝ)*(major0) + (924807276320443/25000000000000 : ℝ)*(major1) + (924807276320443/25000000000000 : ℝ)*(major2) + (1207037101/10000000000000 : ℝ)*(sp1) + (3151595767/5000000000000 : ℝ)*(sp2) + (4910642458252731/100000000000000 : ℝ)*(sp4) + (4910629378017737/100000000000000 : ℝ)*(sp5) + (196423068813999/4000000000000 : ℝ)*(sp6) + (621953905898269/25000000000000 : ℝ)*(sp7) + (621953905898269/25000000000000 : ℝ)*(f.failure) + (4910642458252731/100000000000000 : ℝ)*(f.sum) + (2306866469159/604687500000000000000000000 : ℝ)*base65 + (262428986075416021/32250000000000000000000000000000 : ℝ)*base68 + (205449311685166021/32250000000000000000000000000000 : ℝ)*base70 + (129783358742416021/32250000000000000000000000000000 : ℝ)*base72 + (1174528269481/9675000000000000000000000000 : ℝ)*base74 + (58003704175666021/32250000000000000000000000000000 : ℝ)*base76 + (107269750547833979/32250000000000000000000000000000 : ℝ)*base77 + (6815456207833979/32250000000000000000000000000000 : ℝ)*base79 + (14044315805131/9675000000000000000000000000 : ℝ)*base82 + (9173391/2500000000000000000000 : ℝ)*base90 + (9173391/2500000000000000000000 : ℝ)*base92 + (9173391/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1102_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1857/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s4_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43704737/200000000 : ℝ)*x 0 + (135097199/250000000 : ℝ)*x 1 + (5255539213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43704737/200000000 : ℝ)^8295 ≤ (13272766410499/100000000000000 : ℝ)^6247 := by
    have hnat : (43704737 : ℕ)^8295*100000000000000^6247 ≤ 13272766410499^6247*200000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43704737 200000000 13272766410499 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135097199/250000000 : ℝ)^8295 ≤ (5520615488081/12500000000000 : ℝ)^6247 := by
    have hnat : (135097199 : ℕ)^8295*12500000000000^6247 ≤ 5520615488081^6247*250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135097199 250000000 5520615488081 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255539213/10000000000 : ℝ)^8295 ≤ (665036088617/1562500000000 : ℝ)^6247 := by
    have hnat : (5255539213 : ℕ)^8295*1562500000000^6247 ≤ 665036088617^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255539213 10000000000 665036088617 1562500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43704737/200000000 : ℝ), (135097199/250000000 : ℝ), (5255539213/10000000000 : ℝ)] ![(13272766410499/100000000000000 : ℝ), (5520615488081/12500000000000 : ℝ), (665036088617/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43704737/200000000 : ℝ)|^8295 ≤ (13272766410499/100000000000000 : ℝ)^6247
        have hw : |(-43704737/200000000 : ℝ)|=(43704737/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135097199/250000000 : ℝ)|^8295 ≤ (5520615488081/12500000000000 : ℝ)^6247
        have hw : |(135097199/250000000 : ℝ)|=(135097199/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255539213/10000000000 : ℝ)|^8295 ≤ (665036088617/1562500000000 : ℝ)^6247
        have hw : |(5255539213/10000000000 : ℝ)|=(5255539213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347424831/10000000000 : ℝ)*x 0 + (-2260657257/10000000000 : ℝ)*x 1 + (2627770041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347424831/10000000000 : ℝ)^8295 ≤ (43553229143923/100000000000000 : ℝ)^6247 := by
    have hnat : (5347424831 : ℕ)^8295*100000000000000^6247 ≤ 43553229143923^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347424831 10000000000 43553229143923 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260657257/10000000000 : ℝ)^8295 ≤ (3471112958303/25000000000000 : ℝ)^6247 := by
    have hnat : (2260657257 : ℕ)^8295*25000000000000^6247 ≤ 3471112958303^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260657257 10000000000 3471112958303 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627770041/5000000000 : ℝ)^8295 ≤ (5320289877043/12500000000000 : ℝ)^6247 := by
    have hnat : (2627770041 : ℕ)^8295*12500000000000^6247 ≤ 5320289877043^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627770041 5000000000 5320289877043 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347424831/10000000000 : ℝ), (-2260657257/10000000000 : ℝ), (2627770041/5000000000 : ℝ)] ![(43553229143923/100000000000000 : ℝ), (3471112958303/25000000000000 : ℝ), (5320289877043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347424831/10000000000 : ℝ)|^8295 ≤ (43553229143923/100000000000000 : ℝ)^6247
        have hw : |(5347424831/10000000000 : ℝ)|=(5347424831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260657257/10000000000 : ℝ)|^8295 ≤ (3471112958303/25000000000000 : ℝ)^6247
        have hw : |(-2260657257/10000000000 : ℝ)|=(2260657257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627770041/5000000000 : ℝ)|^8295 ≤ (5320289877043/12500000000000 : ℝ)^6247
        have hw : |(2627770041/5000000000 : ℝ)|=(2627770041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347424493/10000000000 : ℝ)*x 0 + (5255540033/10000000000 : ℝ)*x 1 + (-2260657769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347424493/10000000000 : ℝ)^8295 ≤ (43553225488503/100000000000000 : ℝ)^6247 := by
    have hnat : (5347424493 : ℕ)^8295*100000000000000^6247 ≤ 43553225488503^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347424493 10000000000 43553225488503 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255540033/10000000000 : ℝ)^8295 ≤ (21281159244709/50000000000000 : ℝ)^6247 := by
    have hnat : (5255540033 : ℕ)^8295*50000000000000^6247 ≤ 21281159244709^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255540033 10000000000 21281159244709 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260657769/10000000000 : ℝ)^8295 ≤ (3471114002179/25000000000000 : ℝ)^6247 := by
    have hnat : (2260657769 : ℕ)^8295*25000000000000^6247 ≤ 3471114002179^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260657769 10000000000 3471114002179 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347424493/10000000000 : ℝ), (5255540033/10000000000 : ℝ), (-2260657769/10000000000 : ℝ)] ![(43553225488503/100000000000000 : ℝ), (21281159244709/50000000000000 : ℝ), (3471114002179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347424493/10000000000 : ℝ)|^8295 ≤ (43553225488503/100000000000000 : ℝ)^6247
        have hw : |(5347424493/10000000000 : ℝ)|=(5347424493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255540033/10000000000 : ℝ)|^8295 ≤ (21281159244709/50000000000000 : ℝ)^6247
        have hw : |(5255540033/10000000000 : ℝ)|=(5255540033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260657769/10000000000 : ℝ)|^8295 ≤ (3471114002179/25000000000000 : ℝ)^6247
        have hw : |(-2260657769/10000000000 : ℝ)|=(2260657769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184900223/5000000000 : ℝ)*x 0 + (845170353/2000000000 : ℝ)*x 1 + (564834161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184900223/5000000000 : ℝ)^8295 ≤ (33311292629937/100000000000000 : ℝ)^6247 := by
    have hnat : (2184900223 : ℕ)^8295*100000000000000^6247 ≤ 33311292629937^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184900223 5000000000 33311292629937 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845170353/2000000000 : ℝ)^8295 ≤ (31862142541357/100000000000000 : ℝ)^6247 := by
    have hnat : (845170353 : ℕ)^8295*100000000000000^6247 ≤ 31862142541357^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845170353 2000000000 31862142541357 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564834161/1250000000 : ℝ)^8295 ≤ (34826564815089/100000000000000 : ℝ)^6247 := by
    have hnat : (564834161 : ℕ)^8295*100000000000000^6247 ≤ 34826564815089^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564834161 1250000000 34826564815089 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184900223/5000000000 : ℝ), (845170353/2000000000 : ℝ), (564834161/1250000000 : ℝ)] ![(33311292629937/100000000000000 : ℝ), (31862142541357/100000000000000 : ℝ), (34826564815089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184900223/5000000000 : ℝ)|^8295 ≤ (33311292629937/100000000000000 : ℝ)^6247
        have hw : |(2184900223/5000000000 : ℝ)|=(2184900223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845170353/2000000000 : ℝ)|^8295 ≤ (31862142541357/100000000000000 : ℝ)^6247
        have hw : |(845170353/2000000000 : ℝ)|=(845170353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564834161/1250000000 : ℝ)|^8295 ≤ (34826564815089/100000000000000 : ℝ)^6247
        have hw : |(564834161/1250000000 : ℝ)|=(564834161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185243723/10000000000 : ℝ)*x 0 + (1051193691/2000000000 : ℝ)*x 1 + (2701728749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185243723/10000000000 : ℝ)^8295 ≤ (13272821841713/100000000000000 : ℝ)^6247 := by
    have hnat : (2185243723 : ℕ)^8295*100000000000000^6247 ≤ 13272821841713^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185243723 10000000000 13272821841713 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051193691/2000000000 : ℝ)^8295 ≤ (42566925618499/100000000000000 : ℝ)^6247 := by
    have hnat : (1051193691 : ℕ)^8295*100000000000000^6247 ≤ 42566925618499^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051193691 2000000000 42566925618499 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701728749/5000000000 : ℝ)^8295 ≤ (22080126262399/50000000000000 : ℝ)^6247 := by
    have hnat : (2701728749 : ℕ)^8295*50000000000000^6247 ≤ 22080126262399^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701728749 5000000000 22080126262399 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185243723/10000000000 : ℝ), (1051193691/2000000000 : ℝ), (2701728749/5000000000 : ℝ)] ![(13272821841713/100000000000000 : ℝ), (42566925618499/100000000000000 : ℝ), (22080126262399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185243723/10000000000 : ℝ)|^8295 ≤ (13272821841713/100000000000000 : ℝ)^6247
        have hw : |(-2185243723/10000000000 : ℝ)|=(2185243723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051193691/2000000000 : ℝ)|^8295 ≤ (42566925618499/100000000000000 : ℝ)^6247
        have hw : |(1051193691/2000000000 : ℝ)|=(1051193691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701728749/5000000000 : ℝ)|^8295 ≤ (22080126262399/50000000000000 : ℝ)^6247
        have hw : |(2701728749/5000000000 : ℝ)|=(2701728749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654977623/5000000000 : ℝ)*x 0 + (-21127401/100000000 : ℝ)*x 1 + (5403457597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654977623/5000000000 : ℝ)^8295 ≤ (43148467321467/100000000000000 : ℝ)^6247 := by
    have hnat : (2654977623 : ℕ)^8295*100000000000000^6247 ≤ 43148467321467^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654977623 5000000000 43148467321467 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21127401/100000000 : ℝ)^8295 ≤ (2538255812913/20000000000000 : ℝ)^6247 := by
    have hnat : (21127401 : ℕ)^8295*20000000000000^6247 ≤ 2538255812913^6247*100000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21127401 100000000 2538255812913 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403457597/10000000000 : ℝ)^8295 ≤ (22080126799567/50000000000000 : ℝ)^6247 := by
    have hnat : (5403457597 : ℕ)^8295*50000000000000^6247 ≤ 22080126799567^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403457597 10000000000 22080126799567 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654977623/5000000000 : ℝ), (-21127401/100000000 : ℝ), (5403457597/10000000000 : ℝ)] ![(43148467321467/100000000000000 : ℝ), (2538255812913/20000000000000 : ℝ), (22080126799567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654977623/5000000000 : ℝ)|^8295 ≤ (43148467321467/100000000000000 : ℝ)^6247
        have hw : |(2654977623/5000000000 : ℝ)|=(2654977623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21127401/100000000 : ℝ)|^8295 ≤ (2538255812913/20000000000000 : ℝ)^6247
        have hw : |(-21127401/100000000 : ℝ)|=(21127401/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403457597/10000000000 : ℝ)|^8295 ≤ (22080126799567/50000000000000 : ℝ)^6247
        have hw : |(5403457597/10000000000 : ℝ)|=(5403457597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309955303/10000000000 : ℝ)*x 0 + (2161383/4000000 : ℝ)*x 1 + (-422548031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309955303/10000000000 : ℝ)^8295 ≤ (21574233968247/50000000000000 : ℝ)^6247 := by
    have hnat : (5309955303 : ℕ)^8295*50000000000000^6247 ≤ 21574233968247^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309955303 10000000000 21574233968247 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161383/4000000 : ℝ)^8295 ≤ (22080126273251/50000000000000 : ℝ)^6247 := by
    have hnat : (2161383 : ℕ)^8295*50000000000000^6247 ≤ 22080126273251^6247*4000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161383 4000000 22080126273251 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422548031/2000000000 : ℝ)^8295 ≤ (2538255900653/20000000000000 : ℝ)^6247 := by
    have hnat : (422548031 : ℕ)^8295*20000000000000^6247 ≤ 2538255900653^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422548031 2000000000 2538255900653 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309955303/10000000000 : ℝ), (2161383/4000000 : ℝ), (-422548031/2000000000 : ℝ)] ![(21574233968247/50000000000000 : ℝ), (22080126273251/50000000000000 : ℝ), (2538255900653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309955303/10000000000 : ℝ)|^8295 ≤ (21574233968247/50000000000000 : ℝ)^6247
        have hw : |(5309955303/10000000000 : ℝ)|=(5309955303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161383/4000000 : ℝ)|^8295 ≤ (22080126273251/50000000000000 : ℝ)^6247
        have hw : |(2161383/4000000 : ℝ)|=(2161383/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422548031/2000000000 : ℝ)|^8295 ≤ (2538255900653/20000000000000 : ℝ)^6247
        have hw : |(-422548031/2000000000 : ℝ)|=(422548031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s4_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369815019/10000000000 : ℝ)*x 0 + (4517826789/10000000000 : ℝ)*x 1 + (2113351137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369815019/10000000000 : ℝ)^8295 ≤ (8327860035197/25000000000000 : ℝ)^6247 := by
    have hnat : (4369815019 : ℕ)^8295*25000000000000^6247 ≤ 8327860035197^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369815019 10000000000 8327860035197 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517826789/10000000000 : ℝ)^8295 ≤ (3481790202693/10000000000000 : ℝ)^6247 := by
    have hnat : (4517826789 : ℕ)^8295*10000000000000^6247 ≤ 3481790202693^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517826789 10000000000 3481790202693 10000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113351137/5000000000 : ℝ)^8295 ≤ (31870657819579/100000000000000 : ℝ)^6247 := by
    have hnat : (2113351137 : ℕ)^8295*100000000000000^6247 ≤ 31870657819579^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113351137 5000000000 31870657819579 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369815019/10000000000 : ℝ), (4517826789/10000000000 : ℝ), (2113351137/5000000000 : ℝ)] ![(8327860035197/25000000000000 : ℝ), (3481790202693/10000000000000 : ℝ), (31870657819579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369815019/10000000000 : ℝ)|^8295 ≤ (8327860035197/25000000000000 : ℝ)^6247
        have hw : |(4369815019/10000000000 : ℝ)|=(4369815019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517826789/10000000000 : ℝ)|^8295 ≤ (3481790202693/10000000000000 : ℝ)^6247
        have hw : |(4517826789/10000000000 : ℝ)|=(4517826789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113351137/5000000000 : ℝ)|^8295 ≤ (31870657819579/100000000000000 : ℝ)^6247
        have hw : |(2113351137/5000000000 : ℝ)|=(2113351137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1857/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11097/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1857/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (657/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1857/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (657/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1857/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (657/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1857/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (657/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1857/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (657/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1857/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (657/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (657/6250 : ℝ) ^ (4147/1024 : ℝ) ≤ (10914824411893433/100000000000000000000 : ℝ) := by
    have hpowers : (657/6250 : ℝ)^4147 ≤ (10914824411893433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (657 : ℕ)^4147*100000000000000000000^1024 ≤ 10914824411893433^1024*6250^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        657 6250 10914824411893433 100000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (657/6250 : ℝ)) (X := (10914824411893433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1857/12500 : ℝ) ^ (4147/1024 : ℝ) ≤ (8859197651488381/20000000000000000000 : ℝ) := by
    have hpowers : (1857/12500 : ℝ)^4147 ≤ (8859197651488381/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1857 : ℕ)^4147*20000000000000000000^1024 ≤ 8859197651488381^1024*12500^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1857 12500 8859197651488381 20000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1857/12500 : ℝ)) (X := (8859197651488381/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010914824411893433/50000000000000000000 : ℝ) ≤ (2500134746342173/2500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50010914824411893433/50000000000000000000 : ℝ)^1024 ≤ (2500134746342173/2500000000000000 : ℝ)^4147 := by
      have hnat : (50010914824411893433 : ℕ)^1024*2500000000000000^4147 ≤ 2500134746342173^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010914824411893433 50000000000000000000 2500134746342173 2500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134746342173/2500000000000000 : ℝ)) (X := (50010914824411893433/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027605406334667669/50000000000000000000 : ℝ) ≤ (5000681506182327/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50027605406334667669/50000000000000000000 : ℝ)^1024 ≤ (5000681506182327/5000000000000000 : ℝ)^4147 := by
      have hnat : (50027605406334667669 : ℕ)^1024*5000000000000000^4147 ≤ 5000681506182327^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027605406334667669 50000000000000000000 5000681506182327 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000681506182327/5000000000000000 : ℝ)) (X := (50027605406334667669/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008859197651488381/10000000000000000000 : ℝ) ≤ (1250273379920077/1250000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10008859197651488381/10000000000000000000 : ℝ)^1024 ≤ (1250273379920077/1250000000000000 : ℝ)^4147 := by
      have hnat : (10008859197651488381 : ℕ)^1024*1250000000000000^4147 ≤ 1250273379920077^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008859197651488381 10000000000000000000 1250273379920077 1250000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250273379920077/1250000000000000 : ℝ)) (X := (10008859197651488381/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10914824411893433/100000000000000000000 : ℝ) ≤ ((90468785435163527/90500000000000000 : ℝ)+2*(412013497981/217200000000000 : ℝ)*(657/6250 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (90468785435163527/90500000000000000 : ℝ)+2*(412013497981/217200000000000 : ℝ)*(657/6250 : ℝ)=(2500134746342173/2500000000000000 : ℝ) by norm_num, show 1+2*(10914824411893433/100000000000000000000 : ℝ)=(50010914824411893433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8859197651488381/20000000000000000000 : ℝ)+(10914824411893433/100000000000000000000 : ℝ) ≤ ((90468785435163527/90500000000000000 : ℝ)+(412013497981/217200000000000 : ℝ)*((1857/12500 : ℝ)+(657/6250 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (90468785435163527/90500000000000000 : ℝ)+(412013497981/217200000000000 : ℝ)*((1857/12500 : ℝ)+(657/6250 : ℝ))=(5000681506182327/5000000000000000 : ℝ) by norm_num, show 1+(8859197651488381/20000000000000000000 : ℝ)+(10914824411893433/100000000000000000000 : ℝ)=(50027605406334667669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8859197651488381/20000000000000000000 : ℝ) ≤ ((90468785435163527/90500000000000000 : ℝ)+2*(412013497981/217200000000000 : ℝ)*(1857/12500 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (90468785435163527/90500000000000000 : ℝ)+2*(412013497981/217200000000000 : ℝ)*(1857/12500 : ℝ)=(1250273379920077/1250000000000000 : ℝ) by norm_num, show 1+2*(8859197651488381/20000000000000000000 : ℝ)=(10008859197651488381/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (90468785435163527/90500000000000000 : ℝ)*(X 1 0+X 2 0)+(412013497981/217200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (1857/12500 : ℝ)) (c := (90468785435163527/90500000000000000 : ℝ)) (alpha := (412013497981/217200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (90468785435163527/90500000000000000 : ℝ)*(X 0 1+X 2 1)+(412013497981/217200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (1857/12500 : ℝ)) (c := (90468785435163527/90500000000000000 : ℝ)) (alpha := (412013497981/217200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (90468785435163527/90500000000000000 : ℝ)*(X 0 2+X 1 2)+(412013497981/217200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (1857/12500 : ℝ)) (c := (90468785435163527/90500000000000000 : ℝ)) (alpha := (412013497981/217200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43704737/200000000 : ℝ)*X 0 0+(135097199/250000000 : ℝ)*X 0 1+(5255539213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347424831/10000000000 : ℝ)*X 1 0+(-2260657257/10000000000 : ℝ)*X 1 1+(2627770041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347424493/10000000000 : ℝ)*X 2 0+(5255540033/10000000000 : ℝ)*X 2 1+(-2260657769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184900223/5000000000 : ℝ)*X 0 0+(845170353/2000000000 : ℝ)*X 0 1+(564834161/1250000000 : ℝ)*X 0 2+(2184900223/5000000000 : ℝ)*X 1 0+(845170353/2000000000 : ℝ)*X 1 1+(564834161/1250000000 : ℝ)*X 1 2+(2184900223/5000000000 : ℝ)*X 2 0+(845170353/2000000000 : ℝ)*X 2 1+(564834161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2185243723/10000000000 : ℝ)*X 0 0+(1051193691/2000000000 : ℝ)*X 0 1+(2701728749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654977623/5000000000 : ℝ)*X 1 0+(-21127401/100000000 : ℝ)*X 1 1+(5403457597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309955303/10000000000 : ℝ)*X 2 0+(2161383/4000000 : ℝ)*X 2 1+(-422548031/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369815019/10000000000 : ℝ)*X 0 0+(4517826789/10000000000 : ℝ)*X 0 1+(2113351137/5000000000 : ℝ)*X 0 2+(4369815019/10000000000 : ℝ)*X 1 0+(4517826789/10000000000 : ℝ)*X 1 1+(2113351137/5000000000 : ℝ)*X 1 2+(4369815019/10000000000 : ℝ)*X 2 0+(4517826789/10000000000 : ℝ)*X 2 1+(2113351137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3557322142303358976103/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1189787099/50000000000000 : ℝ)*(base19) + (965844319/50000000000000 : ℝ)*(base23) + (198547317/100000000000000 : ℝ)*(upper2) + (3166461/390625000000 : ℝ)*(upper3) + (2627549/1250000000000 : ℝ)*(upper4) + (2539038776369699/50000000000000 : ℝ)*(major0) + (2539038776369699/50000000000000 : ℝ)*(major1) + (2539038776369699/50000000000000 : ℝ)*(major2) + (6740971436909867/100000000000000 : ℝ)*(sp0) + (1685257545763691/25000000000000 : ℝ)*(sp1) + (1685257657735081/25000000000000 : ℝ)*(sp2) + (853769920164407/25000000000000 : ℝ)*(sp3) + (12225143819/20000000000000 : ℝ)*(sp4) + (10713176501/25000000000000 : ℝ)*(sp7) + (213445158335227/6250000000000 : ℝ)*(f.failure) + (3370516281314481/50000000000000 : ℝ)*(f.sum) + (134194379971/30000000000000000000000000 : ℝ)*base66 + (1416801804270049/75000000000000000000000000000 : ℝ)*base67 + (1052284642770049/75000000000000000000000000000 : ℝ)*base69 + (203668034745049/75000000000000000000000000000 : ℝ)*base71 + (9192249059/30000000000000000000000000 : ℝ)*base73 + (803403767745049/75000000000000000000000000000 : ℝ)*base75 + (1573729721145049/75000000000000000000000000000 : ℝ)*base77 + (5426218245049/75000000000000000000000000000 : ℝ)*base79 + (106592288221/30000000000000000000000000 : ℝ)*base82 + (2558553/625000000000000000000 : ℝ)*base90 + (2558553/625000000000000000000 : ℝ)*base92 + (2558553/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10928343750037852183037403/2262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979728169/100000000000000 : ℝ)*(base19) + (131704331/12500000000000 : ℝ)*(base23) + (32303919/100000000000000 : ℝ)*(upper2) + (33526699/100000000000000 : ℝ)*(upper3) + (129546409/50000000000000 : ℝ)*(upper5) + (2553781488916863/50000000000000 : ℝ)*(major0) + (2553781488916863/50000000000000 : ℝ)*(major1) + (2553781488916863/50000000000000 : ℝ)*(major2) + (6543284973/20000000000000 : ℝ)*(sp1) + (24254645963/100000000000000 : ℝ)*(sp2) + (6780173642981779/100000000000000 : ℝ)*(sp4) + (3390069973414373/50000000000000 : ℝ)*(sp5) + (423759270918823/6250000000000 : ℝ)*(sp6) + (3434952151678761/100000000000000 : ℝ)*(sp7) + (3434952151678761/100000000000000 : ℝ)*(f.failure) + (6780173642981779/100000000000000 : ℝ)*(f.sum) + (7839716266819/1810000000000000000000000000 : ℝ)*base66 + (29424859397007051/4525000000000000000000000000000 : ℝ)*base67 + (1373381738457051/4525000000000000000000000000000 : ℝ)*base69 + (3078785372892949/4525000000000000000000000000000 : ℝ)*base72 + (3408111922761/1810000000000000000000000000 : ℝ)*base73 + (55486380670292949/4525000000000000000000000000000 : ℝ)*base76 + (12122184900192949/4525000000000000000000000000000 : ℝ)*base78 + (55251082489342949/4525000000000000000000000000000 : ℝ)*base80 + (14281102066669/1810000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4786221/10000000000000000000000 : ℝ)*base89 + (4786221/10000000000000000000000 : ℝ)*base91 + (4786221/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1102_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1857/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s5_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185966841/10000000000 : ℝ)*x 0 + (5395985207/10000000000 : ℝ)*x 1 + (1315740817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185966841/10000000000 : ℝ)^8295 ≤ (13278654157021/100000000000000 : ℝ)^6247 := by
    have hnat : (2185966841 : ℕ)^8295*100000000000000^6247 ≤ 13278654157021^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185966841 10000000000 13278654157021 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395985207/10000000000 : ℝ)^8295 ≤ (11019795640089/25000000000000 : ℝ)^6247 := by
    have hnat : (5395985207 : ℕ)^8295*25000000000000^6247 ≤ 11019795640089^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395985207 10000000000 11019795640089 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315740817/2500000000 : ℝ)^8295 ≤ (42642163269763/100000000000000 : ℝ)^6247 := by
    have hnat : (1315740817 : ℕ)^8295*100000000000000^6247 ≤ 42642163269763^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315740817 2500000000 42642163269763 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185966841/10000000000 : ℝ), (5395985207/10000000000 : ℝ), (1315740817/2500000000 : ℝ)] ![(13278654157021/100000000000000 : ℝ), (11019795640089/25000000000000 : ℝ), (42642163269763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185966841/10000000000 : ℝ)|^8295 ≤ (13278654157021/100000000000000 : ℝ)^6247
        have hw : |(-2185966841/10000000000 : ℝ)|=(2185966841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395985207/10000000000 : ℝ)|^8295 ≤ (11019795640089/25000000000000 : ℝ)^6247
        have hw : |(5395985207/10000000000 : ℝ)|=(5395985207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315740817/2500000000 : ℝ)|^8295 ≤ (42642163269763/100000000000000 : ℝ)^6247
        have hw : |(1315740817/2500000000 : ℝ)|=(1315740817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345450461/10000000000 : ℝ)*x 0 + (-1126740683/5000000000 : ℝ)*x 1 + (41116899/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345450461/10000000000 : ℝ)^8295 ≤ (1360371184943/3125000000000 : ℝ)^6247 := by
    have hnat : (5345450461 : ℕ)^8295*3125000000000^6247 ≤ 1360371184943^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345450461 10000000000 1360371184943 3125000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126740683/5000000000 : ℝ)^8295 ≤ (13825960901223/100000000000000 : ℝ)^6247 := by
    have hnat : (1126740683 : ℕ)^8295*100000000000000^6247 ≤ 13825960901223^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126740683 5000000000 13825960901223 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41116899/78125000 : ℝ)^8295 ≤ (42642161161087/100000000000000 : ℝ)^6247 := by
    have hnat : (41116899 : ℕ)^8295*100000000000000^6247 ≤ 42642161161087^6247*78125000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41116899 78125000 42642161161087 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345450461/10000000000 : ℝ), (-1126740683/5000000000 : ℝ), (41116899/78125000 : ℝ)] ![(1360371184943/3125000000000 : ℝ), (13825960901223/100000000000000 : ℝ), (42642161161087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345450461/10000000000 : ℝ)|^8295 ≤ (1360371184943/3125000000000 : ℝ)^6247
        have hw : |(5345450461/10000000000 : ℝ)|=(5345450461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126740683/5000000000 : ℝ)|^8295 ≤ (13825960901223/100000000000000 : ℝ)^6247
        have hw : |(-1126740683/5000000000 : ℝ)|=(1126740683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41116899/78125000 : ℝ)|^8295 ≤ (42642161161087/100000000000000 : ℝ)^6247
        have hw : |(41116899/78125000 : ℝ)|=(41116899/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345450253/10000000000 : ℝ)*x 0 + (5262963111/10000000000 : ℝ)*x 1 + (-2253481591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345450253/10000000000 : ℝ)^8295 ≤ (43531875668959/100000000000000 : ℝ)^6247 := by
    have hnat : (5345450253 : ℕ)^8295*100000000000000^6247 ≤ 43531875668959^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345450253 10000000000 43531875668959 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262963111/10000000000 : ℝ)^8295 ≤ (4264216158067/10000000000000 : ℝ)^6247 := by
    have hnat : (5262963111 : ℕ)^8295*10000000000000^6247 ≤ 4264216158067^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262963111 10000000000 4264216158067 10000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253481591/10000000000 : ℝ)^8295 ≤ (55303850937/400000000000 : ℝ)^6247 := by
    have hnat : (2253481591 : ℕ)^8295*400000000000^6247 ≤ 55303850937^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253481591 10000000000 55303850937 400000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345450253/10000000000 : ℝ), (5262963111/10000000000 : ℝ), (-2253481591/10000000000 : ℝ)] ![(43531875668959/100000000000000 : ℝ), (4264216158067/10000000000000 : ℝ), (55303850937/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345450253/10000000000 : ℝ)|^8295 ≤ (43531875668959/100000000000000 : ℝ)^6247
        have hw : |(5345450253/10000000000 : ℝ)|=(5345450253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262963111/10000000000 : ℝ)|^8295 ≤ (4264216158067/10000000000000 : ℝ)^6247
        have hw : |(5262963111/10000000000 : ℝ)|=(5262963111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253481591/10000000000 : ℝ)|^8295 ≤ (55303850937/400000000000 : ℝ)^6247
        have hw : |(-2253481591/10000000000 : ℝ)|=(2253481591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273139149/625000000 : ℝ)*x 0 + (265057637/625000000 : ℝ)*x 1 + (4503491993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273139149/625000000 : ℝ)^8295 ≤ (33315604126969/100000000000000 : ℝ)^6247 := by
    have hnat : (273139149 : ℕ)^8295*100000000000000^6247 ≤ 33315604126969^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273139149 625000000 33315604126969 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265057637/625000000 : ℝ)^8295 ≤ (32013110492229/100000000000000 : ℝ)^6247 := by
    have hnat : (265057637 : ℕ)^8295*100000000000000^6247 ≤ 32013110492229^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265057637 625000000 32013110492229 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503491993/10000000000 : ℝ)^8295 ≤ (6934257073117/20000000000000 : ℝ)^6247 := by
    have hnat : (4503491993 : ℕ)^8295*20000000000000^6247 ≤ 6934257073117^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503491993 10000000000 6934257073117 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273139149/625000000 : ℝ), (265057637/625000000 : ℝ), (4503491993/10000000000 : ℝ)] ![(33315604126969/100000000000000 : ℝ), (32013110492229/100000000000000 : ℝ), (6934257073117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273139149/625000000 : ℝ)|^8295 ≤ (33315604126969/100000000000000 : ℝ)^6247
        have hw : |(273139149/625000000 : ℝ)|=(273139149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265057637/625000000 : ℝ)|^8295 ≤ (32013110492229/100000000000000 : ℝ)^6247
        have hw : |(265057637/625000000 : ℝ)|=(265057637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503491993/10000000000 : ℝ)|^8295 ≤ (6934257073117/20000000000000 : ℝ)^6247
        have hw : |(4503491993/10000000000 : ℝ)|=(4503491993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185972271/10000000000 : ℝ)*x 0 + (1052661637/2000000000 : ℝ)*x 1 + (1079127811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185972271/10000000000 : ℝ)^8295 ≤ (3319674488783/25000000000000 : ℝ)^6247 := by
    have hnat : (2185972271 : ℕ)^8295*25000000000000^6247 ≤ 3319674488783^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185972271 10000000000 3319674488783 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052661637/2000000000 : ℝ)^8295 ≤ (42645874116687/100000000000000 : ℝ)^6247 := by
    have hnat : (1052661637 : ℕ)^8295*100000000000000^6247 ≤ 42645874116687^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052661637 2000000000 42645874116687 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079127811/2000000000 : ℝ)^8295 ≤ (44075427906161/100000000000000 : ℝ)^6247 := by
    have hnat : (1079127811 : ℕ)^8295*100000000000000^6247 ≤ 44075427906161^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079127811 2000000000 44075427906161 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185972271/10000000000 : ℝ), (1052661637/2000000000 : ℝ), (1079127811/2000000000 : ℝ)] ![(3319674488783/25000000000000 : ℝ), (42645874116687/100000000000000 : ℝ), (44075427906161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185972271/10000000000 : ℝ)|^8295 ≤ (3319674488783/25000000000000 : ℝ)^6247
        have hw : |(-2185972271/10000000000 : ℝ)|=(2185972271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052661637/2000000000 : ℝ)|^8295 ≤ (42645874116687/100000000000000 : ℝ)^6247
        have hw : |(1052661637/2000000000 : ℝ)|=(1052661637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079127811/2000000000 : ℝ)|^8295 ≤ (44075427906161/100000000000000 : ℝ)^6247
        have hw : |(1079127811/2000000000 : ℝ)|=(1079127811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82997667/156250000 : ℝ)*x 0 + (-265100693/1250000000 : ℝ)*x 1 + (674454879/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82997667/156250000 : ℝ)^8295 ≤ (21584460120411/50000000000000 : ℝ)^6247 := by
    have hnat : (82997667 : ℕ)^8295*50000000000000^6247 ≤ 21584460120411^6247*156250000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82997667 156250000 21584460120411 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265100693/1250000000 : ℝ)^8295 ≤ (6377826045829/50000000000000 : ℝ)^6247 := by
    have hnat : (265100693 : ℕ)^8295*50000000000000^6247 ≤ 6377826045829^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265100693 1250000000 6377826045829 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674454879/1250000000 : ℝ)^8295 ≤ (44075427656687/100000000000000 : ℝ)^6247 := by
    have hnat : (674454879 : ℕ)^8295*100000000000000^6247 ≤ 44075427656687^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674454879 1250000000 44075427656687 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82997667/156250000 : ℝ), (-265100693/1250000000 : ℝ), (674454879/1250000000 : ℝ)] ![(21584460120411/50000000000000 : ℝ), (6377826045829/50000000000000 : ℝ), (44075427656687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82997667/156250000 : ℝ)|^8295 ≤ (21584460120411/50000000000000 : ℝ)^6247
        have hw : |(82997667/156250000 : ℝ)|=(82997667/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265100693/1250000000 : ℝ)|^8295 ≤ (6377826045829/50000000000000 : ℝ)^6247
        have hw : |(-265100693/1250000000 : ℝ)|=(265100693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674454879/1250000000 : ℝ)|^8295 ≤ (44075427656687/100000000000000 : ℝ)^6247
        have hw : |(674454879/1250000000 : ℝ)|=(674454879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311850587/10000000000 : ℝ)*x 0 + (5395639163/10000000000 : ℝ)*x 1 + (-1060402751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311850587/10000000000 : ℝ)^8295 ≤ (43168919150909/100000000000000 : ℝ)^6247 := by
    have hnat : (5311850587 : ℕ)^8295*100000000000000^6247 ≤ 43168919150909^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311850587 10000000000 43168919150909 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395639163/10000000000 : ℝ)^8295 ≤ (5509428634701/12500000000000 : ℝ)^6247 := by
    have hnat : (5395639163 : ℕ)^8295*12500000000000^6247 ≤ 5509428634701^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395639163 10000000000 5509428634701 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060402751/5000000000 : ℝ)^8295 ≤ (1594456469529/12500000000000 : ℝ)^6247 := by
    have hnat : (1060402751 : ℕ)^8295*12500000000000^6247 ≤ 1594456469529^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060402751 5000000000 1594456469529 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311850587/10000000000 : ℝ), (5395639163/10000000000 : ℝ), (-1060402751/5000000000 : ℝ)] ![(43168919150909/100000000000000 : ℝ), (5509428634701/12500000000000 : ℝ), (1594456469529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311850587/10000000000 : ℝ)|^8295 ≤ (43168919150909/100000000000000 : ℝ)^6247
        have hw : |(5311850587/10000000000 : ℝ)|=(5311850587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395639163/10000000000 : ℝ)|^8295 ≤ (5509428634701/12500000000000 : ℝ)^6247
        have hw : |(5395639163/10000000000 : ℝ)|=(5395639163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1060402751/5000000000 : ℝ)|^8295 ≤ (1594456469529/12500000000000 : ℝ)^6247
        have hw : |(-1060402751/5000000000 : ℝ)|=(1060402751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s5_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370237001/10000000000 : ℝ)*x 0 + (900562223/2000000000 : ℝ)*x 1 + (2120802927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370237001/10000000000 : ℝ)^8295 ≤ (33315711597807/100000000000000 : ℝ)^6247 := by
    have hnat : (4370237001 : ℕ)^8295*100000000000000^6247 ≤ 33315711597807^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370237001 10000000000 33315711597807 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900562223/2000000000 : ℝ)^8295 ≤ (17332162564753/50000000000000 : ℝ)^6247 := by
    have hnat : (900562223 : ℕ)^8295*50000000000000^6247 ≤ 17332162564753^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900562223 2000000000 17332162564753 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120802927/5000000000 : ℝ)^8295 ≤ (4002495406229/12500000000000 : ℝ)^6247 := by
    have hnat : (2120802927 : ℕ)^8295*12500000000000^6247 ≤ 4002495406229^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120802927 5000000000 4002495406229 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370237001/10000000000 : ℝ), (900562223/2000000000 : ℝ), (2120802927/5000000000 : ℝ)] ![(33315711597807/100000000000000 : ℝ), (17332162564753/50000000000000 : ℝ), (4002495406229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370237001/10000000000 : ℝ)|^8295 ≤ (33315711597807/100000000000000 : ℝ)^6247
        have hw : |(4370237001/10000000000 : ℝ)|=(4370237001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900562223/2000000000 : ℝ)|^8295 ≤ (17332162564753/50000000000000 : ℝ)^6247
        have hw : |(900562223/2000000000 : ℝ)|=(900562223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120802927/5000000000 : ℝ)|^8295 ≤ (4002495406229/12500000000000 : ℝ)^6247
        have hw : |(2120802927/5000000000 : ℝ)|=(2120802927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2251/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11097/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (2718310748586591/20000000000000000000 : ℝ) := by
    have hpowers : (11097/100000 : ℝ)^4147 ≤ (2718310748586591/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11097 : ℕ)^4147*20000000000000000000^1024 ≤ 2718310748586591^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11097 100000 2718310748586591 20000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11097/100000 : ℝ)) (X := (2718310748586591/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4147/1024 : ℝ) ≤ (1491742067644339/4000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4147 ≤ (1491742067644339/4000000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4147*4000000000000000000^1024 ≤ 1491742067644339^1024*50000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 1491742067644339 4000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (1491742067644339/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002718310748586591/10000000000000000000 : ℝ) ≤ (2500167787879361/2500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10002718310748586591/10000000000000000000 : ℝ)^1024 ≤ (2500167787879361/2500000000000000 : ℝ)^4147 := by
      have hnat : (10002718310748586591 : ℕ)^1024*2500000000000000^4147 ≤ 2500167787879361^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002718310748586591 10000000000000000000 2500167787879361 2500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167787879361/2500000000000000 : ℝ)) (X := (10002718310748586591/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005088510543404143/10000000000000000000 : ℝ) ≤ (312539257571199/312500000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10005088510543404143/10000000000000000000 : ℝ)^1024 ≤ (312539257571199/312500000000000 : ℝ)^4147 := by
      have hnat : (10005088510543404143 : ℕ)^1024*312500000000000^4147 ≤ 312539257571199^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005088510543404143 10000000000000000000 312539257571199 312500000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312539257571199/312500000000000 : ℝ)) (X := (10005088510543404143/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001491742067644339/2000000000000000000 : ℝ) ≤ (2500460333259823/2500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (2001491742067644339/2000000000000000000 : ℝ)^1024 ≤ (2500460333259823/2500000000000000 : ℝ)^4147 := by
      have hnat : (2001491742067644339 : ℕ)^1024*2500000000000000^4147 ≤ 2500460333259823^4147*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001491742067644339 2000000000000000000 2500460333259823 2500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500460333259823/2500000000000000 : ℝ)) (X := (2001491742067644339/2000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2718310748586591/20000000000000000000 : ℝ) ≤ ((872197849515787343/872500000000000000 : ℝ)+2*(146272690231/78525000000000 : ℝ)*(11097/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (872197849515787343/872500000000000000 : ℝ)+2*(146272690231/78525000000000 : ℝ)*(11097/100000 : ℝ)=(2500167787879361/2500000000000000 : ℝ) by norm_num, show 1+2*(2718310748586591/20000000000000000000 : ℝ)=(10002718310748586591/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1491742067644339/4000000000000000000 : ℝ)+(2718310748586591/20000000000000000000 : ℝ) ≤ ((872197849515787343/872500000000000000 : ℝ)+(146272690231/78525000000000 : ℝ)*((7119/50000 : ℝ)+(11097/100000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (872197849515787343/872500000000000000 : ℝ)+(146272690231/78525000000000 : ℝ)*((7119/50000 : ℝ)+(11097/100000 : ℝ))=(312539257571199/312500000000000 : ℝ) by norm_num, show 1+(1491742067644339/4000000000000000000 : ℝ)+(2718310748586591/20000000000000000000 : ℝ)=(10005088510543404143/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1491742067644339/4000000000000000000 : ℝ) ≤ ((872197849515787343/872500000000000000 : ℝ)+2*(146272690231/78525000000000 : ℝ)*(7119/50000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (872197849515787343/872500000000000000 : ℝ)+2*(146272690231/78525000000000 : ℝ)*(7119/50000 : ℝ)=(2500460333259823/2500000000000000 : ℝ) by norm_num, show 1+2*(1491742067644339/4000000000000000000 : ℝ)=(2001491742067644339/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (872197849515787343/872500000000000000 : ℝ)*(X 1 0+X 2 0)+(146272690231/78525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (872197849515787343/872500000000000000 : ℝ)) (alpha := (146272690231/78525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (872197849515787343/872500000000000000 : ℝ)*(X 0 1+X 2 1)+(146272690231/78525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (872197849515787343/872500000000000000 : ℝ)) (alpha := (146272690231/78525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (872197849515787343/872500000000000000 : ℝ)*(X 0 2+X 1 2)+(146272690231/78525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (872197849515787343/872500000000000000 : ℝ)) (alpha := (146272690231/78525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185966841/10000000000 : ℝ)*X 0 0+(5395985207/10000000000 : ℝ)*X 0 1+(1315740817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345450461/10000000000 : ℝ)*X 1 0+(-1126740683/5000000000 : ℝ)*X 1 1+(41116899/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345450253/10000000000 : ℝ)*X 2 0+(5262963111/10000000000 : ℝ)*X 2 1+(-2253481591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273139149/625000000 : ℝ)*X 0 0+(265057637/625000000 : ℝ)*X 0 1+(4503491993/10000000000 : ℝ)*X 0 2+(273139149/625000000 : ℝ)*X 1 0+(265057637/625000000 : ℝ)*X 1 1+(4503491993/10000000000 : ℝ)*X 1 2+(273139149/625000000 : ℝ)*X 2 0+(265057637/625000000 : ℝ)*X 2 1+(4503491993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2185972271/10000000000 : ℝ)*X 0 0+(1052661637/2000000000 : ℝ)*X 0 1+(1079127811/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82997667/156250000 : ℝ)*X 1 0+(-265100693/1250000000 : ℝ)*X 1 1+(674454879/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311850587/10000000000 : ℝ)*X 2 0+(5395639163/10000000000 : ℝ)*X 2 1+(-1060402751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370237001/10000000000 : ℝ)*X 0 0+(900562223/2000000000 : ℝ)*X 0 1+(2120802927/5000000000 : ℝ)*X 0 2+(4370237001/10000000000 : ℝ)*X 1 0+(900562223/2000000000 : ℝ)*X 1 1+(2120802927/5000000000 : ℝ)*X 1 2+(4370237001/10000000000 : ℝ)*X 2 0+(900562223/2000000000 : ℝ)*X 2 1+(2120802927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (257341990967771852954920909/32718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1321084797/100000000000000 : ℝ)*(base19) + (324952151/25000000000000 : ℝ)*(base23) + (434819/20000000000000 : ℝ)*(lower2) + (199144947/100000000000000 : ℝ)*(upper3) + (18395923/12500000000000 : ℝ)*(lower4) + (2831542101835343/50000000000000 : ℝ)*(major0) + (2831542101835343/50000000000000 : ℝ)*(major1) + (2831542101835343/50000000000000 : ℝ)*(major2) + (3758797147417931/50000000000000 : ℝ)*(sp0) + (1879403506503203/25000000000000 : ℝ)*(sp1) + (1503522809457801/20000000000000 : ℝ)*(sp2) + (1904265705199611/50000000000000 : ℝ)*(sp3) + (10526130873/50000000000000 : ℝ)*(sp4) + (334182323/1562500000000 : ℝ)*(sp7) + (1904276399033947/50000000000000 : ℝ)*(f.failure) + (7517615347097609/100000000000000 : ℝ)*(f.sum) + (21554880295351/3926250000000000000000000000 : ℝ)*base65 + (1363466031694972841/392625000000000000000000000000000 : ℝ)*base67 + (575218719880972841/392625000000000000000000000000000 : ℝ)*base69 + (4124678336386972841/392625000000000000000000000000000 : ℝ)*base71 + (3172102730119/981562500000000000000000000 : ℝ)*base73 + (434002729388722841/392625000000000000000000000000000 : ℝ)*base75 + (2615403519942847841/392625000000000000000000000000000 : ℝ)*base77 + (4345933638136402159/392625000000000000000000000000000 : ℝ)*base80 + (46122778381669/15705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (50500633/5000000000000000000000 : ℝ)*base90 + (50500633/5000000000000000000000 : ℝ)*base92 + (50500633/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (793359636153063341684481967/65437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767775119/50000000000000 : ℝ)*(base19) + (1743757171/100000000000000 : ℝ)*(base23) + (168329401/100000000000000 : ℝ)*(upper3) + (142115447/100000000000000 : ℝ)*(lower4) + (53053009/100000000000000 : ℝ)*(upper5) + (2846303355748253/50000000000000 : ℝ)*(major0) + (2846303355748253/50000000000000 : ℝ)*(major1) + (2846303355748253/50000000000000 : ℝ)*(major2) + (9823043737/25000000000000 : ℝ)*(sp1) + (52627161213/100000000000000 : ℝ)*(sp2) + (7556805663499513/100000000000000 : ℝ)*(sp4) + (7556764835774327/100000000000000 : ℝ)*(sp5) + (7556751292581129/100000000000000 : ℝ)*(sp6) + (382840735536251/10000000000000 : ℝ)*(sp7) + (382840735536251/10000000000000 : ℝ)*(f.failure) + (7556805663499513/100000000000000 : ℝ)*(f.sum) + (66596068943209/15705000000000000000000000000 : ℝ)*base65 + (884414349463281011/392625000000000000000000000000000 : ℝ)*base67 + (3989606478313281011/392625000000000000000000000000000 : ℝ)*base69 + (6348867818310906011/392625000000000000000000000000000 : ℝ)*base71 + (9838044405887/7852500000000000000000000000 : ℝ)*base73 + (740253166162656011/392625000000000000000000000000000 : ℝ)*base75 + (789505278219906011/392625000000000000000000000000000 : ℝ)*base77 + (5148418134855156011/392625000000000000000000000000000 : ℝ)*base79 + (23371647642251/15705000000000000000000000000 : ℝ)*base82 + (6655111/1000000000000000000000 : ℝ)*base89 + (6655111/1000000000000000000000 : ℝ)*base91 + (6655111/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1102_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1102_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1102_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1102_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1102_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

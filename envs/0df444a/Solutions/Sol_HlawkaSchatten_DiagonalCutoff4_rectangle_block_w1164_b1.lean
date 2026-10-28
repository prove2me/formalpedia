-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:44.412723+00:00
-- url     : https://prove2.me/submissions/74281724-8f6d-4076-9643-da3a175849f2

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
theorem support_rectangle_w1164_s3_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152840253/10000000000 : ℝ)*x 0 + (2713474657/5000000000 : ℝ)*x 1 + (5234111479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152840253/10000000000 : ℝ)^8357 ≤ (13076665451173/100000000000000 : ℝ)^6309 := by
    have hnat : (2152840253 : ℕ)^8357*100000000000000^6309 ≤ 13076665451173^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152840253 10000000000 13076665451173 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713474657/5000000000 : ℝ)^8357 ≤ (22251455430951/50000000000000 : ℝ)^6309 := by
    have hnat : (2713474657 : ℕ)^8357*50000000000000^6309 ≤ 22251455430951^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713474657 5000000000 22251455430951 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234111479/10000000000 : ℝ)^8357 ≤ (10605105917697/25000000000000 : ℝ)^6309 := by
    have hnat : (5234111479 : ℕ)^8357*25000000000000^6309 ≤ 10605105917697^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234111479 10000000000 10605105917697 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152840253/10000000000 : ℝ), (2713474657/5000000000 : ℝ), (5234111479/10000000000 : ℝ)] ![(13076665451173/100000000000000 : ℝ), (22251455430951/50000000000000 : ℝ), (10605105917697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152840253/10000000000 : ℝ)|^8357 ≤ (13076665451173/100000000000000 : ℝ)^6309
        have hw : |(-2152840253/10000000000 : ℝ)|=(2152840253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713474657/5000000000 : ℝ)|^8357 ≤ (22251455430951/50000000000000 : ℝ)^6309
        have hw : |(2713474657/5000000000 : ℝ)|=(2713474657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234111479/10000000000 : ℝ)|^8357 ≤ (10605105917697/25000000000000 : ℝ)^6309
        have hw : |(5234111479/10000000000 : ℝ)|=(5234111479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676635249/5000000000 : ℝ)*x 0 + (-2251365729/10000000000 : ℝ)*x 1 + (1046822257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676635249/5000000000 : ℝ)^8357 ≤ (21852178545653/50000000000000 : ℝ)^6309 := by
    have hnat : (2676635249 : ℕ)^8357*50000000000000^6309 ≤ 21852178545653^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676635249 5000000000 21852178545653 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251365729/10000000000 : ℝ)^8357 ≤ (3468805325961/25000000000000 : ℝ)^6309 := by
    have hnat : (2251365729 : ℕ)^8357*25000000000000^6309 ≤ 3468805325961^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251365729 10000000000 3468805325961 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046822257/2000000000 : ℝ)^8357 ≤ (42420421588103/100000000000000 : ℝ)^6309 := by
    have hnat : (1046822257 : ℕ)^8357*100000000000000^6309 ≤ 42420421588103^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046822257 2000000000 42420421588103 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676635249/5000000000 : ℝ), (-2251365729/10000000000 : ℝ), (1046822257/2000000000 : ℝ)] ![(21852178545653/50000000000000 : ℝ), (3468805325961/25000000000000 : ℝ), (42420421588103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676635249/5000000000 : ℝ)|^8357 ≤ (21852178545653/50000000000000 : ℝ)^6309
        have hw : |(2676635249/5000000000 : ℝ)|=(2676635249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251365729/10000000000 : ℝ)|^8357 ≤ (3468805325961/25000000000000 : ℝ)^6309
        have hw : |(-2251365729/10000000000 : ℝ)|=(2251365729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046822257/2000000000 : ℝ)|^8357 ≤ (42420421588103/100000000000000 : ℝ)^6309
        have hw : |(1046822257/2000000000 : ℝ)|=(1046822257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267663529/500000000 : ℝ)*x 0 + (2617055651/5000000000 : ℝ)*x 1 + (-1125682799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267663529/500000000 : ℝ)^8357 ≤ (43704357978073/100000000000000 : ℝ)^6309 := by
    have hnat : (267663529 : ℕ)^8357*100000000000000^6309 ≤ 43704357978073^6309*500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267663529 500000000 43704357978073 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617055651/5000000000 : ℝ)^8357 ≤ (21210210885303/50000000000000 : ℝ)^6309 := by
    have hnat : (2617055651 : ℕ)^8357*50000000000000^6309 ≤ 21210210885303^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617055651 5000000000 21210210885303 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125682799/5000000000 : ℝ)^8357 ≤ (13875220234407/100000000000000 : ℝ)^6309 := by
    have hnat : (1125682799 : ℕ)^8357*100000000000000^6309 ≤ 13875220234407^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125682799 5000000000 13875220234407 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267663529/500000000 : ℝ), (2617055651/5000000000 : ℝ), (-1125682799/5000000000 : ℝ)] ![(43704357978073/100000000000000 : ℝ), (21210210885303/50000000000000 : ℝ), (13875220234407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267663529/500000000 : ℝ)|^8357 ≤ (43704357978073/100000000000000 : ℝ)^6309
        have hw : |(267663529/500000000 : ℝ)|=(267663529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617055651/5000000000 : ℝ)|^8357 ≤ (21210210885303/50000000000000 : ℝ)^6309
        have hw : |(2617055651/5000000000 : ℝ)|=(2617055651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125682799/5000000000 : ℝ)|^8357 ≤ (13875220234407/100000000000000 : ℝ)^6309
        have hw : |(-1125682799/5000000000 : ℝ)|=(1125682799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359462263/10000000000 : ℝ)*x 0 + (4171019851/10000000000 : ℝ)*x 1 + (4556321923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359462263/10000000000 : ℝ)^8357 ≤ (8323907067159/25000000000000 : ℝ)^6309 := by
    have hnat : (4359462263 : ℕ)^8357*25000000000000^6309 ≤ 8323907067159^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359462263 10000000000 8323907067159 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171019851/10000000000 : ℝ)^8357 ≤ (15701348844209/50000000000000 : ℝ)^6309 := by
    have hnat : (4171019851 : ℕ)^8357*50000000000000^6309 ≤ 15701348844209^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171019851 10000000000 15701348844209 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556321923/10000000000 : ℝ)^8357 ≤ (8825418508801/25000000000000 : ℝ)^6309 := by
    have hnat : (4556321923 : ℕ)^8357*25000000000000^6309 ≤ 8825418508801^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556321923 10000000000 8825418508801 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359462263/10000000000 : ℝ), (4171019851/10000000000 : ℝ), (4556321923/10000000000 : ℝ)] ![(8323907067159/25000000000000 : ℝ), (15701348844209/50000000000000 : ℝ), (8825418508801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359462263/10000000000 : ℝ)|^8357 ≤ (8323907067159/25000000000000 : ℝ)^6309
        have hw : |(4359462263/10000000000 : ℝ)|=(4359462263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171019851/10000000000 : ℝ)|^8357 ≤ (15701348844209/50000000000000 : ℝ)^6309
        have hw : |(4171019851/10000000000 : ℝ)|=(4171019851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556321923/10000000000 : ℝ)|^8357 ≤ (8825418508801/25000000000000 : ℝ)^6309
        have hw : |(4556321923/10000000000 : ℝ)|=(4556321923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076428657/5000000000 : ℝ)*x 0 + (1046969707/2000000000 : ℝ)*x 1 + (2713104097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076428657/5000000000 : ℝ)^8357 ≤ (408650085081/3125000000000 : ℝ)^6309 := by
    have hnat : (1076428657 : ℕ)^8357*3125000000000^6309 ≤ 408650085081^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076428657 5000000000 408650085081 3125000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046969707/2000000000 : ℝ)^8357 ≤ (8485667301923/20000000000000 : ℝ)^6309 := by
    have hnat : (1046969707 : ℕ)^8357*20000000000000^6309 ≤ 8485667301923^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046969707 2000000000 8485667301923 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713104097/5000000000 : ℝ)^8357 ≤ (5561857594869/12500000000000 : ℝ)^6309 := by
    have hnat : (2713104097 : ℕ)^8357*12500000000000^6309 ≤ 5561857594869^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713104097 5000000000 5561857594869 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076428657/5000000000 : ℝ), (1046969707/2000000000 : ℝ), (2713104097/5000000000 : ℝ)] ![(408650085081/3125000000000 : ℝ), (8485667301923/20000000000000 : ℝ), (5561857594869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076428657/5000000000 : ℝ)|^8357 ≤ (408650085081/3125000000000 : ℝ)^6309
        have hw : |(-1076428657/5000000000 : ℝ)|=(1076428657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046969707/2000000000 : ℝ)|^8357 ≤ (8485667301923/20000000000000 : ℝ)^6309
        have hw : |(1046969707/2000000000 : ℝ)|=(1046969707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713104097/5000000000 : ℝ)|^8357 ≤ (5561857594869/12500000000000 : ℝ)^6309
        have hw : |(2713104097/5000000000 : ℝ)|=(2713104097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663042253/1250000000 : ℝ)*x 0 + (-411853761/2000000000 : ℝ)*x 1 + (2713104097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663042253/1250000000 : ℝ)^8357 ≤ (10793994244229/25000000000000 : ℝ)^6309 := by
    have hnat : (663042253 : ℕ)^8357*25000000000000^6309 ≤ 10793994244229^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663042253 1250000000 10793994244229 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411853761/2000000000 : ℝ)^8357 ≤ (12329162252647/100000000000000 : ℝ)^6309 := by
    have hnat : (411853761 : ℕ)^8357*100000000000000^6309 ≤ 12329162252647^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411853761 2000000000 12329162252647 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713104097/5000000000 : ℝ)^8357 ≤ (5561857594869/12500000000000 : ℝ)^6309 := by
    have hnat : (2713104097 : ℕ)^8357*12500000000000^6309 ≤ 5561857594869^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713104097 5000000000 5561857594869 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663042253/1250000000 : ℝ), (-411853761/2000000000 : ℝ), (2713104097/5000000000 : ℝ)] ![(10793994244229/25000000000000 : ℝ), (12329162252647/100000000000000 : ℝ), (5561857594869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663042253/1250000000 : ℝ)|^8357 ≤ (10793994244229/25000000000000 : ℝ)^6309
        have hw : |(663042253/1250000000 : ℝ)|=(663042253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411853761/2000000000 : ℝ)|^8357 ≤ (12329162252647/100000000000000 : ℝ)^6309
        have hw : |(-411853761/2000000000 : ℝ)|=(411853761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713104097/5000000000 : ℝ)|^8357 ≤ (5561857594869/12500000000000 : ℝ)^6309
        have hw : |(2713104097/5000000000 : ℝ)|=(2713104097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060867581/2000000000 : ℝ)*x 0 + (678276051/1250000000 : ℝ)*x 1 + (-2059268673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060867581/2000000000 : ℝ)^8357 ≤ (21587987846927/50000000000000 : ℝ)^6309 := by
    have hnat : (1060867581 : ℕ)^8357*50000000000000^6309 ≤ 21587987846927^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060867581 2000000000 21587987846927 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678276051/1250000000 : ℝ)^8357 ≤ (8898972616677/20000000000000 : ℝ)^6309 := by
    have hnat : (678276051 : ℕ)^8357*20000000000000^6309 ≤ 8898972616677^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678276051 1250000000 8898972616677 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059268673/10000000000 : ℝ)^8357 ≤ (12329161205797/100000000000000 : ℝ)^6309 := by
    have hnat : (2059268673 : ℕ)^8357*100000000000000^6309 ≤ 12329161205797^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059268673 10000000000 12329161205797 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060867581/2000000000 : ℝ), (678276051/1250000000 : ℝ), (-2059268673/10000000000 : ℝ)] ![(21587987846927/50000000000000 : ℝ), (8898972616677/20000000000000 : ℝ), (12329161205797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060867581/2000000000 : ℝ)|^8357 ≤ (21587987846927/50000000000000 : ℝ)^6309
        have hw : |(1060867581/2000000000 : ℝ)|=(1060867581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678276051/1250000000 : ℝ)|^8357 ≤ (8898972616677/20000000000000 : ℝ)^6309
        have hw : |(678276051/1250000000 : ℝ)|=(678276051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059268673/10000000000 : ℝ)|^8357 ≤ (12329161205797/100000000000000 : ℝ)^6309
        have hw : |(-2059268673/10000000000 : ℝ)|=(2059268673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s3_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359496369/10000000000 : ℝ)*x 0 + (910969841/2000000000 : ℝ)*x 1 + (834500131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359496369/10000000000 : ℝ)^8357 ≤ (33295973313451/100000000000000 : ℝ)^6309 := by
    have hnat : (4359496369 : ℕ)^8357*100000000000000^6309 ≤ 33295973313451^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359496369 10000000000 33295973313451 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910969841/2000000000 : ℝ)^8357 ≤ (1411462417883/4000000000000 : ℝ)^6309 := by
    have hnat : (910969841 : ℕ)^8357*4000000000000^6309 ≤ 1411462417883^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910969841 2000000000 1411462417883 4000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834500131/2000000000 : ℝ)^8357 ≤ (245448954807/781250000000 : ℝ)^6309 := by
    have hnat : (834500131 : ℕ)^8357*781250000000^6309 ≤ 245448954807^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834500131 2000000000 245448954807 781250000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359496369/10000000000 : ℝ), (910969841/2000000000 : ℝ), (834500131/2000000000 : ℝ)] ![(33295973313451/100000000000000 : ℝ), (1411462417883/4000000000000 : ℝ), (245448954807/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359496369/10000000000 : ℝ)|^8357 ≤ (33295973313451/100000000000000 : ℝ)^6309
        have hw : |(4359496369/10000000000 : ℝ)|=(4359496369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(910969841/2000000000 : ℝ)|^8357 ≤ (1411462417883/4000000000000 : ℝ)^6309
        have hw : |(910969841/2000000000 : ℝ)|=(910969841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834500131/2000000000 : ℝ)|^8357 ≤ (245448954807/781250000000 : ℝ)^6309
        have hw : |(834500131/2000000000 : ℝ)|=(834500131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10699/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (739/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8219/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8219/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8219/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8219/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8219/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8219/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9169/100000 : ℝ) ^ (2089/512 : ℝ) ≤ (2918519399839617/50000000000000000000 : ℝ) := by
    have hpowers : (9169/100000 : ℝ)^2089 ≤ (2918519399839617/50000000000000000000 : ℝ)^512 := by
      have hnat : (9169 : ℕ)^2089*50000000000000000000^512 ≤ 2918519399839617^512*100000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9169 100000 2918519399839617 50000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9169/100000 : ℝ)) (X := (2918519399839617/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8219/50000 : ℝ) ^ (2089/512 : ℝ) ≤ (63183337216793891/100000000000000000000 : ℝ) := by
    have hpowers : (8219/50000 : ℝ)^2089 ≤ (63183337216793891/100000000000000000000 : ℝ)^512 := by
      have hnat : (8219 : ℕ)^2089*100000000000000000000^512 ≤ 63183337216793891^512*50000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8219 50000 63183337216793891 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8219/50000 : ℝ)) (X := (63183337216793891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002918519399839617/25000000000000000000 : ℝ) ≤ (2500071527816797/2500000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (25002918519399839617/25000000000000000000 : ℝ)^512 ≤ (2500071527816797/2500000000000000 : ℝ)^2089 := by
      have hnat : (25002918519399839617 : ℕ)^512*2500000000000000^2089 ≤ 2500071527816797^2089*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002918519399839617 25000000000000000000 2500071527816797 2500000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071527816797/2500000000000000 : ℝ)) (X := (25002918519399839617/25000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (160110432601626357/160000000000000000 : ℝ) ≤ (1250211400370259/1250000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (160110432601626357/160000000000000000 : ℝ)^512 ≤ (1250211400370259/1250000000000000 : ℝ)^2089 := by
      have hnat : (160110432601626357 : ℕ)^512*1250000000000000^2089 ≤ 1250211400370259^2089*160000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160110432601626357 160000000000000000 1250211400370259 1250000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250211400370259/1250000000000000 : ℝ)) (X := (160110432601626357/160000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063183337216793891/50000000000000000000 : ℝ) ≤ (2500774073664239/2500000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50063183337216793891/50000000000000000000 : ℝ)^512 ≤ (2500774073664239/2500000000000000 : ℝ)^2089 := by
      have hnat : (50063183337216793891 : ℕ)^512*2500000000000000^2089 ≤ 2500774073664239^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063183337216793891 50000000000000000000 2500774073664239 2500000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500774073664239/2500000000000000 : ℝ)) (X := (50063183337216793891/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2918519399839617/50000000000000000000 : ℝ) ≤ ((3633315658565020339/3634500000000000000 : ℝ)+2*(351272923721/181725000000000 : ℝ)*(9169/100000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (3633315658565020339/3634500000000000000 : ℝ)+2*(351272923721/181725000000000 : ℝ)*(9169/100000 : ℝ)=(2500071527816797/2500000000000000 : ℝ) by norm_num, show 1+2*(2918519399839617/50000000000000000000 : ℝ)=(25002918519399839617/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63183337216793891/100000000000000000000 : ℝ)+(2918519399839617/50000000000000000000 : ℝ) ≤ ((3633315658565020339/3634500000000000000 : ℝ)+(351272923721/181725000000000 : ℝ)*((8219/50000 : ℝ)+(9169/100000 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (3633315658565020339/3634500000000000000 : ℝ)+(351272923721/181725000000000 : ℝ)*((8219/50000 : ℝ)+(9169/100000 : ℝ))=(1250211400370259/1250000000000000 : ℝ) by norm_num, show 1+(63183337216793891/100000000000000000000 : ℝ)+(2918519399839617/50000000000000000000 : ℝ)=(160110432601626357/160000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63183337216793891/100000000000000000000 : ℝ) ≤ ((3633315658565020339/3634500000000000000 : ℝ)+2*(351272923721/181725000000000 : ℝ)*(8219/50000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (3633315658565020339/3634500000000000000 : ℝ)+2*(351272923721/181725000000000 : ℝ)*(8219/50000 : ℝ)=(2500774073664239/2500000000000000 : ℝ) by norm_num, show 1+2*(63183337216793891/100000000000000000000 : ℝ)=(50063183337216793891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3633315658565020339/3634500000000000000 : ℝ)*(X 1 0+X 2 0)+(351272923721/181725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8219/50000 : ℝ)) (c := (3633315658565020339/3634500000000000000 : ℝ)) (alpha := (351272923721/181725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3633315658565020339/3634500000000000000 : ℝ)*(X 0 1+X 2 1)+(351272923721/181725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8219/50000 : ℝ)) (c := (3633315658565020339/3634500000000000000 : ℝ)) (alpha := (351272923721/181725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3633315658565020339/3634500000000000000 : ℝ)*(X 0 2+X 1 2)+(351272923721/181725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8219/50000 : ℝ)) (c := (3633315658565020339/3634500000000000000 : ℝ)) (alpha := (351272923721/181725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152840253/10000000000 : ℝ)*X 0 0+(2713474657/5000000000 : ℝ)*X 0 1+(5234111479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676635249/5000000000 : ℝ)*X 1 0+(-2251365729/10000000000 : ℝ)*X 1 1+(1046822257/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267663529/500000000 : ℝ)*X 2 0+(2617055651/5000000000 : ℝ)*X 2 1+(-1125682799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359462263/10000000000 : ℝ)*X 0 0+(4171019851/10000000000 : ℝ)*X 0 1+(4556321923/10000000000 : ℝ)*X 0 2+(4359462263/10000000000 : ℝ)*X 1 0+(4171019851/10000000000 : ℝ)*X 1 1+(4556321923/10000000000 : ℝ)*X 1 2+(4359462263/10000000000 : ℝ)*X 2 0+(4171019851/10000000000 : ℝ)*X 2 1+(4556321923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076428657/5000000000 : ℝ)*X 0 0+(1046969707/2000000000 : ℝ)*X 0 1+(2713104097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663042253/1250000000 : ℝ)*X 1 0+(-411853761/2000000000 : ℝ)*X 1 1+(2713104097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060867581/2000000000 : ℝ)*X 2 0+(678276051/1250000000 : ℝ)*X 2 1+(-2059268673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359496369/10000000000 : ℝ)*X 0 0+(910969841/2000000000 : ℝ)*X 0 1+(834500131/2000000000 : ℝ)*X 0 2+(4359496369/10000000000 : ℝ)*X 1 0+(910969841/2000000000 : ℝ)*X 1 1+(834500131/2000000000 : ℝ)*X 1 2+(4359496369/10000000000 : ℝ)*X 2 0+(910969841/2000000000 : ℝ)*X 2 1+(834500131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61450169743595702443619031/7571875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (960821017/50000000000000 : ℝ)*(base19) + (1840575287/100000000000000 : ℝ)*(base23) + (8592051/10000000000000 : ℝ)*(lower2) + (165300643/100000000000000 : ℝ)*(upper3) + (198498507/100000000000000 : ℝ)*(upper5) + (30395184173223/781250000000 : ℝ)*(major0) + (30395184173223/781250000000 : ℝ)*(major1) + (30395184173223/781250000000 : ℝ)*(major2) + (2592867328586629/50000000000000 : ℝ)*(sp0) + (1037153313787883/20000000000000 : ℝ)*(sp1) + (5185766650006163/100000000000000 : ℝ)*(sp2) + (1297691025116689/50000000000000 : ℝ)*(sp3) + (528647003/1562500000000 : ℝ)*(sp4) + (3267402173/20000000000000 : ℝ)*(sp7) + (2595398387244243/100000000000000 : ℝ)*(f.failure) + (5185768490581449/100000000000000 : ℝ)*(f.sum) + (102572268378377/12115000000000000000000000000 : ℝ)*base65 + (76229013901164533/7571875000000000000000000000000 : ℝ)*base68 + (112074827168577033/7571875000000000000000000000000 : ℝ)*base70 + (59991124435170783/7571875000000000000000000000000 : ℝ)*base72 + (9798775000453/3028750000000000000000000000 : ℝ)*base73 + (329347421488761/59155273437500000000000000000 : ℝ)*base76 + (27717566069577033/7571875000000000000000000000000 : ℝ)*base78 + (4277351172920783/7571875000000000000000000000000 : ℝ)*base80 + (33520238847793/12115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (738939/312500000000000000000 : ℝ)*base89 + (738939/312500000000000000000 : ℝ)*base91 + (738939/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80179698337066015671865557/15143750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36015177/3125000000000 : ℝ)*(base19) + (1217243703/100000000000000 : ℝ)*(base23) + (60598269/50000000000000 : ℝ)*(upper3) + (70352163/100000000000000 : ℝ)*(lower4) + (6761881/5000000000000 : ℝ)*(upper5) + (1960293615064113/50000000000000 : ℝ)*(major0) + (1960293615064113/50000000000000 : ℝ)*(major1) + (1960293615064113/50000000000000 : ℝ)*(major2) + (4226266947/20000000000000 : ℝ)*(sp1) + (331028999/1250000000000 : ℝ)*(sp2) + (326610033381387/6250000000000 : ℝ)*(sp4) + (5225738250281793/100000000000000 : ℝ)*(sp5) + (5225732834538569/100000000000000 : ℝ)*(sp6) + (261541374966847/10000000000000 : ℝ)*(sp7) + (261541374966847/10000000000000 : ℝ)*(f.failure) + (326610033381387/6250000000000 : ℝ)*(f.sum) + (662356291701/6057500000000000000000000000 : ℝ)*base66 + (144320764990765231/60575000000000000000000000000000 : ℝ)*base68 + (54073345236865231/60575000000000000000000000000000 : ℝ)*base70 + (114844803821584769/60575000000000000000000000000000 : ℝ)*base71 + (6442719778811/6057500000000000000000000000 : ℝ)*base74 + (1319959704541540231/60575000000000000000000000000000 : ℝ)*base76 + (433490180886140231/60575000000000000000000000000000 : ℝ)*base78 + (448912174092165231/60575000000000000000000000000000 : ℝ)*base80 + (35145876219333/12115000000000000000000000000 : ℝ)*base81 + (41631/31250000000000000000 : ℝ)*base89 + (41631/31250000000000000000 : ℝ)*base91 + (41631/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1164_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10699/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (739/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s4_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155672327/10000000000 : ℝ)*x 0 + (67510727/125000000 : ℝ)*x 1 + (5258349047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155672327/10000000000 : ℝ)^8357 ≤ (6549728461489/50000000000000 : ℝ)^6309 := by
    have hnat : (2155672327 : ℕ)^8357*50000000000000^6309 ≤ 6549728461489^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155672327 10000000000 6549728461489 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67510727/125000000 : ℝ)^8357 ≤ (44219721833263/100000000000000 : ℝ)^6309 := by
    have hnat : (67510727 : ℕ)^8357*100000000000000^6309 ≤ 44219721833263^6309*125000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67510727 125000000 44219721833263 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258349047/10000000000 : ℝ)^8357 ≤ (21340410612719/50000000000000 : ℝ)^6309 := by
    have hnat : (5258349047 : ℕ)^8357*50000000000000^6309 ≤ 21340410612719^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258349047 10000000000 21340410612719 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155672327/10000000000 : ℝ), (67510727/125000000 : ℝ), (5258349047/10000000000 : ℝ)] ![(6549728461489/50000000000000 : ℝ), (44219721833263/100000000000000 : ℝ), (21340410612719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155672327/10000000000 : ℝ)|^8357 ≤ (6549728461489/50000000000000 : ℝ)^6309
        have hw : |(-2155672327/10000000000 : ℝ)|=(2155672327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67510727/125000000 : ℝ)|^8357 ≤ (44219721833263/100000000000000 : ℝ)^6309
        have hw : |(67510727/125000000 : ℝ)|=(67510727/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258349047/10000000000 : ℝ)|^8357 ≤ (21340410612719/50000000000000 : ℝ)^6309
        have hw : |(5258349047/10000000000 : ℝ)|=(5258349047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673369709/5000000000 : ℝ)*x 0 + (-2228078989/10000000000 : ℝ)*x 1 + (5258349007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673369709/5000000000 : ℝ)^8357 ≤ (43633742508887/100000000000000 : ℝ)^6309 := by
    have hnat : (2673369709 : ℕ)^8357*100000000000000^6309 ≤ 43633742508887^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673369709 5000000000 43633742508887 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228078989/10000000000 : ℝ)^8357 ≤ (6842718341339/50000000000000 : ℝ)^6309 := by
    have hnat : (2228078989 : ℕ)^8357*50000000000000^6309 ≤ 6842718341339^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228078989 10000000000 6842718341339 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258349007/10000000000 : ℝ)^8357 ≤ (21340410397687/50000000000000 : ℝ)^6309 := by
    have hnat : (5258349007 : ℕ)^8357*50000000000000^6309 ≤ 21340410397687^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258349007 10000000000 21340410397687 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673369709/5000000000 : ℝ), (-2228078989/10000000000 : ℝ), (5258349007/10000000000 : ℝ)] ![(43633742508887/100000000000000 : ℝ), (6842718341339/50000000000000 : ℝ), (21340410397687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673369709/5000000000 : ℝ)|^8357 ≤ (43633742508887/100000000000000 : ℝ)^6309
        have hw : |(2673369709/5000000000 : ℝ)|=(2673369709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228078989/10000000000 : ℝ)|^8357 ≤ (6842718341339/50000000000000 : ℝ)^6309
        have hw : |(-2228078989/10000000000 : ℝ)|=(2228078989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258349007/10000000000 : ℝ)|^8357 ≤ (21340410397687/50000000000000 : ℝ)^6309
        have hw : |(5258349007/10000000000 : ℝ)|=(5258349007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346740167/10000000000 : ℝ)*x 0 + (164323379/312500000 : ℝ)*x 1 + (-445615831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346740167/10000000000 : ℝ)^8357 ≤ (43633750605533/100000000000000 : ℝ)^6309 := by
    have hnat : (5346740167 : ℕ)^8357*100000000000000^6309 ≤ 43633750605533^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346740167 10000000000 43633750605533 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164323379/312500000 : ℝ)^8357 ≤ (8536162268943/20000000000000 : ℝ)^6309 := by
    have hnat : (164323379 : ℕ)^8357*20000000000000^6309 ≤ 8536162268943^6309*312500000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164323379 312500000 8536162268943 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445615831/2000000000 : ℝ)^8357 ≤ (3421359508319/25000000000000 : ℝ)^6309 := by
    have hnat : (445615831 : ℕ)^8357*25000000000000^6309 ≤ 3421359508319^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445615831 2000000000 3421359508319 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346740167/10000000000 : ℝ), (164323379/312500000 : ℝ), (-445615831/2000000000 : ℝ)] ![(43633750605533/100000000000000 : ℝ), (8536162268943/20000000000000 : ℝ), (3421359508319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346740167/10000000000 : ℝ)|^8357 ≤ (43633750605533/100000000000000 : ℝ)^6309
        have hw : |(5346740167/10000000000 : ℝ)|=(5346740167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164323379/312500000 : ℝ)|^8357 ≤ (8536162268943/20000000000000 : ℝ)^6309
        have hw : |(164323379/312500000 : ℝ)|=(164323379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445615831/2000000000 : ℝ)|^8357 ≤ (3421359508319/25000000000000 : ℝ)^6309
        have hw : |(-445615831/2000000000 : ℝ)|=(445615831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361152623/10000000000 : ℝ)*x 0 + (4221080677/10000000000 : ℝ)*x 1 + (4505824543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361152623/10000000000 : ℝ)^8357 ≤ (832818260457/2500000000000 : ℝ)^6309 := by
    have hnat : (4361152623 : ℕ)^8357*2500000000000^6309 ≤ 832818260457^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361152623 10000000000 832818260457 2500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221080677/10000000000 : ℝ)^8357 ≤ (31902911307809/100000000000000 : ℝ)^6309 := by
    have hnat : (4221080677 : ℕ)^8357*100000000000000^6309 ≤ 31902911307809^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221080677 10000000000 31902911307809 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505824543/10000000000 : ℝ)^8357 ≤ (34784358255609/100000000000000 : ℝ)^6309 := by
    have hnat : (4505824543 : ℕ)^8357*100000000000000^6309 ≤ 34784358255609^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505824543 10000000000 34784358255609 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361152623/10000000000 : ℝ), (4221080677/10000000000 : ℝ), (4505824543/10000000000 : ℝ)] ![(832818260457/2500000000000 : ℝ), (31902911307809/100000000000000 : ℝ), (34784358255609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361152623/10000000000 : ℝ)|^8357 ≤ (832818260457/2500000000000 : ℝ)^6309
        have hw : |(4361152623/10000000000 : ℝ)|=(4361152623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221080677/10000000000 : ℝ)|^8357 ≤ (31902911307809/100000000000000 : ℝ)^6309
        have hw : |(4221080677/10000000000 : ℝ)|=(4221080677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505824543/10000000000 : ℝ)|^8357 ≤ (34784358255609/100000000000000 : ℝ)^6309
        have hw : |(4505824543/10000000000 : ℝ)|=(4505824543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-134729997/625000000 : ℝ)*x 0 + (2629375789/5000000000 : ℝ)*x 1 + (5400453439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134729997/625000000 : ℝ)^8357 ≤ (13099518299251/100000000000000 : ℝ)^6309 := by
    have hnat : (134729997 : ℕ)^8357*100000000000000^6309 ≤ 13099518299251^6309*625000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134729997 625000000 13099518299251 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629375789/5000000000 : ℝ)^8357 ≤ (42685149132827/100000000000000 : ℝ)^6309 := by
    have hnat : (2629375789 : ℕ)^8357*100000000000000^6309 ≤ 42685149132827^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629375789 5000000000 42685149132827 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400453439/10000000000 : ℝ)^8357 ≤ (4421533255043/10000000000000 : ℝ)^6309 := by
    have hnat : (5400453439 : ℕ)^8357*10000000000000^6309 ≤ 4421533255043^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400453439 10000000000 4421533255043 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134729997/625000000 : ℝ), (2629375789/5000000000 : ℝ), (5400453439/10000000000 : ℝ)] ![(13099518299251/100000000000000 : ℝ), (42685149132827/100000000000000 : ℝ), (4421533255043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134729997/625000000 : ℝ)|^8357 ≤ (13099518299251/100000000000000 : ℝ)^6309
        have hw : |(-134729997/625000000 : ℝ)|=(134729997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629375789/5000000000 : ℝ)|^8357 ≤ (42685149132827/100000000000000 : ℝ)^6309
        have hw : |(2629375789/5000000000 : ℝ)|=(2629375789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400453439/10000000000 : ℝ)|^8357 ≤ (4421533255043/10000000000000 : ℝ)^6309
        have hw : |(5400453439/10000000000 : ℝ)|=(5400453439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655289247/5000000000 : ℝ)*x 0 + (-1042986783/5000000000 : ℝ)*x 1 + (5400453347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655289247/5000000000 : ℝ)^8357 ≤ (21621637403063/50000000000000 : ℝ)^6309 := by
    have hnat : (2655289247 : ℕ)^8357*50000000000000^6309 ≤ 21621637403063^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655289247 5000000000 21621637403063 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042986783/5000000000 : ℝ)^8357 ≤ (12541393633701/100000000000000 : ℝ)^6309 := by
    have hnat : (1042986783 : ℕ)^8357*100000000000000^6309 ≤ 12541393633701^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042986783 5000000000 12541393633701 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400453347/10000000000 : ℝ)^8357 ≤ (44215331552683/100000000000000 : ℝ)^6309 := by
    have hnat : (5400453347 : ℕ)^8357*100000000000000^6309 ≤ 44215331552683^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400453347 10000000000 44215331552683 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655289247/5000000000 : ℝ), (-1042986783/5000000000 : ℝ), (5400453347/10000000000 : ℝ)] ![(21621637403063/50000000000000 : ℝ), (12541393633701/100000000000000 : ℝ), (44215331552683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655289247/5000000000 : ℝ)|^8357 ≤ (21621637403063/50000000000000 : ℝ)^6309
        have hw : |(2655289247/5000000000 : ℝ)|=(2655289247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042986783/5000000000 : ℝ)|^8357 ≤ (12541393633701/100000000000000 : ℝ)^6309
        have hw : |(-1042986783/5000000000 : ℝ)|=(1042986783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400453347/10000000000 : ℝ)|^8357 ≤ (44215331552683/100000000000000 : ℝ)^6309
        have hw : |(5400453347/10000000000 : ℝ)|=(5400453347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310578249/10000000000 : ℝ)*x 0 + (1350113329/2500000000 : ℝ)*x 1 + (-104298697/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310578249/10000000000 : ℝ)^8357 ≤ (43243272163519/100000000000000 : ℝ)^6309 := by
    have hnat : (5310578249 : ℕ)^8357*100000000000000^6309 ≤ 43243272163519^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310578249 10000000000 43243272163519 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350113329/2500000000 : ℝ)^8357 ≤ (22107665608243/50000000000000 : ℝ)^6309 := by
    have hnat : (1350113329 : ℕ)^8357*50000000000000^6309 ≤ 22107665608243^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350113329 2500000000 22107665608243 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104298697/500000000 : ℝ)^8357 ≤ (783837288263/6250000000000 : ℝ)^6309 := by
    have hnat : (104298697 : ℕ)^8357*6250000000000^6309 ≤ 783837288263^6309*500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104298697 500000000 783837288263 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310578249/10000000000 : ℝ), (1350113329/2500000000 : ℝ), (-104298697/500000000 : ℝ)] ![(43243272163519/100000000000000 : ℝ), (22107665608243/50000000000000 : ℝ), (783837288263/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310578249/10000000000 : ℝ)|^8357 ≤ (43243272163519/100000000000000 : ℝ)^6309
        have hw : |(5310578249/10000000000 : ℝ)|=(5310578249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350113329/2500000000 : ℝ)|^8357 ≤ (22107665608243/50000000000000 : ℝ)^6309
        have hw : |(1350113329/2500000000 : ℝ)|=(1350113329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104298697/500000000 : ℝ)|^8357 ≤ (783837288263/6250000000000 : ℝ)^6309
        have hw : |(-104298697/500000000 : ℝ)|=(104298697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s4_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180583153/5000000000 : ℝ)*x 0 + (4505018507/10000000000 : ℝ)*x 1 + (4221890099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180583153/5000000000 : ℝ)^8357 ≤ (16656434432133/50000000000000 : ℝ)^6309 := by
    have hnat : (2180583153 : ℕ)^8357*50000000000000^6309 ≤ 16656434432133^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180583153 5000000000 16656434432133 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505018507/10000000000 : ℝ)^8357 ≤ (6955223217673/20000000000000 : ℝ)^6309 := by
    have hnat : (4505018507 : ℕ)^8357*20000000000000^6309 ≤ 6955223217673^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505018507 10000000000 6955223217673 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221890099/10000000000 : ℝ)^8357 ≤ (79777537599/250000000000 : ℝ)^6309 := by
    have hnat : (4221890099 : ℕ)^8357*250000000000^6309 ≤ 79777537599^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221890099 10000000000 79777537599 250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180583153/5000000000 : ℝ), (4505018507/10000000000 : ℝ), (4221890099/10000000000 : ℝ)] ![(16656434432133/50000000000000 : ℝ), (6955223217673/20000000000000 : ℝ), (79777537599/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180583153/5000000000 : ℝ)|^8357 ≤ (16656434432133/50000000000000 : ℝ)^6309
        have hw : |(2180583153/5000000000 : ℝ)|=(2180583153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505018507/10000000000 : ℝ)|^8357 ≤ (6955223217673/20000000000000 : ℝ)^6309
        have hw : |(4505018507/10000000000 : ℝ)|=(4505018507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221890099/10000000000 : ℝ)|^8357 ≤ (79777537599/250000000000 : ℝ)^6309
        have hw : |(4221890099/10000000000 : ℝ)|=(4221890099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10699/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10699/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10699/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10699/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10699/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10699/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10699/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10699/100000 : ℝ) ^ (2089/512 : ℝ) ≤ (1095580698728621/10000000000000000000 : ℝ) := by
    have hpowers : (10699/100000 : ℝ)^2089 ≤ (1095580698728621/10000000000000000000 : ℝ)^512 := by
      have hnat : (10699 : ℕ)^2089*10000000000000000000^512 ≤ 1095580698728621^512*100000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10699 100000 1095580698728621 10000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10699/100000 : ℝ)) (X := (1095580698728621/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (739/5000 : ℝ) ^ (2089/512 : ℝ) ≤ (40945560619522273/100000000000000000000 : ℝ) := by
    have hpowers : (739/5000 : ℝ)^2089 ≤ (40945560619522273/100000000000000000000 : ℝ)^512 := by
      have hnat : (739 : ℕ)^2089*100000000000000000000^512 ≤ 40945560619522273^512*5000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        739 5000 40945560619522273 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (739/5000 : ℝ)) (X := (40945560619522273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001095580698728621/5000000000000000000 : ℝ) ≤ (10000536994668021/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (5001095580698728621/5000000000000000000 : ℝ)^512 ≤ (10000536994668021/10000000000000000 : ℝ)^2089 := by
      have hnat : (5001095580698728621 : ℕ)^512*10000000000000000^2089 ≤ 10000536994668021^2089*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001095580698728621 5000000000000000000 10000536994668021 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536994668021/10000000000000000 : ℝ)) (X := (5001095580698728621/5000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051901367606808483/100000000000000000000 : ℝ) ≤ (400050872754341/400000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (100051901367606808483/100000000000000000000 : ℝ)^512 ≤ (400050872754341/400000000000000 : ℝ)^2089 := by
      have hnat : (100051901367606808483 : ℕ)^512*400000000000000^2089 ≤ 400050872754341^2089*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051901367606808483 100000000000000000000 400050872754341 400000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400050872754341/400000000000000 : ℝ)) (X := (100051901367606808483/100000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040945560619522273/50000000000000000000 : ℝ) ≤ (10002006643049029/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50040945560619522273/50000000000000000000 : ℝ)^512 ≤ (10002006643049029/10000000000000000 : ℝ)^2089 := by
      have hnat : (50040945560619522273 : ℕ)^512*10000000000000000^2089 ≤ 10002006643049029^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040945560619522273 50000000000000000000 10002006643049029 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002006643049029/10000000000000000 : ℝ)) (X := (50040945560619522273/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1095580698728621/10000000000000000000 : ℝ) ≤ ((769744673720977153/770000000000000000 : ℝ)+2*(1733075921/962500000000 : ℝ)*(10699/100000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (769744673720977153/770000000000000000 : ℝ)+2*(1733075921/962500000000 : ℝ)*(10699/100000 : ℝ)=(10000536994668021/10000000000000000 : ℝ) by norm_num, show 1+2*(1095580698728621/10000000000000000000 : ℝ)=(5001095580698728621/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40945560619522273/100000000000000000000 : ℝ)+(1095580698728621/10000000000000000000 : ℝ) ≤ ((769744673720977153/770000000000000000 : ℝ)+(1733075921/962500000000 : ℝ)*((739/5000 : ℝ)+(10699/100000 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (769744673720977153/770000000000000000 : ℝ)+(1733075921/962500000000 : ℝ)*((739/5000 : ℝ)+(10699/100000 : ℝ))=(400050872754341/400000000000000 : ℝ) by norm_num, show 1+(40945560619522273/100000000000000000000 : ℝ)+(1095580698728621/10000000000000000000 : ℝ)=(100051901367606808483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40945560619522273/100000000000000000000 : ℝ) ≤ ((769744673720977153/770000000000000000 : ℝ)+2*(1733075921/962500000000 : ℝ)*(739/5000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (769744673720977153/770000000000000000 : ℝ)+2*(1733075921/962500000000 : ℝ)*(739/5000 : ℝ)=(10002006643049029/10000000000000000 : ℝ) by norm_num, show 1+2*(40945560619522273/100000000000000000000 : ℝ)=(50040945560619522273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (769744673720977153/770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1733075921/962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (10699/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (769744673720977153/770000000000000000 : ℝ)) (alpha := (1733075921/962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (769744673720977153/770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1733075921/962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (10699/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (769744673720977153/770000000000000000 : ℝ)) (alpha := (1733075921/962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (769744673720977153/770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1733075921/962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (10699/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (769744673720977153/770000000000000000 : ℝ)) (alpha := (1733075921/962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155672327/10000000000 : ℝ)*X 0 0+(67510727/125000000 : ℝ)*X 0 1+(5258349047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673369709/5000000000 : ℝ)*X 1 0+(-2228078989/10000000000 : ℝ)*X 1 1+(5258349007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346740167/10000000000 : ℝ)*X 2 0+(164323379/312500000 : ℝ)*X 2 1+(-445615831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361152623/10000000000 : ℝ)*X 0 0+(4221080677/10000000000 : ℝ)*X 0 1+(4505824543/10000000000 : ℝ)*X 0 2+(4361152623/10000000000 : ℝ)*X 1 0+(4221080677/10000000000 : ℝ)*X 1 1+(4505824543/10000000000 : ℝ)*X 1 2+(4361152623/10000000000 : ℝ)*X 2 0+(4221080677/10000000000 : ℝ)*X 2 1+(4505824543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-134729997/625000000 : ℝ)*X 0 0+(2629375789/5000000000 : ℝ)*X 0 1+(5400453439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655289247/5000000000 : ℝ)*X 1 0+(-1042986783/5000000000 : ℝ)*X 1 1+(5400453347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310578249/10000000000 : ℝ)*X 2 0+(1350113329/2500000000 : ℝ)*X 2 1+(-104298697/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180583153/5000000000 : ℝ)*X 0 0+(4505018507/10000000000 : ℝ)*X 0 1+(4221890099/10000000000 : ℝ)*X 0 2+(2180583153/5000000000 : ℝ)*X 1 0+(4505018507/10000000000 : ℝ)*X 1 1+(4221890099/10000000000 : ℝ)*X 1 2+(2180583153/5000000000 : ℝ)*X 2 0+(4505018507/10000000000 : ℝ)*X 2 1+(4221890099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5677752699792330504969/385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156295951/25000000000000 : ℝ)*(base19) + (282006317/20000000000000 : ℝ)*(base23) + (72222907/25000000000000 : ℝ)*(lower2) + (51318459/25000000000000 : ℝ)*(upper3) + (18294851/10000000000000 : ℝ)*(lower4) + (329032948702077/6250000000000 : ℝ)*(major0) + (329032948702077/6250000000000 : ℝ)*(major1) + (329032948702077/6250000000000 : ℝ)*(major2) + (7017096761914127/100000000000000 : ℝ)*(sp0) + (1403420115398817/20000000000000 : ℝ)*(sp1) + (54821092126143/781250000000 : ℝ)*(sp2) + (1755967866048309/50000000000000 : ℝ)*(sp3) + (4440263763/100000000000000 : ℝ)*(sp4) + (1058288227/6250000000000 : ℝ)*(sp7) + (14047810658833/400000000000 : ℝ)*(f.failure) + (7017101202177889/100000000000000 : ℝ)*(f.sum) + (2710823984509/385000000000000000000000000 : ℝ)*base66 + (38574012463753219/4812500000000000000000000000000 : ℝ)*base68 + (17100707964496781/4812500000000000000000000000000 : ℝ)*base69 + (6685986974746781/4812500000000000000000000000000 : ℝ)*base71 + (34221688449/385000000000000000000000000 : ℝ)*base74 + (27837963067565719/4812500000000000000000000000000 : ℝ)*base76 + (23457307704371781/4812500000000000000000000000000 : ℝ)*base77 + (20771730745378219/4812500000000000000000000000000 : ℝ)*base80 + (316927722547/192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9/1250000000000000000 : ℝ)*base89 + (9/1250000000000000000 : ℝ)*base91 + (9/1250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22543623947919358827/55000000000000000000000000 : ℝ) := by norm_num
    linear_combination (562670671/50000000000000 : ℝ)*(base19) + (63788939/6250000000000 : ℝ)*(base23) + (44338651/25000000000000 : ℝ)*(upper2) + (2642811/2500000000000 : ℝ)*(upper5) + (1323630010034031/25000000000000 : ℝ)*(major0) + (1323630010034031/25000000000000 : ℝ)*(major1) + (1323630010034031/25000000000000 : ℝ)*(major2) + (328046999/5000000000000 : ℝ)*(sp0) + (38416469931/100000000000000 : ℝ)*(sp1) + (21804659917/100000000000000 : ℝ)*(sp2) + (7057072679889187/100000000000000 : ℝ)*(sp4) + (7057039699017893/100000000000000 : ℝ)*(sp5) + (282282256621849/4000000000000 : ℝ)*(sp6) + (220747551611267/6250000000000 : ℝ)*(sp7) + (220747551611267/6250000000000 : ℝ)*(f.failure) + (7057079240829167/100000000000000 : ℝ)*(f.sum) + (87533921559/13750000000000000000000000 : ℝ)*base65 + (9879839044743751/2750000000000000000000000000000 : ℝ)*base68 + (17300637844993751/2750000000000000000000000000000 : ℝ)*base70 + (12768526414756249/2750000000000000000000000000000 : ℝ)*base71 + (303847036509/55000000000000000000000000 : ℝ)*base74 + (11151733258756249/2750000000000000000000000000000 : ℝ)*base75 + (18374641038756249/2750000000000000000000000000000 : ℝ)*base77 + (14641446417243751/2750000000000000000000000000000 : ℝ)*base80 + (89176221261/55000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38541/19531250000000000000 : ℝ)*base89 + (38541/19531250000000000000 : ℝ)*base91 + (38541/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1164_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10699/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s5_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156263783/10000000000 : ℝ)*x 0 + (53943419/100000000 : ℝ)*x 1 + (5264476849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156263783/10000000000 : ℝ)^8357 ≤ (13104217967029/100000000000000 : ℝ)^6309 := by
    have hnat : (2156263783 : ℕ)^8357*100000000000000^6309 ≤ 13104217967029^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156263783 10000000000 13104217967029 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53943419/100000000 : ℝ)^8357 ≤ (44149064631321/100000000000000 : ℝ)^6309 := by
    have hnat : (53943419 : ℕ)^8357*100000000000000^6309 ≤ 44149064631321^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53943419 100000000 44149064631321 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264476849/10000000000 : ℝ)^8357 ≤ (21373358689893/50000000000000 : ℝ)^6309 := by
    have hnat : (5264476849 : ℕ)^8357*50000000000000^6309 ≤ 21373358689893^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264476849 10000000000 21373358689893 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156263783/10000000000 : ℝ), (53943419/100000000 : ℝ), (5264476849/10000000000 : ℝ)] ![(13104217967029/100000000000000 : ℝ), (44149064631321/100000000000000 : ℝ), (21373358689893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156263783/10000000000 : ℝ)|^8357 ≤ (13104217967029/100000000000000 : ℝ)^6309
        have hw : |(-2156263783/10000000000 : ℝ)|=(2156263783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53943419/100000000 : ℝ)|^8357 ≤ (44149064631321/100000000000000 : ℝ)^6309
        have hw : |(53943419/100000000 : ℝ)|=(53943419/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264476849/10000000000 : ℝ)|^8357 ≤ (21373358689893/50000000000000 : ℝ)^6309
        have hw : |(5264476849/10000000000 : ℝ)|=(5264476849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668137651/1250000000 : ℝ)*x 0 + (-2222154021/10000000000 : ℝ)*x 1 + (5264476569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668137651/1250000000 : ℝ)^8357 ≤ (43616034436293/100000000000000 : ℝ)^6309 := by
    have hnat : (668137651 : ℕ)^8357*100000000000000^6309 ≤ 43616034436293^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668137651 1250000000 43616034436293 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222154021/10000000000 : ℝ)^8357 ≤ (6818625591873/50000000000000 : ℝ)^6309 := by
    have hnat : (2222154021 : ℕ)^8357*50000000000000^6309 ≤ 6818625591873^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222154021 10000000000 6818625591873 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264476569/10000000000 : ℝ)^8357 ≤ (42746714368199/100000000000000 : ℝ)^6309 := by
    have hnat : (5264476569 : ℕ)^8357*100000000000000^6309 ≤ 42746714368199^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264476569 10000000000 42746714368199 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668137651/1250000000 : ℝ), (-2222154021/10000000000 : ℝ), (5264476569/10000000000 : ℝ)] ![(43616034436293/100000000000000 : ℝ), (6818625591873/50000000000000 : ℝ), (42746714368199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668137651/1250000000 : ℝ)|^8357 ≤ (43616034436293/100000000000000 : ℝ)^6309
        have hw : |(668137651/1250000000 : ℝ)|=(668137651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222154021/10000000000 : ℝ)|^8357 ≤ (6818625591873/50000000000000 : ℝ)^6309
        have hw : |(-2222154021/10000000000 : ℝ)|=(2222154021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264476569/10000000000 : ℝ)|^8357 ≤ (42746714368199/100000000000000 : ℝ)^6309
        have hw : |(5264476569/10000000000 : ℝ)|=(5264476569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345101799/10000000000 : ℝ)*x 0 + (658059489/1250000000 : ℝ)*x 1 + (-2222154103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345101799/10000000000 : ℝ)^8357 ≤ (10904010206083/25000000000000 : ℝ)^6309 := by
    have hnat : (5345101799 : ℕ)^8357*25000000000000^6309 ≤ 10904010206083^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345101799 10000000000 10904010206083 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658059489/1250000000 : ℝ)^8357 ≤ (10686676825431/25000000000000 : ℝ)^6309 := by
    have hnat : (658059489 : ℕ)^8357*25000000000000^6309 ≤ 10686676825431^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658059489 1250000000 10686676825431 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222154103/10000000000 : ℝ)^8357 ≤ (13637251850333/100000000000000 : ℝ)^6309 := by
    have hnat : (2222154103 : ℕ)^8357*100000000000000^6309 ≤ 13637251850333^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222154103 10000000000 13637251850333 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345101799/10000000000 : ℝ), (658059489/1250000000 : ℝ), (-2222154103/10000000000 : ℝ)] ![(10904010206083/25000000000000 : ℝ), (10686676825431/25000000000000 : ℝ), (13637251850333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345101799/10000000000 : ℝ)|^8357 ≤ (10904010206083/25000000000000 : ℝ)^6309
        have hw : |(5345101799/10000000000 : ℝ)|=(5345101799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658059489/1250000000 : ℝ)|^8357 ≤ (10686676825431/25000000000000 : ℝ)^6309
        have hw : |(658059489/1250000000 : ℝ)|=(658059489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2222154103/10000000000 : ℝ)|^8357 ≤ (13637251850333/100000000000000 : ℝ)^6309
        have hw : |(-2222154103/10000000000 : ℝ)|=(2222154103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361497587/10000000000 : ℝ)*x 0 + (4233667981/10000000000 : ℝ)*x 1 + (2246574041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361497587/10000000000 : ℝ)^8357 ≤ (33316220842151/100000000000000 : ℝ)^6309 := by
    have hnat : (4361497587 : ℕ)^8357*100000000000000^6309 ≤ 33316220842151^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361497587 10000000000 33316220842151 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233667981/10000000000 : ℝ)^8357 ≤ (2001811830957/6250000000000 : ℝ)^6309 := by
    have hnat : (4233667981 : ℕ)^8357*6250000000000^6309 ≤ 2001811830957^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233667981 10000000000 2001811830957 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246574041/5000000000 : ℝ)^8357 ≤ (34654789843603/100000000000000 : ℝ)^6309 := by
    have hnat : (2246574041 : ℕ)^8357*100000000000000^6309 ≤ 34654789843603^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246574041 5000000000 34654789843603 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361497587/10000000000 : ℝ), (4233667981/10000000000 : ℝ), (2246574041/5000000000 : ℝ)] ![(33316220842151/100000000000000 : ℝ), (2001811830957/6250000000000 : ℝ), (34654789843603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361497587/10000000000 : ℝ)|^8357 ≤ (33316220842151/100000000000000 : ℝ)^6309
        have hw : |(4361497587/10000000000 : ℝ)|=(4361497587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233667981/10000000000 : ℝ)|^8357 ≤ (2001811830957/6250000000000 : ℝ)^6309
        have hw : |(4233667981/10000000000 : ℝ)|=(4233667981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246574041/5000000000 : ℝ)|^8357 ≤ (34654789843603/100000000000000 : ℝ)^6309
        have hw : |(2246574041/5000000000 : ℝ)|=(2246574041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431253981/2000000000 : ℝ)*x 0 + (2632405743/5000000000 : ℝ)*x 1 + (1348501337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431253981/2000000000 : ℝ)^8357 ≤ (3276066812379/25000000000000 : ℝ)^6309 := by
    have hnat : (431253981 : ℕ)^8357*25000000000000^6309 ≤ 3276066812379^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431253981 2000000000 3276066812379 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632405743/5000000000 : ℝ)^8357 ≤ (10687579165423/25000000000000 : ℝ)^6309 := by
    have hnat : (2632405743 : ℕ)^8357*25000000000000^6309 ≤ 10687579165423^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632405743 5000000000 10687579165423 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348501337/2500000000 : ℝ)^8357 ≤ (44145416078061/100000000000000 : ℝ)^6309 := by
    have hnat : (1348501337 : ℕ)^8357*100000000000000^6309 ≤ 44145416078061^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348501337 2500000000 44145416078061 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431253981/2000000000 : ℝ), (2632405743/5000000000 : ℝ), (1348501337/2500000000 : ℝ)] ![(3276066812379/25000000000000 : ℝ), (10687579165423/25000000000000 : ℝ), (44145416078061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431253981/2000000000 : ℝ)|^8357 ≤ (3276066812379/25000000000000 : ℝ)^6309
        have hw : |(-431253981/2000000000 : ℝ)|=(431253981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632405743/5000000000 : ℝ)|^8357 ≤ (10687579165423/25000000000000 : ℝ)^6309
        have hw : |(2632405743/5000000000 : ℝ)|=(2632405743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348501337/2500000000 : ℝ)|^8357 ≤ (44145416078061/100000000000000 : ℝ)^6309
        have hw : |(1348501337/2500000000 : ℝ)|=(1348501337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664018421/1250000000 : ℝ)*x 0 + (-523155921/2500000000 : ℝ)*x 1 + (5394005731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664018421/1250000000 : ℝ)^8357 ≤ (43260197734103/100000000000000 : ℝ)^6309 := by
    have hnat : (664018421 : ℕ)^8357*100000000000000^6309 ≤ 43260197734103^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664018421 1250000000 43260197734103 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523155921/2500000000 : ℝ)^8357 ≤ (12594382024057/100000000000000 : ℝ)^6309 := by
    have hnat : (523155921 : ℕ)^8357*100000000000000^6309 ≤ 12594382024057^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523155921 2500000000 12594382024057 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394005731/10000000000 : ℝ)^8357 ≤ (22072710115057/50000000000000 : ℝ)^6309 := by
    have hnat : (5394005731 : ℕ)^8357*50000000000000^6309 ≤ 22072710115057^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394005731 10000000000 22072710115057 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664018421/1250000000 : ℝ), (-523155921/2500000000 : ℝ), (5394005731/10000000000 : ℝ)] ![(43260197734103/100000000000000 : ℝ), (12594382024057/100000000000000 : ℝ), (22072710115057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664018421/1250000000 : ℝ)|^8357 ≤ (43260197734103/100000000000000 : ℝ)^6309
        have hw : |(664018421/1250000000 : ℝ)|=(664018421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523155921/2500000000 : ℝ)|^8357 ≤ (12594382024057/100000000000000 : ℝ)^6309
        have hw : |(-523155921/2500000000 : ℝ)|=(523155921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394005731/10000000000 : ℝ)|^8357 ≤ (22072710115057/50000000000000 : ℝ)^6309
        have hw : |(5394005731/10000000000 : ℝ)|=(5394005731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312146949/10000000000 : ℝ)*x 0 + (2697002973/5000000000 : ℝ)*x 1 + (-1046311979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312146949/10000000000 : ℝ)^8357 ≤ (43260193214271/100000000000000 : ℝ)^6309 := by
    have hnat : (5312146949 : ℕ)^8357*100000000000000^6309 ≤ 43260193214271^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312146949 10000000000 43260193214271 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697002973/5000000000 : ℝ)^8357 ≤ (44145422560901/100000000000000 : ℝ)^6309 := by
    have hnat : (2697002973 : ℕ)^8357*100000000000000^6309 ≤ 44145422560901^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697002973 5000000000 44145422560901 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046311979/5000000000 : ℝ)^8357 ≤ (12594384208427/100000000000000 : ℝ)^6309 := by
    have hnat : (1046311979 : ℕ)^8357*100000000000000^6309 ≤ 12594384208427^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046311979 5000000000 12594384208427 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312146949/10000000000 : ℝ), (2697002973/5000000000 : ℝ), (-1046311979/5000000000 : ℝ)] ![(43260193214271/100000000000000 : ℝ), (44145422560901/100000000000000 : ℝ), (12594384208427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312146949/10000000000 : ℝ)|^8357 ≤ (43260193214271/100000000000000 : ℝ)^6309
        have hw : |(5312146949/10000000000 : ℝ)|=(5312146949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697002973/5000000000 : ℝ)|^8357 ≤ (44145422560901/100000000000000 : ℝ)^6309
        have hw : |(2697002973/5000000000 : ℝ)|=(2697002973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046311979/5000000000 : ℝ)|^8357 ≤ (12594384208427/100000000000000 : ℝ)^6309
        have hw : |(-1046311979/5000000000 : ℝ)|=(1046311979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s5_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872301721/2000000000 : ℝ)*x 0 + (1123119517/2500000000 : ℝ)*x 1 + (42343399/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872301721/2000000000 : ℝ)^8357 ≤ (33316332326247/100000000000000 : ℝ)^6309 := by
    have hnat : (872301721 : ℕ)^8357*100000000000000^6309 ≤ 33316332326247^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872301721 2000000000 33316332326247 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123119517/2500000000 : ℝ)^8357 ≤ (34647944806951/100000000000000 : ℝ)^6309 := by
    have hnat : (1123119517 : ℕ)^8357*100000000000000^6309 ≤ 34647944806951^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123119517 2500000000 34647944806951 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42343399/100000000 : ℝ)^8357 ≤ (32035722850463/100000000000000 : ℝ)^6309 := by
    have hnat : (42343399 : ℕ)^8357*100000000000000^6309 ≤ 32035722850463^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42343399 100000000 32035722850463 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872301721/2000000000 : ℝ), (1123119517/2500000000 : ℝ), (42343399/100000000 : ℝ)] ![(33316332326247/100000000000000 : ℝ), (34647944806951/100000000000000 : ℝ), (32035722850463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872301721/2000000000 : ℝ)|^8357 ≤ (33316332326247/100000000000000 : ℝ)^6309
        have hw : |(872301721/2000000000 : ℝ)|=(872301721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123119517/2500000000 : ℝ)|^8357 ≤ (34647944806951/100000000000000 : ℝ)^6309
        have hw : |(1123119517/2500000000 : ℝ)|=(1123119517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42343399/100000000 : ℝ)|^8357 ≤ (32035722850463/100000000000000 : ℝ)^6309
        have hw : |(42343399/100000000 : ℝ)|=(42343399/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (701/6250 : ℝ) ^ (2089/512 : ℝ) ≤ (13282040835349411/100000000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^2089 ≤ (13282040835349411/100000000000000000000 : ℝ)^512 := by
      have hnat : (701 : ℕ)^2089*100000000000000000000^512 ≤ 13282040835349411^512*6250^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 13282040835349411 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (13282040835349411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (2089/512 : ℝ) ≤ (1755811385587529/5000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^2089 ≤ (1755811385587529/5000000000000000000 : ℝ)^512 := by
      have hnat : (7117 : ℕ)^2089*5000000000000000000^512 ≤ 1755811385587529^512*50000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 1755811385587529 5000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (1755811385587529/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013282040835349411/50000000000000000000 : ℝ) ≤ (400026040107831/400000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50013282040835349411/50000000000000000000 : ℝ)^512 ≤ (400026040107831/400000000000000 : ℝ)^2089 := by
      have hnat : (50013282040835349411 : ℕ)^512*400000000000000^2089 ≤ 400026040107831^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013282040835349411 50000000000000000000 400026040107831 400000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026040107831/400000000000000 : ℝ)) (X := (50013282040835349411/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048398268547099991/100000000000000000000 : ℝ) ≤ (5000592996360963/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (100048398268547099991/100000000000000000000 : ℝ)^512 ≤ (5000592996360963/5000000000000000 : ℝ)^2089 := by
      have hnat : (100048398268547099991 : ℕ)^512*5000000000000000^2089 ≤ 5000592996360963^2089*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048398268547099991 100000000000000000000 5000592996360963 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000592996360963/5000000000000000 : ℝ)) (X := (100048398268547099991/100000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501755811385587529/2500000000000000000 : ℝ) ≤ (10001720982748077/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (2501755811385587529/2500000000000000000 : ℝ)^512 ≤ (10001720982748077/10000000000000000 : ℝ)^2089 := by
      have hnat : (2501755811385587529 : ℕ)^512*10000000000000000^2089 ≤ 10001720982748077^2089*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501755811385587529 2500000000000000000 10001720982748077 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001720982748077/10000000000000000 : ℝ)) (X := (2501755811385587529/2500000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13282040835349411/100000000000000000000 : ℝ) ≤ ((5028327304978204953/5030000000000000000 : ℝ)+2*(178330008717/100600000000000 : ℝ)*(701/6250 : ℝ))^(2089/512 : ℝ) := by
    rw [show (5028327304978204953/5030000000000000000 : ℝ)+2*(178330008717/100600000000000 : ℝ)*(701/6250 : ℝ)=(400026040107831/400000000000000 : ℝ) by norm_num, show 1+2*(13282040835349411/100000000000000000000 : ℝ)=(50013282040835349411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1755811385587529/5000000000000000000 : ℝ)+(13282040835349411/100000000000000000000 : ℝ) ≤ ((5028327304978204953/5030000000000000000 : ℝ)+(178330008717/100600000000000 : ℝ)*((7117/50000 : ℝ)+(701/6250 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (5028327304978204953/5030000000000000000 : ℝ)+(178330008717/100600000000000 : ℝ)*((7117/50000 : ℝ)+(701/6250 : ℝ))=(5000592996360963/5000000000000000 : ℝ) by norm_num, show 1+(1755811385587529/5000000000000000000 : ℝ)+(13282040835349411/100000000000000000000 : ℝ)=(100048398268547099991/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1755811385587529/5000000000000000000 : ℝ) ≤ ((5028327304978204953/5030000000000000000 : ℝ)+2*(178330008717/100600000000000 : ℝ)*(7117/50000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (5028327304978204953/5030000000000000000 : ℝ)+2*(178330008717/100600000000000 : ℝ)*(7117/50000 : ℝ)=(10001720982748077/10000000000000000 : ℝ) by norm_num, show 1+2*(1755811385587529/5000000000000000000 : ℝ)=(2501755811385587529/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5028327304978204953/5030000000000000000 : ℝ)*(X 1 0+X 2 0)+(178330008717/100600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (5028327304978204953/5030000000000000000 : ℝ)) (alpha := (178330008717/100600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5028327304978204953/5030000000000000000 : ℝ)*(X 0 1+X 2 1)+(178330008717/100600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (5028327304978204953/5030000000000000000 : ℝ)) (alpha := (178330008717/100600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5028327304978204953/5030000000000000000 : ℝ)*(X 0 2+X 1 2)+(178330008717/100600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (5028327304978204953/5030000000000000000 : ℝ)) (alpha := (178330008717/100600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156263783/10000000000 : ℝ)*X 0 0+(53943419/100000000 : ℝ)*X 0 1+(5264476849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668137651/1250000000 : ℝ)*X 1 0+(-2222154021/10000000000 : ℝ)*X 1 1+(5264476569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345101799/10000000000 : ℝ)*X 2 0+(658059489/1250000000 : ℝ)*X 2 1+(-2222154103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361497587/10000000000 : ℝ)*X 0 0+(4233667981/10000000000 : ℝ)*X 0 1+(2246574041/5000000000 : ℝ)*X 0 2+(4361497587/10000000000 : ℝ)*X 1 0+(4233667981/10000000000 : ℝ)*X 1 1+(2246574041/5000000000 : ℝ)*X 1 2+(4361497587/10000000000 : ℝ)*X 2 0+(4233667981/10000000000 : ℝ)*X 2 1+(2246574041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431253981/2000000000 : ℝ)*X 0 0+(2632405743/5000000000 : ℝ)*X 0 1+(1348501337/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664018421/1250000000 : ℝ)*X 1 0+(-523155921/2500000000 : ℝ)*X 1 1+(5394005731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312146949/10000000000 : ℝ)*X 2 0+(2697002973/5000000000 : ℝ)*X 2 1+(-1046311979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872301721/2000000000 : ℝ)*X 0 0+(1123119517/2500000000 : ℝ)*X 0 1+(42343399/100000000 : ℝ)*X 0 2+(872301721/2000000000 : ℝ)*X 1 0+(1123119517/2500000000 : ℝ)*X 1 1+(42343399/100000000 : ℝ)*X 1 2+(872301721/2000000000 : ℝ)*X 2 0+(1123119517/2500000000 : ℝ)*X 2 1+(42343399/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25573224051594444064161/2515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53973541/20000000000000 : ℝ)*(base8) + (57732901/12500000000000 : ℝ)*(base21) + (557480037/100000000000000 : ℝ)*(lower2) + (616949/2000000000000 : ℝ)*(upper4) + (2888534056355211/50000000000000 : ℝ)*(major0) + (2888534056355211/50000000000000 : ℝ)*(major1) + (2888534056355211/50000000000000 : ℝ)*(major2) + (7700268201381459/100000000000000 : ℝ)*(sp0) + (7700262794049583/100000000000000 : ℝ)*(sp1) + (770023752538973/10000000000000 : ℝ)*(sp2) + (192692838102477/5000000000000 : ℝ)*(sp3) + (5677199581/100000000000000 : ℝ)*(sp5) + (30483996227/100000000000000 : ℝ)*(sp6) + (5326589733/50000000000000 : ℝ)*(sp7) + (1926933707614503/50000000000000 : ℝ)*(f.failure) + (1925067117812291/25000000000000 : ℝ)*(f.sum) + (1376046472727/628750000000000000000000000 : ℝ)*base66 + (4066888864550089917/251500000000000000000000000000000 : ℝ)*base68 + (4583439590935410083/251500000000000000000000000000000 : ℝ)*base69 + (1967840694768910083/251500000000000000000000000000000 : ℝ)*base71 + (163351879991/314375000000000000000000000 : ℝ)*base74 + (169821639064910083/251500000000000000000000000000000 : ℝ)*base75 + (3429257915412589917/251500000000000000000000000000000 : ℝ)*base78 + (573533091153089917/251500000000000000000000000000000 : ℝ)*base80 + (668274208927/2515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (663081/156250000000000000000 : ℝ)*base90 + (663081/156250000000000000000 : ℝ)*base92 + (663081/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1658898078590099481299135739/251500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2007713763/100000000000000 : ℝ)*(base19) + (932900567/50000000000000 : ℝ)*(base23) + (320991663/100000000000000 : ℝ)*(upper3) + (245734063/100000000000000 : ℝ)*(lower4) + (19104263/20000000000000 : ℝ)*(upper5) + (5807087495625679/100000000000000 : ℝ)*(major0) + (5807087495625679/100000000000000 : ℝ)*(major1) + (5807087495625679/100000000000000 : ℝ)*(major2) + (69498861261/100000000000000 : ℝ)*(sp1) + (70467020181/100000000000000 : ℝ)*(sp2) + (7740281502316257/100000000000000 : ℝ)*(sp4) + (7740209995741233/100000000000000 : ℝ)*(sp5) + (7740209169494943/100000000000000 : ℝ)*(sp6) + (1936946634533943/50000000000000 : ℝ)*(sp7) + (1936946634533943/50000000000000 : ℝ)*(f.failure) + (7740281502316257/100000000000000 : ℝ)*(f.sum) + (36819332584507/5030000000000000000000000000 : ℝ)*base66 + (2331704541773938087/503000000000000000000000000000000 : ℝ)*base67 + (11168639073715938087/503000000000000000000000000000000 : ℝ)*base69 + (5214117818962061913/503000000000000000000000000000000 : ℝ)*base72 + (31476808373007/5030000000000000000000000000 : ℝ)*base74 + (4898262503527938087/503000000000000000000000000000000 : ℝ)*base75 + (1227971835444061913/503000000000000000000000000000000 : ℝ)*base78 + (1228533368029938087/503000000000000000000000000000000 : ℝ)*base79 + (7107451597953/5030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (129539/156250000000000000000 : ℝ)*base89 + (129539/156250000000000000000 : ℝ)*base91 + (129539/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1164_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1164_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1164_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1164_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1164_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8219/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

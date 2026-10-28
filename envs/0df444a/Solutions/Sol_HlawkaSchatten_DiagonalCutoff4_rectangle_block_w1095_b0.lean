-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:39.648426+00:00
-- url     : https://prove2.me/submissions/63abeb3b-4f89-4fbd-9485-042c5fb1c12e

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
theorem support_rectangle_w1095_s0_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-381355151/2000000000 : ℝ)*x 0 + (758157127/1250000000 : ℝ)*x 1 + (477449943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381355151/2000000000 : ℝ)^259 ≤ (5534269071951/50000000000000 : ℝ)^195 := by
    have hnat : (381355151 : ℕ)^259*50000000000000^195 ≤ 5534269071951^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381355151 2000000000 5534269071951 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758157127/1250000000 : ℝ)^259 ≤ (51472967367213/100000000000000 : ℝ)^195 := by
    have hnat : (758157127 : ℕ)^259*100000000000000^195 ≤ 51472967367213^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758157127 1250000000 51472967367213 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477449943/1000000000 : ℝ)^259 ≤ (9364623618767/25000000000000 : ℝ)^195 := by
    have hnat : (477449943 : ℕ)^259*25000000000000^195 ≤ 9364623618767^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477449943 1000000000 9364623618767 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381355151/2000000000 : ℝ), (758157127/1250000000 : ℝ), (477449943/1000000000 : ℝ)] ![(5534269071951/50000000000000 : ℝ), (51472967367213/100000000000000 : ℝ), (9364623618767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381355151/2000000000 : ℝ)|^259 ≤ (5534269071951/50000000000000 : ℝ)^195
        have hw : |(-381355151/2000000000 : ℝ)|=(381355151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758157127/1250000000 : ℝ)|^259 ≤ (51472967367213/100000000000000 : ℝ)^195
        have hw : |(758157127/1250000000 : ℝ)|=(758157127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477449943/1000000000 : ℝ)|^259 ≤ (9364623618767/25000000000000 : ℝ)^195
        have hw : |(477449943/1000000000 : ℝ)|=(477449943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1103888129/2000000000 : ℝ)*x 0 + (-2648888191/10000000000 : ℝ)*x 1 + (4774499461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103888129/2000000000 : ℝ)^259 ≤ (9082673456297/20000000000000 : ℝ)^195 := by
    have hnat : (1103888129 : ℕ)^259*20000000000000^195 ≤ 9082673456297^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103888129 2000000000 9082673456297 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2648888191/10000000000 : ℝ)^259 ≤ (1070508619167/6250000000000 : ℝ)^195 := by
    have hnat : (2648888191 : ℕ)^259*6250000000000^195 ≤ 1070508619167^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648888191 10000000000 1070508619167 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774499461/10000000000 : ℝ)^259 ≤ (37458494798103/100000000000000 : ℝ)^195 := by
    have hnat : (4774499461 : ℕ)^259*100000000000000^195 ≤ 37458494798103^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774499461 10000000000 37458494798103 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103888129/2000000000 : ℝ), (-2648888191/10000000000 : ℝ), (4774499461/10000000000 : ℝ)] ![(9082673456297/20000000000000 : ℝ), (1070508619167/6250000000000 : ℝ), (37458494798103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103888129/2000000000 : ℝ)|^259 ≤ (9082673456297/20000000000000 : ℝ)^195
        have hw : |(1103888129/2000000000 : ℝ)|=(1103888129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2648888191/10000000000 : ℝ)|^259 ≤ (1070508619167/6250000000000 : ℝ)^195
        have hw : |(-2648888191/10000000000 : ℝ)|=(2648888191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774499461/10000000000 : ℝ)|^259 ≤ (37458494798103/100000000000000 : ℝ)^195
        have hw : |(4774499461/10000000000 : ℝ)|=(4774499461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2759720419/5000000000 : ℝ)*x 0 + (7639199/16000000 : ℝ)*x 1 + (-2648888049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759720419/5000000000 : ℝ)^259 ≤ (11353342347663/25000000000000 : ℝ)^195 := by
    have hnat : (2759720419 : ℕ)^259*25000000000000^195 ≤ 11353342347663^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759720419 5000000000 11353342347663 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7639199/16000000 : ℝ)^259 ≤ (18729246950971/50000000000000 : ℝ)^195 := by
    have hnat : (7639199 : ℕ)^259*50000000000000^195 ≤ 18729246950971^195*16000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7639199 16000000 18729246950971 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2648888049/10000000000 : ℝ)^259 ≤ (17128136687121/100000000000000 : ℝ)^195 := by
    have hnat : (2648888049 : ℕ)^259*100000000000000^195 ≤ 17128136687121^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648888049 10000000000 17128136687121 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759720419/5000000000 : ℝ), (7639199/16000000 : ℝ), (-2648888049/10000000000 : ℝ)] ![(11353342347663/25000000000000 : ℝ), (18729246950971/50000000000000 : ℝ), (17128136687121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759720419/5000000000 : ℝ)|^259 ≤ (11353342347663/25000000000000 : ℝ)^195
        have hw : |(2759720419/5000000000 : ℝ)|=(2759720419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7639199/16000000 : ℝ)|^259 ≤ (18729246950971/50000000000000 : ℝ)^195
        have hw : |(7639199/16000000 : ℝ)|=(7639199/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2648888049/10000000000 : ℝ)|^259 ≤ (17128136687121/100000000000000 : ℝ)^195
        have hw : |(-2648888049/10000000000 : ℝ)|=(2648888049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (262801211/625000000 : ℝ)*x 0 + (3123357273/10000000000 : ℝ)*x 1 + (1133526903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262801211/625000000 : ℝ)^259 ≤ (1265666499871/4000000000000 : ℝ)^195 := by
    have hnat : (262801211 : ℕ)^259*4000000000000^195 ≤ 1265666499871^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262801211 625000000 1265666499871 4000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123357273/10000000000 : ℝ)^259 ≤ (2664795686433/12500000000000 : ℝ)^195 := by
    have hnat : (3123357273 : ℕ)^259*12500000000000^195 ≤ 2664795686433^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123357273 10000000000 2664795686433 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133526903/2000000000 : ℝ)^259 ≤ (23519985998053/50000000000000 : ℝ)^195 := by
    have hnat : (1133526903 : ℕ)^259*50000000000000^195 ≤ 23519985998053^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133526903 2000000000 23519985998053 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262801211/625000000 : ℝ), (3123357273/10000000000 : ℝ), (1133526903/2000000000 : ℝ)] ![(1265666499871/4000000000000 : ℝ), (2664795686433/12500000000000 : ℝ), (23519985998053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262801211/625000000 : ℝ)|^259 ≤ (1265666499871/4000000000000 : ℝ)^195
        have hw : |(262801211/625000000 : ℝ)|=(262801211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123357273/10000000000 : ℝ)|^259 ≤ (2664795686433/12500000000000 : ℝ)^195
        have hw : |(3123357273/10000000000 : ℝ)|=(3123357273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133526903/2000000000 : ℝ)|^259 ≤ (23519985998053/50000000000000 : ℝ)^195
        have hw : |(1133526903/2000000000 : ℝ)|=(1133526903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912061857/10000000000 : ℝ)*x 0 + (2403908957/5000000000 : ℝ)*x 1 + (376923143/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912061857/10000000000 : ℝ)^259 ≤ (5554656326723/50000000000000 : ℝ)^195 := by
    have hnat : (1912061857 : ℕ)^259*50000000000000^195 ≤ 5554656326723^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912061857 10000000000 5554656326723 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403908957/5000000000 : ℝ)^259 ≤ (37806085971701/100000000000000 : ℝ)^195 := by
    have hnat : (2403908957 : ℕ)^259*100000000000000^195 ≤ 37806085971701^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403908957 5000000000 37806085971701 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376923143/625000000 : ℝ)^259 ≤ (51084601365863/100000000000000 : ℝ)^195 := by
    have hnat : (376923143 : ℕ)^259*100000000000000^195 ≤ 51084601365863^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376923143 625000000 51084601365863 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912061857/10000000000 : ℝ), (2403908957/5000000000 : ℝ), (376923143/625000000 : ℝ)] ![(5554656326723/50000000000000 : ℝ), (37806085971701/100000000000000 : ℝ), (51084601365863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912061857/10000000000 : ℝ)|^259 ≤ (5554656326723/50000000000000 : ℝ)^195
        have hw : |(-1912061857/10000000000 : ℝ)|=(1912061857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403908957/5000000000 : ℝ)|^259 ≤ (37806085971701/100000000000000 : ℝ)^195
        have hw : |(2403908957/5000000000 : ℝ)|=(2403908957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376923143/625000000 : ℝ)|^259 ≤ (51084601365863/100000000000000 : ℝ)^195
        have hw : |(376923143/625000000 : ℝ)|=(376923143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (323059539/625000000 : ℝ)*x 0 + (-696309593/5000000000 : ℝ)*x 1 + (6030770263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323059539/625000000 : ℝ)^259 ≤ (416236153367/1000000000000 : ℝ)^195 := by
    have hnat : (323059539 : ℕ)^259*1000000000000^195 ≤ 416236153367^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323059539 625000000 416236153367 1000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (696309593/5000000000 : ℝ)^259 ≤ (3645891776409/50000000000000 : ℝ)^195 := by
    have hnat : (696309593 : ℕ)^259*50000000000000^195 ≤ 3645891776409^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696309593 5000000000 3645891776409 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6030770263/10000000000 : ℝ)^259 ≤ (51084601084593/100000000000000 : ℝ)^195 := by
    have hnat : (6030770263 : ℕ)^259*100000000000000^195 ≤ 51084601084593^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6030770263 10000000000 51084601084593 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323059539/625000000 : ℝ), (-696309593/5000000000 : ℝ), (6030770263/10000000000 : ℝ)] ![(416236153367/1000000000000 : ℝ), (3645891776409/50000000000000 : ℝ), (51084601084593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323059539/625000000 : ℝ)|^259 ≤ (416236153367/1000000000000 : ℝ)^195
        have hw : |(323059539/625000000 : ℝ)|=(323059539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-696309593/5000000000 : ℝ)|^259 ≤ (3645891776409/50000000000000 : ℝ)^195
        have hw : |(-696309593/5000000000 : ℝ)|=(696309593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6030770263/10000000000 : ℝ)|^259 ≤ (51084601084593/100000000000000 : ℝ)^195
        have hw : |(6030770263/10000000000 : ℝ)|=(6030770263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5168953529/10000000000 : ℝ)*x 0 + (301538529/500000000 : ℝ)*x 1 + (-1392617283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168953529/10000000000 : ℝ)^259 ≤ (41623625016157/100000000000000 : ℝ)^195 := by
    have hnat : (5168953529 : ℕ)^259*100000000000000^195 ≤ 41623625016157^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168953529 10000000000 41623625016157 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301538529/500000000 : ℝ)^259 ≤ (3192787790693/6250000000000 : ℝ)^195 := by
    have hnat : (301538529 : ℕ)^259*6250000000000^195 ≤ 3192787790693^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301538529 500000000 3192787790693 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392617283/10000000000 : ℝ)^259 ≤ (1822942579597/25000000000000 : ℝ)^195 := by
    have hnat : (1392617283 : ℕ)^259*25000000000000^195 ≤ 1822942579597^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392617283 10000000000 1822942579597 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168953529/10000000000 : ℝ), (301538529/500000000 : ℝ), (-1392617283/10000000000 : ℝ)] ![(41623625016157/100000000000000 : ℝ), (3192787790693/6250000000000 : ℝ), (1822942579597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168953529/10000000000 : ℝ)|^259 ≤ (41623625016157/100000000000000 : ℝ)^195
        have hw : |(5168953529/10000000000 : ℝ)|=(5168953529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301538529/500000000 : ℝ)|^259 ≤ (3192787790693/6250000000000 : ℝ)^195
        have hw : |(301538529/500000000 : ℝ)|=(301538529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1392617283/10000000000 : ℝ)|^259 ≤ (1822942579597/25000000000000 : ℝ)^195
        have hw : |(-1392617283/10000000000 : ℝ)|=(1392617283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s0_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (210761819/500000000 : ℝ)*x 0 + (700244849/1250000000 : ℝ)*x 1 + (3191335521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210761819/500000000 : ℝ)^259 ≤ (15872910695439/50000000000000 : ℝ)^195 := by
    have hnat : (210761819 : ℕ)^259*50000000000000^195 ≤ 15872910695439^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210761819 500000000 15872910695439 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700244849/1250000000 : ℝ)^259 ≤ (926347157751/2000000000000 : ℝ)^195 := by
    have hnat : (700244849 : ℕ)^259*2000000000000^195 ≤ 926347157751^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700244849 1250000000 926347157751 2000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191335521/10000000000 : ℝ)^259 ≤ (2193682071127/10000000000000 : ℝ)^195 := by
    have hnat : (3191335521 : ℕ)^259*10000000000000^195 ≤ 2193682071127^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191335521 10000000000 2193682071127 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210761819/500000000 : ℝ), (700244849/1250000000 : ℝ), (3191335521/10000000000 : ℝ)] ![(15872910695439/50000000000000 : ℝ), (926347157751/2000000000000 : ℝ), (2193682071127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210761819/500000000 : ℝ)|^259 ≤ (15872910695439/50000000000000 : ℝ)^195
        have hw : |(210761819/500000000 : ℝ)|=(210761819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(700244849/1250000000 : ℝ)|^259 ≤ (926347157751/2000000000000 : ℝ)^195
        have hw : |(700244849/1250000000 : ℝ)|=(700244849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191335521/10000000000 : ℝ)|^259 ≤ (2193682071127/10000000000000 : ℝ)^195
        have hw : |(3191335521/10000000000 : ℝ)|=(3191335521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (109/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/25000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8287/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8287 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8287*1^2048 ≤ 0^2048*1^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8287/2048 : ℝ) ≤ (2453470463646817237/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8287 ≤ (2453470463646817237/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8287*100000000000000000000^2048 ≤ 2453470463646817237^2048*5^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2453470463646817237 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2453470463646817237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8287 := by
      have hnat : (1 : ℕ)^2048*1^8287 ≤ 1^8287*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102453470463646817237/100000000000000000000 : ℝ) ≤ (10060081515443761/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (102453470463646817237/100000000000000000000 : ℝ)^2048 ≤ (10060081515443761/10000000000000000 : ℝ)^8287 := by
      have hnat : (102453470463646817237 : ℕ)^2048*10000000000000000^8287 ≤ 10060081515443761^8287*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102453470463646817237 100000000000000000000 10060081515443761 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060081515443761/10000000000000000 : ℝ)) (X := (102453470463646817237/100000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52453470463646817237/50000000000000000000 : ℝ) ≤ (5060081515443761/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (52453470463646817237/50000000000000000000 : ℝ)^2048 ≤ (5060081515443761/5000000000000000 : ℝ)^8287 := by
      have hnat : (52453470463646817237 : ℕ)^2048*5000000000000000^8287 ≤ 5060081515443761^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52453470463646817237 50000000000000000000 5060081515443761 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060081515443761/5000000000000000 : ℝ)) (X := (52453470463646817237/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60081515443761/4000000000000000 : ℝ)*(0 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60081515443761/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2453470463646817237/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60081515443761/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60081515443761/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060081515443761/10000000000000000 : ℝ) by norm_num, show 1+(2453470463646817237/100000000000000000000 : ℝ)+(0 : ℝ)=(102453470463646817237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2453470463646817237/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60081515443761/4000000000000000 : ℝ)*(2/5 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60081515443761/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060081515443761/5000000000000000 : ℝ) by norm_num, show 1+2*(2453470463646817237/100000000000000000000 : ℝ)=(52453470463646817237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60081515443761/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60081515443761/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60081515443761/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60081515443761/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60081515443761/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60081515443761/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-381355151/2000000000 : ℝ)*X 0 0+(758157127/1250000000 : ℝ)*X 0 1+(477449943/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103888129/2000000000 : ℝ)*X 1 0+(-2648888191/10000000000 : ℝ)*X 1 1+(4774499461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759720419/5000000000 : ℝ)*X 2 0+(7639199/16000000 : ℝ)*X 2 1+(-2648888049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262801211/625000000 : ℝ)*X 0 0+(3123357273/10000000000 : ℝ)*X 0 1+(1133526903/2000000000 : ℝ)*X 0 2+(262801211/625000000 : ℝ)*X 1 0+(3123357273/10000000000 : ℝ)*X 1 1+(1133526903/2000000000 : ℝ)*X 1 2+(262801211/625000000 : ℝ)*X 2 0+(3123357273/10000000000 : ℝ)*X 2 1+(1133526903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1912061857/10000000000 : ℝ)*X 0 0+(2403908957/5000000000 : ℝ)*X 0 1+(376923143/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323059539/625000000 : ℝ)*X 1 0+(-696309593/5000000000 : ℝ)*X 1 1+(6030770263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168953529/10000000000 : ℝ)*X 2 0+(301538529/500000000 : ℝ)*X 2 1+(-1392617283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210761819/500000000 : ℝ)*X 0 0+(700244849/1250000000 : ℝ)*X 0 1+(3191335521/10000000000 : ℝ)*X 0 2+(210761819/500000000 : ℝ)*X 1 0+(700244849/1250000000 : ℝ)*X 1 1+(3191335521/10000000000 : ℝ)*X 1 2+(210761819/500000000 : ℝ)*X 2 0+(700244849/1250000000 : ℝ)*X 2 1+(3191335521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (358501979905731606215613/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13600621/20000000000000 : ℝ)*(base1) + (362705509/20000000000000 : ℝ)*(base19) + (340620067/20000000000000 : ℝ)*(base23) + (68759013/50000000000000 : ℝ)*(base24) + (415608513/100000000000000 : ℝ)*(upper3) + (583896540689489/100000000000000 : ℝ)*(major0) + (583896540689489/100000000000000 : ℝ)*(major1) + (583896540689489/100000000000000 : ℝ)*(major2) + (387372405706429/50000000000000 : ℝ)*(sp0) + (24210841428399/3125000000000 : ℝ)*(sp1) + (24210840581811/3125000000000 : ℝ)*(sp2) + (49130101851767/12500000000000 : ℝ)*(sp3) + (3995826559/100000000000000 : ℝ)*(sp4) + (3220324099/100000000000000 : ℝ)*(sp7) + (19652205157067/5000000000000 : ℝ)*(f.failure) + (96843592404539/12500000000000 : ℝ)*(f.sum) + (395308162728129/200000000000000000000000000000 : ℝ)*base65 + (1854237067328129/400000000000000000000000000000 : ℝ)*base67 + (1033018922928129/400000000000000000000000000000 : ℝ)*base69 + (588850296928129/400000000000000000000000000000 : ℝ)*base71 + (668292573728129/200000000000000000000000000000 : ℝ)*base73 + (496910723471871/400000000000000000000000000000 : ℝ)*base76 + (390190930528129/400000000000000000000000000000 : ℝ)*base77 + (39159071071871/400000000000000000000000000000 : ℝ)*base80 + (335514949128129/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (282837/62500000000000000000 : ℝ)*base90 + (282837/62500000000000000000 : ℝ)*base92 + (282837/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557056862479420307912511/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97729257/100000000000000 : ℝ)*(base19) + (356955561/50000000000000 : ℝ)*(base23) + (86776437/20000000000000 : ℝ)*(base39) + (36746759/100000000000000 : ℝ)*(base45) + (2040769/20000000000000 : ℝ)*(upper2) + (62537521/25000000000000 : ℝ)*(upper5) + (616260776602551/100000000000000 : ℝ)*(major0) + (616260776602551/100000000000000 : ℝ)*(major1) + (308130171360183/50000000000000 : ℝ)*(major2) + (471972491/100000000000000 : ℝ)*(sp2) + (5110570389791/625000000000 : ℝ)*(sp4) + (817691164637303/100000000000000 : ℝ)*(sp5) + (204422627591283/25000000000000 : ℝ)*(sp6) + (82965952822709/20000000000000 : ℝ)*(sp7) + (82965952822709/20000000000000 : ℝ)*(f.failure) + (163538339249749/20000000000000 : ℝ)*(f.sum) + (330574960029163/400000000000000000000000000000 : ℝ)*base66 + (582028484831737/200000000000000000000000000000 : ℝ)*base68 + (776030199634311/400000000000000000000000000000 : ℝ)*base69 + (221310176768263/200000000000000000000000000000 : ℝ)*base71 + (1211965800829163/400000000000000000000000000000 : ℝ)*base74 + (175969636034311/400000000000000000000000000000 : ℝ)*base75 + (434348535234311/400000000000000000000000000000 : ℝ)*base77 + (52228240365689/400000000000000000000000000000 : ℝ)*base80 + (265628416365689/200000000000000000000000000000 : ℝ)*base82 + (767501/250000000000000000000 : ℝ)*base89 + (767501/250000000000000000000 : ℝ)*base91 + (767501/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1095_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s1_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114832651/10000000000 : ℝ)*x 0 + (5714255969/10000000000 : ℝ)*x 1 + (998455783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114832651/10000000000 : ℝ)^259 ≤ (2540142774857/20000000000000 : ℝ)^195 := by
    have hnat : (2114832651 : ℕ)^259*20000000000000^195 ≤ 2540142774857^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114832651 10000000000 2540142774857 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5714255969/10000000000 : ℝ)^259 ≤ (11888652236871/25000000000000 : ℝ)^195 := by
    have hnat : (5714255969 : ℕ)^259*25000000000000^195 ≤ 11888652236871^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714255969 10000000000 11888652236871 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998455783/2000000000 : ℝ)^259 ≤ (9936169287659/25000000000000 : ℝ)^195 := by
    have hnat : (998455783 : ℕ)^259*25000000000000^195 ≤ 9936169287659^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998455783 2000000000 9936169287659 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114832651/10000000000 : ℝ), (5714255969/10000000000 : ℝ), (998455783/2000000000 : ℝ)] ![(2540142774857/20000000000000 : ℝ), (11888652236871/25000000000000 : ℝ), (9936169287659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114832651/10000000000 : ℝ)|^259 ≤ (2540142774857/20000000000000 : ℝ)^195
        have hw : |(-2114832651/10000000000 : ℝ)|=(2114832651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5714255969/10000000000 : ℝ)|^259 ≤ (11888652236871/25000000000000 : ℝ)^195
        have hw : |(5714255969/10000000000 : ℝ)|=(5714255969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998455783/2000000000 : ℝ)|^259 ≤ (9936169287659/25000000000000 : ℝ)^195
        have hw : |(998455783/2000000000 : ℝ)|=(998455783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (169428391/312500000 : ℝ)*x 0 + (-2505398893/10000000000 : ℝ)*x 1 + (312017443/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169428391/312500000 : ℝ)^259 ≤ (22174217091701/50000000000000 : ℝ)^195 := by
    have hnat : (169428391 : ℕ)^259*50000000000000^195 ≤ 22174217091701^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169428391 312500000 22174217091701 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2505398893/10000000000 : ℝ)^259 ≤ (15906886816743/100000000000000 : ℝ)^195 := by
    have hnat : (2505398893 : ℕ)^259*100000000000000^195 ≤ 15906886816743^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505398893 10000000000 15906886816743 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312017443/625000000 : ℝ)^259 ≤ (39744678979963/100000000000000 : ℝ)^195 := by
    have hnat : (312017443 : ℕ)^259*100000000000000^195 ≤ 39744678979963^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312017443 625000000 39744678979963 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169428391/312500000 : ℝ), (-2505398893/10000000000 : ℝ), (312017443/625000000 : ℝ)] ![(22174217091701/50000000000000 : ℝ), (15906886816743/100000000000000 : ℝ), (39744678979963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169428391/312500000 : ℝ)|^259 ≤ (22174217091701/50000000000000 : ℝ)^195
        have hw : |(169428391/312500000 : ℝ)|=(169428391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2505398893/10000000000 : ℝ)|^259 ≤ (15906886816743/100000000000000 : ℝ)^195
        have hw : |(-2505398893/10000000000 : ℝ)|=(2505398893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312017443/625000000 : ℝ)|^259 ≤ (39744678979963/100000000000000 : ℝ)^195
        have hw : |(312017443/625000000 : ℝ)|=(312017443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2710854749/5000000000 : ℝ)*x 0 + (4992278099/10000000000 : ℝ)*x 1 + (-156587429/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710854749/5000000000 : ℝ)^259 ≤ (22174222447869/50000000000000 : ℝ)^195 := by
    have hnat : (2710854749 : ℕ)^259*50000000000000^195 ≤ 22174222447869^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710854749 5000000000 22174222447869 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992278099/10000000000 : ℝ)^259 ≤ (19872334261067/50000000000000 : ℝ)^195 := by
    have hnat : (4992278099 : ℕ)^259*50000000000000^195 ≤ 19872334261067^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992278099 10000000000 19872334261067 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156587429/625000000 : ℝ)^259 ≤ (15906886572191/100000000000000 : ℝ)^195 := by
    have hnat : (156587429 : ℕ)^259*100000000000000^195 ≤ 15906886572191^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156587429 625000000 15906886572191 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710854749/5000000000 : ℝ), (4992278099/10000000000 : ℝ), (-156587429/625000000 : ℝ)] ![(22174222447869/50000000000000 : ℝ), (19872334261067/50000000000000 : ℝ), (15906886572191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710854749/5000000000 : ℝ)|^259 ≤ (22174222447869/50000000000000 : ℝ)^195
        have hw : |(2710854749/5000000000 : ℝ)|=(2710854749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992278099/10000000000 : ℝ)|^259 ≤ (19872334261067/50000000000000 : ℝ)^195
        have hw : |(4992278099/10000000000 : ℝ)|=(4992278099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156587429/625000000 : ℝ)|^259 ≤ (15906886572191/100000000000000 : ℝ)^195
        have hw : |(-156587429/625000000 : ℝ)|=(156587429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1080348079/2500000000 : ℝ)*x 0 + (733626239/2000000000 : ℝ)*x 1 + (636406867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080348079/2500000000 : ℝ)^259 ≤ (8203015501633/25000000000000 : ℝ)^195 := by
    have hnat : (1080348079 : ℕ)^259*25000000000000^195 ≤ 8203015501633^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080348079 2500000000 8203015501633 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733626239/2000000000 : ℝ)^259 ≤ (26393283935457/100000000000000 : ℝ)^195 := by
    have hnat : (733626239 : ℕ)^259*100000000000000^195 ≤ 26393283935457^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733626239 2000000000 26393283935457 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636406867/1250000000 : ℝ)^259 ≤ (509933175611/1250000000000 : ℝ)^195 := by
    have hnat : (636406867 : ℕ)^259*1250000000000^195 ≤ 509933175611^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636406867 1250000000 509933175611 1250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080348079/2500000000 : ℝ), (733626239/2000000000 : ℝ), (636406867/1250000000 : ℝ)] ![(8203015501633/25000000000000 : ℝ), (26393283935457/100000000000000 : ℝ), (509933175611/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080348079/2500000000 : ℝ)|^259 ≤ (8203015501633/25000000000000 : ℝ)^195
        have hw : |(1080348079/2500000000 : ℝ)|=(1080348079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733626239/2000000000 : ℝ)|^259 ≤ (26393283935457/100000000000000 : ℝ)^195
        have hw : |(733626239/2000000000 : ℝ)|=(733626239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(636406867/1250000000 : ℝ)|^259 ≤ (509933175611/1250000000000 : ℝ)^195
        have hw : |(636406867/1250000000 : ℝ)|=(636406867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-528926683/2500000000 : ℝ)*x 0 + (5002315149/10000000000 : ℝ)*x 1 + (2852008973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528926683/2500000000 : ℝ)^259 ≤ (12707686533029/100000000000000 : ℝ)^195 := by
    have hnat : (528926683 : ℕ)^259*100000000000000^195 ≤ 12707686533029^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528926683 2500000000 12707686533029 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002315149/10000000000 : ℝ)^259 ≤ (39850836745161/100000000000000 : ℝ)^195 := by
    have hnat : (5002315149 : ℕ)^259*100000000000000^195 ≤ 39850836745161^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002315149 10000000000 39850836745161 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852008973/5000000000 : ℝ)^259 ≤ (11860369174807/25000000000000 : ℝ)^195 := by
    have hnat : (2852008973 : ℕ)^259*25000000000000^195 ≤ 11860369174807^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852008973 5000000000 11860369174807 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528926683/2500000000 : ℝ), (5002315149/10000000000 : ℝ), (2852008973/5000000000 : ℝ)] ![(12707686533029/100000000000000 : ℝ), (39850836745161/100000000000000 : ℝ), (11860369174807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528926683/2500000000 : ℝ)|^259 ≤ (12707686533029/100000000000000 : ℝ)^195
        have hw : |(-528926683/2500000000 : ℝ)|=(528926683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002315149/10000000000 : ℝ)|^259 ≤ (39850836745161/100000000000000 : ℝ)^195
        have hw : |(5002315149/10000000000 : ℝ)|=(5002315149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852008973/5000000000 : ℝ)|^259 ≤ (11860369174807/25000000000000 : ℝ)^195
        have hw : |(2852008973/5000000000 : ℝ)|=(2852008973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (327315539/625000000 : ℝ)*x 0 + (-896829879/5000000000 : ℝ)*x 1 + (2852008891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327315539/625000000 : ℝ)^259 ≤ (42353508236337/100000000000000 : ℝ)^195 := by
    have hnat : (327315539 : ℕ)^259*100000000000000^195 ≤ 42353508236337^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327315539 625000000 42353508236337 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896829879/5000000000 : ℝ)^259 ≤ (5102508432351/50000000000000 : ℝ)^195 := by
    have hnat : (896829879 : ℕ)^259*50000000000000^195 ≤ 5102508432351^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896829879 5000000000 5102508432351 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852008891/5000000000 : ℝ)^259 ≤ (47441474887527/100000000000000 : ℝ)^195 := by
    have hnat : (2852008891 : ℕ)^259*100000000000000^195 ≤ 47441474887527^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852008891 5000000000 47441474887527 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327315539/625000000 : ℝ), (-896829879/5000000000 : ℝ), (2852008891/5000000000 : ℝ)] ![(42353508236337/100000000000000 : ℝ), (5102508432351/50000000000000 : ℝ), (47441474887527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327315539/625000000 : ℝ)|^259 ≤ (42353508236337/100000000000000 : ℝ)^195
        have hw : |(327315539/625000000 : ℝ)|=(327315539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-896829879/5000000000 : ℝ)|^259 ≤ (5102508432351/50000000000000 : ℝ)^195
        have hw : |(-896829879/5000000000 : ℝ)|=(896829879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852008891/5000000000 : ℝ)|^259 ≤ (47441474887527/100000000000000 : ℝ)^195
        have hw : |(2852008891/5000000000 : ℝ)|=(2852008891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1309262161/2500000000 : ℝ)*x 0 + (5704017907/10000000000 : ℝ)*x 1 + (-896829773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309262161/2500000000 : ℝ)^259 ≤ (1323547139099/3125000000000 : ℝ)^195 := by
    have hnat : (1309262161 : ℕ)^259*3125000000000^195 ≤ 1323547139099^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309262161 2500000000 1323547139099 3125000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704017907/10000000000 : ℝ)^259 ≤ (11860369067099/25000000000000 : ℝ)^195 := by
    have hnat : (5704017907 : ℕ)^259*25000000000000^195 ≤ 11860369067099^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704017907 10000000000 11860369067099 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896829773/5000000000 : ℝ)^259 ≤ (10205015262657/100000000000000 : ℝ)^195 := by
    have hnat : (896829773 : ℕ)^259*100000000000000^195 ≤ 10205015262657^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896829773 5000000000 10205015262657 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309262161/2500000000 : ℝ), (5704017907/10000000000 : ℝ), (-896829773/5000000000 : ℝ)] ![(1323547139099/3125000000000 : ℝ), (11860369067099/25000000000000 : ℝ), (10205015262657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309262161/2500000000 : ℝ)|^259 ≤ (1323547139099/3125000000000 : ℝ)^195
        have hw : |(1309262161/2500000000 : ℝ)|=(1309262161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704017907/10000000000 : ℝ)|^259 ≤ (11860369067099/25000000000000 : ℝ)^195
        have hw : |(5704017907/10000000000 : ℝ)|=(5704017907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896829773/5000000000 : ℝ)|^259 ≤ (10205015262657/100000000000000 : ℝ)^195
        have hw : |(-896829773/5000000000 : ℝ)|=(896829773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s1_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (864622859/2000000000 : ℝ)*x 0 + (5071472771/10000000000 : ℝ)*x 1 + (3688311129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864622859/2000000000 : ℝ)^259 ≤ (6565885852677/20000000000000 : ℝ)^195 := by
    have hnat : (864622859 : ℕ)^259*20000000000000^195 ≤ 6565885852677^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864622859 2000000000 6565885852677 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071472771/10000000000 : ℝ)^259 ≤ (8116851352241/20000000000000 : ℝ)^195 := by
    have hnat : (5071472771 : ℕ)^259*20000000000000^195 ≤ 8116851352241^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071472771 10000000000 8116851352241 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688311129/10000000000 : ℝ)^259 ≤ (1661644623039/6250000000000 : ℝ)^195 := by
    have hnat : (3688311129 : ℕ)^259*6250000000000^195 ≤ 1661644623039^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688311129 10000000000 1661644623039 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864622859/2000000000 : ℝ), (5071472771/10000000000 : ℝ), (3688311129/10000000000 : ℝ)] ![(6565885852677/20000000000000 : ℝ), (8116851352241/20000000000000 : ℝ), (1661644623039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864622859/2000000000 : ℝ)|^259 ≤ (6565885852677/20000000000000 : ℝ)^195
        have hw : |(864622859/2000000000 : ℝ)|=(864622859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071472771/10000000000 : ℝ)|^259 ≤ (8116851352241/20000000000000 : ℝ)^195
        have hw : |(5071472771/10000000000 : ℝ)|=(5071472771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688311129/10000000000 : ℝ)|^259 ≤ (1661644623039/6250000000000 : ℝ)^195
        have hw : |(3688311129/10000000000 : ℝ)|=(3688311129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10327/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/50000 : ℝ) ^ (8287/2048 : ℝ) ≤ (1699674287/100000000000000000000 : ℝ) := by
    have hpowers : (109/50000 : ℝ)^8287 ≤ (1699674287/100000000000000000000 : ℝ)^2048 := by
      have hnat : (109 : ℕ)^8287*100000000000000000000^2048 ≤ 1699674287^2048*50000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 50000 1699674287 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/50000 : ℝ)) (X := (1699674287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/25000 : ℝ) ^ (8287/2048 : ℝ) ≤ (144769323507493749/25000000000000000000 : ℝ) := by
    have hpowers : (6999/25000 : ℝ)^8287 ≤ (144769323507493749/25000000000000000000 : ℝ)^2048 := by
      have hnat : (6999 : ℕ)^8287*25000000000000000000^2048 ≤ 144769323507493749^2048*25000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 25000 144769323507493749 25000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/25000 : ℝ)) (X := (144769323507493749/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000001699674287/50000000000000000000 : ℝ) ≤ (1000000000008401/1000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50000000001699674287/50000000000000000000 : ℝ)^2048 ≤ (1000000000008401/1000000000000000 : ℝ)^8287 := by
      have hnat : (50000000001699674287 : ℕ)^2048*1000000000000000^8287 ≤ 1000000000008401^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000001699674287 50000000000000000000 1000000000008401 1000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000008401/1000000000000000 : ℝ)) (X := (50000000001699674287/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100579077295729649283/100000000000000000000 : ℝ) ≤ (10014279882158847/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (100579077295729649283/100000000000000000000 : ℝ)^2048 ≤ (10014279882158847/10000000000000000 : ℝ)^8287 := by
      have hnat : (100579077295729649283 : ℕ)^2048*10000000000000000^8287 ≤ 10014279882158847^8287*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100579077295729649283 100000000000000000000 10014279882158847 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014279882158847/10000000000000000 : ℝ)) (X := (100579077295729649283/100000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12644769323507493749/12500000000000000000 : ℝ) ≤ (2507139941058421/2500000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (12644769323507493749/12500000000000000000 : ℝ)^2048 ≤ (2507139941058421/2500000000000000 : ℝ)^8287 := by
      have hnat : (12644769323507493749 : ℕ)^2048*2500000000000000^8287 ≤ 2507139941058421^8287*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12644769323507493749 12500000000000000000 2507139941058421 2500000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507139941058421/2500000000000000 : ℝ)) (X := (12644769323507493749/12500000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1699674287/100000000000000000000 : ℝ) ≤ ((17360860873359312553/17361250000000000000 : ℝ)+2*(14279882074837/2777800000000000 : ℝ)*(109/50000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (17360860873359312553/17361250000000000000 : ℝ)+2*(14279882074837/2777800000000000 : ℝ)*(109/50000 : ℝ)=(1000000000008401/1000000000000000 : ℝ) by norm_num, show 1+2*(1699674287/100000000000000000000 : ℝ)=(50000000001699674287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(144769323507493749/25000000000000000000 : ℝ)+(1699674287/100000000000000000000 : ℝ) ≤ ((17360860873359312553/17361250000000000000 : ℝ)+(14279882074837/2777800000000000 : ℝ)*((6999/25000 : ℝ)+(109/50000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (17360860873359312553/17361250000000000000 : ℝ)+(14279882074837/2777800000000000 : ℝ)*((6999/25000 : ℝ)+(109/50000 : ℝ))=(10014279882158847/10000000000000000 : ℝ) by norm_num, show 1+(144769323507493749/25000000000000000000 : ℝ)+(1699674287/100000000000000000000 : ℝ)=(100579077295729649283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(144769323507493749/25000000000000000000 : ℝ) ≤ ((17360860873359312553/17361250000000000000 : ℝ)+2*(14279882074837/2777800000000000 : ℝ)*(6999/25000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (17360860873359312553/17361250000000000000 : ℝ)+2*(14279882074837/2777800000000000 : ℝ)*(6999/25000 : ℝ)=(2507139941058421/2500000000000000 : ℝ) by norm_num, show 1+2*(144769323507493749/25000000000000000000 : ℝ)=(12644769323507493749/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17360860873359312553/17361250000000000000 : ℝ)*(X 1 0+X 2 0)+(14279882074837/2777800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (109/50000 : ℝ)) (hi := (6999/25000 : ℝ)) (c := (17360860873359312553/17361250000000000000 : ℝ)) (alpha := (14279882074837/2777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17360860873359312553/17361250000000000000 : ℝ)*(X 0 1+X 2 1)+(14279882074837/2777800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (109/50000 : ℝ)) (hi := (6999/25000 : ℝ)) (c := (17360860873359312553/17361250000000000000 : ℝ)) (alpha := (14279882074837/2777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17360860873359312553/17361250000000000000 : ℝ)*(X 0 2+X 1 2)+(14279882074837/2777800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (109/50000 : ℝ)) (hi := (6999/25000 : ℝ)) (c := (17360860873359312553/17361250000000000000 : ℝ)) (alpha := (14279882074837/2777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114832651/10000000000 : ℝ)*X 0 0+(5714255969/10000000000 : ℝ)*X 0 1+(998455783/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((169428391/312500000 : ℝ)*X 1 0+(-2505398893/10000000000 : ℝ)*X 1 1+(312017443/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710854749/5000000000 : ℝ)*X 2 0+(4992278099/10000000000 : ℝ)*X 2 1+(-156587429/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080348079/2500000000 : ℝ)*X 0 0+(733626239/2000000000 : ℝ)*X 0 1+(636406867/1250000000 : ℝ)*X 0 2+(1080348079/2500000000 : ℝ)*X 1 0+(733626239/2000000000 : ℝ)*X 1 1+(636406867/1250000000 : ℝ)*X 1 2+(1080348079/2500000000 : ℝ)*X 2 0+(733626239/2000000000 : ℝ)*X 2 1+(636406867/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528926683/2500000000 : ℝ)*X 0 0+(5002315149/10000000000 : ℝ)*X 0 1+(2852008973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327315539/625000000 : ℝ)*X 1 0+(-896829879/5000000000 : ℝ)*X 1 1+(2852008891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309262161/2500000000 : ℝ)*X 2 0+(5704017907/10000000000 : ℝ)*X 2 1+(-896829773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864622859/2000000000 : ℝ)*X 0 0+(5071472771/10000000000 : ℝ)*X 0 1+(3688311129/10000000000 : ℝ)*X 0 2+(864622859/2000000000 : ℝ)*X 1 0+(5071472771/10000000000 : ℝ)*X 1 1+(3688311129/10000000000 : ℝ)*X 1 2+(864622859/2000000000 : ℝ)*X 2 0+(5071472771/10000000000 : ℝ)*X 2 1+(3688311129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (670257132862044130094598741/86806250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195725657/100000000000000 : ℝ)*(base1) + (1549790579/100000000000000 : ℝ)*(base19) + (1801686643/100000000000000 : ℝ)*(base23) + (7656493/6250000000000 : ℝ)*(upper3) + (40134099/20000000000000 : ℝ)*(upper5) + (104389343183467/10000000000000 : ℝ)*(major0) + (104389343183467/10000000000000 : ℝ)*(major1) + (104389343183467/10000000000000 : ℝ)*(major2) + (1385092256019027/100000000000000 : ℝ)*(sp0) + (1385098657288099/100000000000000 : ℝ)*(sp1) + (346274601348009/25000000000000 : ℝ)*(sp2) + (140536577311157/20000000000000 : ℝ)*(sp3) + (2036696327/25000000000000 : ℝ)*(sp4) + (663386507/20000000000000 : ℝ)*(sp7) + (87835799901747/12500000000000 : ℝ)*(f.failure) + (692550103539339/50000000000000 : ℝ)*(f.sum) + (38646976412549/13889000000000000000000000000 : ℝ)*base66 + (756494160527717501/173612500000000000000000000000000 : ℝ)*base67 + (898149940813505001/173612500000000000000000000000000 : ℝ)*base69 + (754972627869442501/173612500000000000000000000000000 : ℝ)*base71 + (13793939116069/6944500000000000000000000000 : ℝ)*base74 + (1582717806375117501/173612500000000000000000000000000 : ℝ)*base75 + (961543856814942501/173612500000000000000000000000000 : ℝ)*base77 + (450855168733955001/173612500000000000000000000000000 : ℝ)*base79 + (178038254117/173612500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (471683/156250000000000000000 : ℝ)*base89 + (471683/156250000000000000000 : ℝ)*base91 + (471683/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7507941422655008012198611251/868062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20162761/20000000000000 : ℝ)*(base1) + (481486273/25000000000000 : ℝ)*(base19) + (973149321/50000000000000 : ℝ)*(base23) + (98252553/50000000000000 : ℝ)*(upper3) + (49205567/25000000000000 : ℝ)*(upper5) + (1074043216131989/100000000000000 : ℝ)*(major0) + (1074043216131989/100000000000000 : ℝ)*(major1) + (1074043216131989/100000000000000 : ℝ)*(major2) + (7727574643/100000000000000 : ℝ)*(sp1) + (8150420149/100000000000000 : ℝ)*(sp2) + (285020964099099/20000000000000 : ℝ)*(sp4) + (356273766540489/25000000000000 : ℝ)*(sp5) + (14250946229629/1000000000000 : ℝ)*(sp6) + (72298132346583/10000000000000 : ℝ)*(sp7) + (361490712139817/50000000000000 : ℝ)*(f.failure) + (142510471968169/10000000000000 : ℝ)*(f.sum) + (138390930803107/138890000000000000000000000000 : ℝ)*base66 + (1458704710113110833/1736125000000000000000000000000000 : ℝ)*base68 + (8127297923475014167/1736125000000000000000000000000000 : ℝ)*base69 + (5895165418528735833/1736125000000000000000000000000000 : ℝ)*base72 + (168665612712923/138890000000000000000000000000 : ℝ)*base73 + (3558313618420764167/1736125000000000000000000000000000 : ℝ)*base75 + (8554514891070985833/1736125000000000000000000000000000 : ℝ)*base78 + (5231153806131110833/1736125000000000000000000000000000 : ℝ)*base80 + (895756172307533/138890000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5043087/625000000000000000000 : ℝ)*base90 + (5043087/625000000000000000000 : ℝ)*base92 + (5043087/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1095_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10327/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s2_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-135664091/625000000 : ℝ)*x 0 + (5519998853/10000000000 : ℝ)*x 1 + (2575554041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135664091/625000000 : ℝ)^259 ≤ (6573832824991/50000000000000 : ℝ)^195 := by
    have hnat : (135664091 : ℕ)^259*50000000000000^195 ≤ 6573832824991^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135664091 625000000 6573832824991 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519998853/10000000000 : ℝ)^259 ≤ (4541946766381/10000000000000 : ℝ)^195 := by
    have hnat : (5519998853 : ℕ)^259*10000000000000^195 ≤ 4541946766381^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519998853 10000000000 4541946766381 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575554041/5000000000 : ℝ)^259 ≤ (8286573334287/20000000000000 : ℝ)^195 := by
    have hnat : (2575554041 : ℕ)^259*20000000000000^195 ≤ 8286573334287^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575554041 5000000000 8286573334287 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135664091/625000000 : ℝ), (5519998853/10000000000 : ℝ), (2575554041/5000000000 : ℝ)] ![(6573832824991/50000000000000 : ℝ), (4541946766381/10000000000000 : ℝ), (8286573334287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135664091/625000000 : ℝ)|^259 ≤ (6573832824991/50000000000000 : ℝ)^195
        have hw : |(-135664091/625000000 : ℝ)|=(135664091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519998853/10000000000 : ℝ)|^259 ≤ (4541946766381/10000000000000 : ℝ)^195
        have hw : |(5519998853/10000000000 : ℝ)|=(5519998853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575554041/5000000000 : ℝ)|^259 ≤ (8286573334287/20000000000000 : ℝ)^195
        have hw : |(2575554041/5000000000 : ℝ)|=(2575554041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5375913091/10000000000 : ℝ)*x 0 + (-2362774113/10000000000 : ℝ)*x 1 + (2575554567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375913091/10000000000 : ℝ)^259 ≤ (43851583618701/100000000000000 : ℝ)^195 := by
    have hnat : (5375913091 : ℕ)^259*100000000000000^195 ≤ 43851583618701^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375913091 10000000000 43851583618701 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2362774113/10000000000 : ℝ)^259 ≤ (147155384609/1000000000000 : ℝ)^195 := by
    have hnat : (2362774113 : ℕ)^259*1000000000000^195 ≤ 147155384609^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362774113 10000000000 147155384609 1000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575554567/5000000000 : ℝ)^259 ≤ (10358219477593/25000000000000 : ℝ)^195 := by
    have hnat : (2575554567 : ℕ)^259*25000000000000^195 ≤ 10358219477593^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575554567 5000000000 10358219477593 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375913091/10000000000 : ℝ), (-2362774113/10000000000 : ℝ), (2575554567/5000000000 : ℝ)] ![(43851583618701/100000000000000 : ℝ), (147155384609/1000000000000 : ℝ), (10358219477593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375913091/10000000000 : ℝ)|^259 ≤ (43851583618701/100000000000000 : ℝ)^195
        have hw : |(5375913091/10000000000 : ℝ)|=(5375913091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2362774113/10000000000 : ℝ)|^259 ≤ (147155384609/1000000000000 : ℝ)^195
        have hw : |(-2362774113/10000000000 : ℝ)|=(2362774113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575554567/5000000000 : ℝ)|^259 ≤ (10358219477593/25000000000000 : ℝ)^195
        have hw : |(2575554567/5000000000 : ℝ)|=(2575554567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2687956521/5000000000 : ℝ)*x 0 + (2575554591/5000000000 : ℝ)*x 1 + (-1181387057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687956521/5000000000 : ℝ)^259 ≤ (2740723942989/6250000000000 : ℝ)^195 := by
    have hnat : (2687956521 : ℕ)^259*6250000000000^195 ≤ 2740723942989^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687956521 5000000000 2740723942989 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575554591/5000000000 : ℝ)^259 ≤ (1657315136927/4000000000000 : ℝ)^195 := by
    have hnat : (2575554591 : ℕ)^259*4000000000000^195 ≤ 1657315136927^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575554591 5000000000 1657315136927 4000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181387057/5000000000 : ℝ)^259 ≤ (3678884617293/25000000000000 : ℝ)^195 := by
    have hnat : (1181387057 : ℕ)^259*25000000000000^195 ≤ 3678884617293^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181387057 5000000000 3678884617293 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687956521/5000000000 : ℝ), (2575554591/5000000000 : ℝ), (-1181387057/5000000000 : ℝ)] ![(2740723942989/6250000000000 : ℝ), (1657315136927/4000000000000 : ℝ), (3678884617293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687956521/5000000000 : ℝ)|^259 ≤ (2740723942989/6250000000000 : ℝ)^195
        have hw : |(2687956521/5000000000 : ℝ)|=(2687956521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575554591/5000000000 : ℝ)|^259 ≤ (1657315136927/4000000000000 : ℝ)^195
        have hw : |(2575554591/5000000000 : ℝ)|=(2575554591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1181387057/5000000000 : ℝ)|^259 ≤ (3678884617293/25000000000000 : ℝ)^195
        have hw : |(-1181387057/5000000000 : ℝ)|=(1181387057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4359544191/10000000000 : ℝ)*x 0 + (4011162643/10000000000 : ℝ)*x 1 + (4738299999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359544191/10000000000 : ℝ)^259 ≤ (16598689595889/50000000000000 : ℝ)^195 := by
    have hnat : (4359544191 : ℕ)^259*50000000000000^195 ≤ 16598689595889^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359544191 10000000000 16598689595889 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011162643/10000000000 : ℝ)^259 ≤ (7430217886221/25000000000000 : ℝ)^195 := by
    have hnat : (4011162643 : ℕ)^259*25000000000000^195 ≤ 7430217886221^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011162643 10000000000 7430217886221 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4738299999/10000000000 : ℝ)^259 ≤ (37081749244193/100000000000000 : ℝ)^195 := by
    have hnat : (4738299999 : ℕ)^259*100000000000000^195 ≤ 37081749244193^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738299999 10000000000 37081749244193 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359544191/10000000000 : ℝ), (4011162643/10000000000 : ℝ), (4738299999/10000000000 : ℝ)] ![(16598689595889/50000000000000 : ℝ), (7430217886221/25000000000000 : ℝ), (37081749244193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359544191/10000000000 : ℝ)|^259 ≤ (16598689595889/50000000000000 : ℝ)^195
        have hw : |(4359544191/10000000000 : ℝ)|=(4359544191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011162643/10000000000 : ℝ)|^259 ≤ (7430217886221/25000000000000 : ℝ)^195
        have hw : |(4011162643/10000000000 : ℝ)|=(4011162643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4738299999/10000000000 : ℝ)|^259 ≤ (37081749244193/100000000000000 : ℝ)^195
        have hw : |(4738299999/10000000000 : ℝ)|=(4738299999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170741709/10000000000 : ℝ)*x 0 + (2576868713/5000000000 : ℝ)*x 1 + (5517342519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170741709/10000000000 : ℝ)^259 ≤ (6574300459877/50000000000000 : ℝ)^195 := by
    have hnat : (2170741709 : ℕ)^259*50000000000000^195 ≤ 6574300459877^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170741709 10000000000 6574300459877 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576868713/5000000000 : ℝ)^259 ≤ (41460959356771/100000000000000 : ℝ)^195 := by
    have hnat : (2576868713 : ℕ)^259*100000000000000^195 ≤ 41460959356771^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576868713 5000000000 41460959356771 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517342519/10000000000 : ℝ)^259 ≤ (4539043969919/10000000000000 : ℝ)^195 := by
    have hnat : (5517342519 : ℕ)^259*10000000000000^195 ≤ 4539043969919^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517342519 10000000000 4539043969919 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170741709/10000000000 : ℝ), (2576868713/5000000000 : ℝ), (5517342519/10000000000 : ℝ)] ![(6574300459877/50000000000000 : ℝ), (41460959356771/100000000000000 : ℝ), (4539043969919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170741709/10000000000 : ℝ)|^259 ≤ (6574300459877/50000000000000 : ℝ)^195
        have hw : |(-2170741709/10000000000 : ℝ)|=(2170741709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576868713/5000000000 : ℝ)|^259 ≤ (41460959356771/100000000000000 : ℝ)^195
        have hw : |(2576868713/5000000000 : ℝ)|=(2576868713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517342519/10000000000 : ℝ)|^259 ≤ (4539043969919/10000000000000 : ℝ)^195
        have hw : |(5517342519/10000000000 : ℝ)|=(5517342519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1320653361/2500000000 : ℝ)*x 0 + (-499135053/2500000000 : ℝ)*x 1 + (5517342609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320653361/2500000000 : ℝ)^259 ≤ (10710910895919/25000000000000 : ℝ)^195 := by
    have hnat : (1320653361 : ℕ)^259*25000000000000^195 ≤ 10710910895919^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320653361 2500000000 10710910895919 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499135053/2500000000 : ℝ)^259 ≤ (11765915720411/100000000000000 : ℝ)^195 := by
    have hnat : (499135053 : ℕ)^259*100000000000000^195 ≤ 11765915720411^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499135053 2500000000 11765915720411 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517342609/10000000000 : ℝ)^259 ≤ (45390440682617/100000000000000 : ℝ)^195 := by
    have hnat : (5517342609 : ℕ)^259*100000000000000^195 ≤ 45390440682617^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517342609 10000000000 45390440682617 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320653361/2500000000 : ℝ), (-499135053/2500000000 : ℝ), (5517342609/10000000000 : ℝ)] ![(10710910895919/25000000000000 : ℝ), (11765915720411/100000000000000 : ℝ), (45390440682617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320653361/2500000000 : ℝ)|^259 ≤ (10710910895919/25000000000000 : ℝ)^195
        have hw : |(1320653361/2500000000 : ℝ)|=(1320653361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499135053/2500000000 : ℝ)|^259 ≤ (11765915720411/100000000000000 : ℝ)^195
        have hw : |(-499135053/2500000000 : ℝ)|=(499135053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517342609/10000000000 : ℝ)|^259 ≤ (45390440682617/100000000000000 : ℝ)^195
        have hw : |(5517342609/10000000000 : ℝ)|=(5517342609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (264130681/500000000 : ℝ)*x 0 + (1379335633/2500000000 : ℝ)*x 1 + (-1996540077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264130681/500000000 : ℝ)^259 ≤ (5355455684947/12500000000000 : ℝ)^195 := by
    have hnat : (264130681 : ℕ)^259*12500000000000^195 ≤ 5355455684947^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264130681 500000000 5355455684947 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379335633/2500000000 : ℝ)^259 ≤ (1134760996031/2500000000000 : ℝ)^195 := by
    have hnat : (1379335633 : ℕ)^259*2500000000000^195 ≤ 1134760996031^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379335633 2500000000 1134760996031 2500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996540077/10000000000 : ℝ)^259 ≤ (11765914663723/100000000000000 : ℝ)^195 := by
    have hnat : (1996540077 : ℕ)^259*100000000000000^195 ≤ 11765914663723^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996540077 10000000000 11765914663723 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264130681/500000000 : ℝ), (1379335633/2500000000 : ℝ), (-1996540077/10000000000 : ℝ)] ![(5355455684947/12500000000000 : ℝ), (1134760996031/2500000000000 : ℝ), (11765914663723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264130681/500000000 : ℝ)|^259 ≤ (5355455684947/12500000000000 : ℝ)^195
        have hw : |(264130681/500000000 : ℝ)|=(264130681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379335633/2500000000 : ℝ)|^259 ≤ (1134760996031/2500000000000 : ℝ)^195
        have hw : |(1379335633/2500000000 : ℝ)|=(1379335633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1996540077/10000000000 : ℝ)|^259 ≤ (11765914663723/100000000000000 : ℝ)^195
        have hw : |(-1996540077/10000000000 : ℝ)|=(1996540077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s2_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4359774677/10000000000 : ℝ)*x 0 + (2366558903/5000000000 : ℝ)*x 1 + (40163971/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359774677/10000000000 : ℝ)^259 ≤ (33199710373807/100000000000000 : ℝ)^195 := by
    have hnat : (4359774677 : ℕ)^259*100000000000000^195 ≤ 33199710373807^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359774677 10000000000 33199710373807 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366558903/5000000000 : ℝ)^259 ≤ (37027892707361/100000000000000 : ℝ)^195 := by
    have hnat : (2366558903 : ℕ)^259*100000000000000^195 ≤ 37027892707361^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366558903 5000000000 37027892707361 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40163971/100000000 : ℝ)^259 ≤ (3721549612961/12500000000000 : ℝ)^195 := by
    have hnat : (40163971 : ℕ)^259*12500000000000^195 ≤ 3721549612961^195*100000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40163971 100000000 3721549612961 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359774677/10000000000 : ℝ), (2366558903/5000000000 : ℝ), (40163971/100000000 : ℝ)] ![(33199710373807/100000000000000 : ℝ), (37027892707361/100000000000000 : ℝ), (3721549612961/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359774677/10000000000 : ℝ)|^259 ≤ (33199710373807/100000000000000 : ℝ)^195
        have hw : |(4359774677/10000000000 : ℝ)|=(4359774677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366558903/5000000000 : ℝ)|^259 ≤ (37027892707361/100000000000000 : ℝ)^195
        have hw : |(2366558903/5000000000 : ℝ)|=(2366558903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40163971/100000000 : ℝ)|^259 ≤ (3721549612961/12500000000000 : ℝ)^195
        have hw : |(40163971/100000000 : ℝ)|=(40163971/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10327/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2213/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16647/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10327/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10327/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10327/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10327/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10327/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10327/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2691/50000 : ℝ) ^ (8287/2048 : ℝ) ≤ (366334161978697/50000000000000000000 : ℝ) := by
    have hpowers : (2691/50000 : ℝ)^8287 ≤ (366334161978697/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2691 : ℕ)^8287*50000000000000000000^2048 ≤ 366334161978697^2048*50000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2691 50000 366334161978697 50000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2691/50000 : ℝ)) (X := (366334161978697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10327/50000 : ℝ) ^ (8287/2048 : ℝ) ≤ (169138308079799701/100000000000000000000 : ℝ) := by
    have hpowers : (10327/50000 : ℝ)^8287 ≤ (169138308079799701/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10327 : ℕ)^8287*100000000000000000000^2048 ≤ 169138308079799701^2048*50000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10327 50000 169138308079799701 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10327/50000 : ℝ)) (X := (169138308079799701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000366334161978697/25000000000000000000 : ℝ) ≤ (10000036213260547/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (25000366334161978697/25000000000000000000 : ℝ)^2048 ≤ (10000036213260547/10000000000000000 : ℝ)^8287 := by
      have hnat : (25000366334161978697 : ℕ)^2048*10000000000000000^8287 ≤ 10000036213260547^8287*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000366334161978697 25000000000000000000 10000036213260547 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036213260547/10000000000000000 : ℝ)) (X := (25000366334161978697/25000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20033974195280751419/20000000000000000000 : ℝ) ≤ (10004195408690131/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (20033974195280751419/20000000000000000000 : ℝ)^2048 ≤ (10004195408690131/10000000000000000 : ℝ)^8287 := by
      have hnat : (20033974195280751419 : ℕ)^2048*10000000000000000^8287 ≤ 10004195408690131^8287*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20033974195280751419 20000000000000000000 10004195408690131 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004195408690131/10000000000000000 : ℝ)) (X := (20033974195280751419/20000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50169138308079799701/50000000000000000000 : ℝ) ≤ (2001670920823943/2000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50169138308079799701/50000000000000000000 : ℝ)^2048 ≤ (2001670920823943/2000000000000000 : ℝ)^8287 := by
      have hnat : (50169138308079799701 : ℕ)^2048*2000000000000000^8287 ≤ 2001670920823943^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50169138308079799701 50000000000000000000 2001670920823943 2000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001670920823943/2000000000000000 : ℝ)) (X := (50169138308079799701/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(366334161978697/50000000000000000000 : ℝ) ≤ ((829759692767994737/830000000000000000 : ℝ)+2*(259949714349/95450000000000 : ℝ)*(2691/50000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (829759692767994737/830000000000000000 : ℝ)+2*(259949714349/95450000000000 : ℝ)*(2691/50000 : ℝ)=(10000036213260547/10000000000000000 : ℝ) by norm_num, show 1+2*(366334161978697/50000000000000000000 : ℝ)=(25000366334161978697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(169138308079799701/100000000000000000000 : ℝ)+(366334161978697/50000000000000000000 : ℝ) ≤ ((829759692767994737/830000000000000000 : ℝ)+(259949714349/95450000000000 : ℝ)*((10327/50000 : ℝ)+(2691/50000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (829759692767994737/830000000000000000 : ℝ)+(259949714349/95450000000000 : ℝ)*((10327/50000 : ℝ)+(2691/50000 : ℝ))=(10004195408690131/10000000000000000 : ℝ) by norm_num, show 1+(169138308079799701/100000000000000000000 : ℝ)+(366334161978697/50000000000000000000 : ℝ)=(20033974195280751419/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(169138308079799701/100000000000000000000 : ℝ) ≤ ((829759692767994737/830000000000000000 : ℝ)+2*(259949714349/95450000000000 : ℝ)*(10327/50000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (829759692767994737/830000000000000000 : ℝ)+2*(259949714349/95450000000000 : ℝ)*(10327/50000 : ℝ)=(2001670920823943/2000000000000000 : ℝ) by norm_num, show 1+2*(169138308079799701/100000000000000000000 : ℝ)=(50169138308079799701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (829759692767994737/830000000000000000 : ℝ)*(X 1 0+X 2 0)+(259949714349/95450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2691/50000 : ℝ)) (hi := (10327/50000 : ℝ)) (c := (829759692767994737/830000000000000000 : ℝ)) (alpha := (259949714349/95450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (829759692767994737/830000000000000000 : ℝ)*(X 0 1+X 2 1)+(259949714349/95450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2691/50000 : ℝ)) (hi := (10327/50000 : ℝ)) (c := (829759692767994737/830000000000000000 : ℝ)) (alpha := (259949714349/95450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (829759692767994737/830000000000000000 : ℝ)*(X 0 2+X 1 2)+(259949714349/95450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2691/50000 : ℝ)) (hi := (10327/50000 : ℝ)) (c := (829759692767994737/830000000000000000 : ℝ)) (alpha := (259949714349/95450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135664091/625000000 : ℝ)*X 0 0+(5519998853/10000000000 : ℝ)*X 0 1+(2575554041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375913091/10000000000 : ℝ)*X 1 0+(-2362774113/10000000000 : ℝ)*X 1 1+(2575554567/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687956521/5000000000 : ℝ)*X 2 0+(2575554591/5000000000 : ℝ)*X 2 1+(-1181387057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359544191/10000000000 : ℝ)*X 0 0+(4011162643/10000000000 : ℝ)*X 0 1+(4738299999/10000000000 : ℝ)*X 0 2+(4359544191/10000000000 : ℝ)*X 1 0+(4011162643/10000000000 : ℝ)*X 1 1+(4738299999/10000000000 : ℝ)*X 1 2+(4359544191/10000000000 : ℝ)*X 2 0+(4011162643/10000000000 : ℝ)*X 2 1+(4738299999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170741709/10000000000 : ℝ)*X 0 0+(2576868713/5000000000 : ℝ)*X 0 1+(5517342519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320653361/2500000000 : ℝ)*X 1 0+(-499135053/2500000000 : ℝ)*X 1 1+(5517342609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264130681/500000000 : ℝ)*X 2 0+(1379335633/2500000000 : ℝ)*X 2 1+(-1996540077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359774677/10000000000 : ℝ)*X 0 0+(2366558903/5000000000 : ℝ)*X 0 1+(40163971/100000000 : ℝ)*X 0 2+(4359774677/10000000000 : ℝ)*X 1 0+(2366558903/5000000000 : ℝ)*X 1 1+(40163971/100000000 : ℝ)*X 1 2+(4359774677/10000000000 : ℝ)*X 2 0+(2366558903/5000000000 : ℝ)*X 2 1+(40163971/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1516335572799583595320941921/238625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648328627/100000000000000 : ℝ)*(base19) + (201197227/50000000000000 : ℝ)*(base23) + (46417/390625000000 : ℝ)*(upper2) + (88255803/50000000000000 : ℝ)*(upper3) + (130811641/100000000000000 : ℝ)*(upper4) + (1021529982802157/50000000000000 : ℝ)*(major0) + (1021529982802157/50000000000000 : ℝ)*(major1) + (1021529982802157/50000000000000 : ℝ)*(major2) + (677710708256663/25000000000000 : ℝ)*(sp0) + (67771343392691/2500000000000 : ℝ)*(sp1) + (1355426990820907/50000000000000 : ℝ)*(sp2) + (1375259807757919/100000000000000 : ℝ)*(sp3) + (721938101/6250000000000 : ℝ)*(sp4) + (5527598743/100000000000000 : ℝ)*(sp7) + (1375265335356663/100000000000000 : ℝ)*(f.failure) + (2710854384036267/100000000000000 : ℝ)*(f.sum) + (2705777593337/596562500000000000000000000 : ℝ)*base65 + (7827974848023202693/954500000000000000000000000000000 : ℝ)*base68 + (396383531667797307/954500000000000000000000000000000 : ℝ)*base69 + (1219769407321702693/954500000000000000000000000000000 : ℝ)*base72 + (27273908230197/9545000000000000000000000000 : ℝ)*base73 + (543149518896202693/954500000000000000000000000000000 : ℝ)*base76 + (11175608111187702693/954500000000000000000000000000000 : ℝ)*base78 + (103223124315202693/954500000000000000000000000000000 : ℝ)*base80 + (83291889339347/9545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10987807/1250000000000000000000 : ℝ)*base89 + (10987807/1250000000000000000000 : ℝ)*base91 + (10987807/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90346970396335827817252743/20750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859459593/100000000000000 : ℝ)*(base19) + (1043260767/100000000000000 : ℝ)*(base23) + (132334967/100000000000000 : ℝ)*(upper3) + (26207257/100000000000000 : ℝ)*(lower4) + (1957173/2500000000000 : ℝ)*(upper5) + (1036370022578013/50000000000000 : ℝ)*(major0) + (1036370022578013/50000000000000 : ℝ)*(major1) + (1036370022578013/50000000000000 : ℝ)*(major2) + (758214263/10000000000000 : ℝ)*(sp1) + (4996000423/50000000000000 : ℝ)*(sp2) + (1375117880897509/50000000000000 : ℝ)*(sp4) + (687556830048199/25000000000000 : ℝ)*(sp5) + (550044945306681/20000000000000 : ℝ)*(sp6) + (1395244183381333/100000000000000 : ℝ)*(sp7) + (1395244183381333/100000000000000 : ℝ)*(f.failure) + (1375117880897509/50000000000000 : ℝ)*(f.sum) + (21646375856907/9545000000000000000000000000 : ℝ)*base66 + (1140783010203495637/954500000000000000000000000000000 : ℝ)*base68 + (5633259987504504363/954500000000000000000000000000000 : ℝ)*base69 + (9006019671333995637/954500000000000000000000000000000 : ℝ)*base72 + (1988246564157/2386250000000000000000000000 : ℝ)*base73 + (1597704468184495637/954500000000000000000000000000000 : ℝ)*base76 + (4287631114384995637/954500000000000000000000000000000 : ℝ)*base78 + (5062793338058504363/954500000000000000000000000000000 : ℝ)*base79 + (34365946384453/9545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2784563/1250000000000000000000 : ℝ)*base90 + (2784563/1250000000000000000000 : ℝ)*base92 + (2784563/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10327/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1095_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1095_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1095_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1095_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

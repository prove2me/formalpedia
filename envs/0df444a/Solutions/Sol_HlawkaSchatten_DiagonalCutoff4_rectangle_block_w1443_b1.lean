-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1443_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:26.61761+00:00
-- url     : https://prove2.me/submissions/4f68c6b7-4e85-418a-858b-579729571571

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
theorem support_rectangle_w1443_s3_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958852479/10000000000 : ℝ)*x 0 + (2707947389/5000000000 : ℝ)*x 1 + (5239456127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958852479/10000000000 : ℝ)^4403 ≤ (11952096795963/100000000000000 : ℝ)^3379 := by
    have hnat : (1958852479 : ℕ)^4403*100000000000000^3379 ≤ 11952096795963^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958852479 10000000000 11952096795963 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707947389/5000000000 : ℝ)^4403 ≤ (44973785757249/100000000000000 : ℝ)^3379 := by
    have hnat : (2707947389 : ℕ)^4403*100000000000000^3379 ≤ 44973785757249^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707947389 5000000000 44973785757249 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239456127/10000000000 : ℝ)^4403 ≤ (21537058718651/50000000000000 : ℝ)^3379 := by
    have hnat : (5239456127 : ℕ)^4403*50000000000000^3379 ≤ 21537058718651^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239456127 10000000000 21537058718651 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958852479/10000000000 : ℝ), (2707947389/5000000000 : ℝ), (5239456127/10000000000 : ℝ)] ![(11952096795963/100000000000000 : ℝ), (44973785757249/100000000000000 : ℝ), (21537058718651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958852479/10000000000 : ℝ)|^4403 ≤ (11952096795963/100000000000000 : ℝ)^3379
        have hw : |(-1958852479/10000000000 : ℝ)|=(1958852479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707947389/5000000000 : ℝ)|^4403 ≤ (44973785757249/100000000000000 : ℝ)^3379
        have hw : |(2707947389/5000000000 : ℝ)|=(2707947389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239456127/10000000000 : ℝ)|^4403 ≤ (21537058718651/50000000000000 : ℝ)^3379
        have hw : |(5239456127/10000000000 : ℝ)|=(5239456127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337300373/2500000000 : ℝ)*x 0 + (-1024415477/5000000000 : ℝ)*x 1 + (5239455513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337300373/2500000000 : ℝ)^4403 ≤ (44253477511787/100000000000000 : ℝ)^3379 := by
    have hnat : (1337300373 : ℕ)^4403*100000000000000^3379 ≤ 44253477511787^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337300373 2500000000 44253477511787 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024415477/5000000000 : ℝ)^4403 ≤ (6336205809193/50000000000000 : ℝ)^3379 := by
    have hnat : (1024415477 : ℕ)^4403*50000000000000^3379 ≤ 6336205809193^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024415477 5000000000 6336205809193 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239455513/10000000000 : ℝ)^4403 ≤ (43074110859829/100000000000000 : ℝ)^3379 := by
    have hnat : (5239455513 : ℕ)^4403*100000000000000^3379 ≤ 43074110859829^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239455513 10000000000 43074110859829 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337300373/2500000000 : ℝ), (-1024415477/5000000000 : ℝ), (5239455513/10000000000 : ℝ)] ![(44253477511787/100000000000000 : ℝ), (6336205809193/50000000000000 : ℝ), (43074110859829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337300373/2500000000 : ℝ)|^4403 ≤ (44253477511787/100000000000000 : ℝ)^3379
        have hw : |(1337300373/2500000000 : ℝ)|=(1337300373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024415477/5000000000 : ℝ)|^4403 ≤ (6336205809193/50000000000000 : ℝ)^3379
        have hw : |(-1024415477/5000000000 : ℝ)|=(1024415477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239455513/10000000000 : ℝ)|^4403 ≤ (43074110859829/100000000000000 : ℝ)^3379
        have hw : |(5239455513/10000000000 : ℝ)|=(5239455513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106984029/200000000 : ℝ)*x 0 + (2619727813/5000000000 : ℝ)*x 1 + (-102441543/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106984029/200000000 : ℝ)^4403 ≤ (44253477059027/100000000000000 : ℝ)^3379 := by
    have hnat : (106984029 : ℕ)^4403*100000000000000^3379 ≤ 44253477059027^3379*200000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106984029 200000000 44253477059027 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619727813/5000000000 : ℝ)^4403 ≤ (43074112070341/100000000000000 : ℝ)^3379 := by
    have hnat : (2619727813 : ℕ)^4403*100000000000000^3379 ≤ 43074112070341^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619727813 5000000000 43074112070341 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102441543/500000000 : ℝ)^4403 ≤ (12672410860783/100000000000000 : ℝ)^3379 := by
    have hnat : (102441543 : ℕ)^4403*100000000000000^3379 ≤ 12672410860783^3379*500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102441543 500000000 12672410860783 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106984029/200000000 : ℝ), (2619727813/5000000000 : ℝ), (-102441543/500000000 : ℝ)] ![(44253477059027/100000000000000 : ℝ), (43074112070341/100000000000000 : ℝ), (12672410860783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106984029/200000000 : ℝ)|^4403 ≤ (44253477059027/100000000000000 : ℝ)^3379
        have hw : |(106984029/200000000 : ℝ)|=(106984029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619727813/5000000000 : ℝ)|^4403 ≤ (43074112070341/100000000000000 : ℝ)^3379
        have hw : |(2619727813/5000000000 : ℝ)|=(2619727813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102441543/500000000 : ℝ)|^4403 ≤ (12672410860783/100000000000000 : ℝ)^3379
        have hw : |(-102441543/500000000 : ℝ)|=(102441543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300288647/10000000000 : ℝ)*x 0 + (4112285673/10000000000 : ℝ)*x 1 + (4495940517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300288647/10000000000 : ℝ)^4403 ≤ (520295091721/1562500000000 : ℝ)^3379 := by
    have hnat : (4300288647 : ℕ)^4403*1562500000000^3379 ≤ 520295091721^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300288647 10000000000 520295091721 1562500000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4112285673/10000000000 : ℝ)^4403 ≤ (7853656491829/25000000000000 : ℝ)^3379 := by
    have hnat : (4112285673 : ℕ)^4403*25000000000000^3379 ≤ 7853656491829^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112285673 10000000000 7853656491829 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495940517/10000000000 : ℝ)^4403 ≤ (35286488146323/100000000000000 : ℝ)^3379 := by
    have hnat : (4495940517 : ℕ)^4403*100000000000000^3379 ≤ 35286488146323^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495940517 10000000000 35286488146323 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300288647/10000000000 : ℝ), (4112285673/10000000000 : ℝ), (4495940517/10000000000 : ℝ)] ![(520295091721/1562500000000 : ℝ), (7853656491829/25000000000000 : ℝ), (35286488146323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300288647/10000000000 : ℝ)|^4403 ≤ (520295091721/1562500000000 : ℝ)^3379
        have hw : |(4300288647/10000000000 : ℝ)|=(4300288647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4112285673/10000000000 : ℝ)|^4403 ≤ (7853656491829/25000000000000 : ℝ)^3379
        have hw : |(4112285673/10000000000 : ℝ)|=(4112285673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495940517/10000000000 : ℝ)|^4403 ≤ (35286488146323/100000000000000 : ℝ)^3379
        have hw : |(4495940517/10000000000 : ℝ)|=(4495940517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-195886707/1000000000 : ℝ)*x 0 + (524015697/1000000000 : ℝ)*x 1 + (676898773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195886707/1000000000 : ℝ)^4403 ≤ (1195221280409/10000000000000 : ℝ)^3379 := by
    have hnat : (195886707 : ℕ)^4403*10000000000000^3379 ≤ 1195221280409^3379*1000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195886707 1000000000 1195221280409 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524015697/1000000000 : ℝ)^4403 ≤ (43081625367311/100000000000000 : ℝ)^3379 := by
    have hnat : (524015697 : ℕ)^4403*100000000000000^3379 ≤ 43081625367311^3379*1000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524015697 1000000000 43081625367311 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676898773/1250000000 : ℝ)^4403 ≤ (22483080903081/50000000000000 : ℝ)^3379 := by
    have hnat : (676898773 : ℕ)^4403*50000000000000^3379 ≤ 22483080903081^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676898773 1250000000 22483080903081 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195886707/1000000000 : ℝ), (524015697/1000000000 : ℝ), (676898773/1250000000 : ℝ)] ![(1195221280409/10000000000000 : ℝ), (43081625367311/100000000000000 : ℝ), (22483080903081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195886707/1000000000 : ℝ)|^4403 ≤ (1195221280409/10000000000000 : ℝ)^3379
        have hw : |(-195886707/1000000000 : ℝ)|=(195886707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524015697/1000000000 : ℝ)|^4403 ≤ (43081625367311/100000000000000 : ℝ)^3379
        have hw : |(524015697/1000000000 : ℝ)|=(524015697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676898773/1250000000 : ℝ)|^4403 ≤ (22483080903081/50000000000000 : ℝ)^3379
        have hw : |(676898773/1250000000 : ℝ)|=(676898773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325817597/2500000000 : ℝ)*x 0 + (-58534277/312500000 : ℝ)*x 1 + (1353797533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325817597/2500000000 : ℝ)^4403 ≤ (8751797100531/20000000000000 : ℝ)^3379 := by
    have hnat : (1325817597 : ℕ)^4403*20000000000000^3379 ≤ 8751797100531^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325817597 2500000000 8751797100531 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58534277/312500000 : ℝ)^4403 ≤ (11274853236679/100000000000000 : ℝ)^3379 := by
    have hnat : (58534277 : ℕ)^4403*100000000000000^3379 ≤ 11274853236679^3379*312500000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58534277 312500000 11274853236679 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353797533/2500000000 : ℝ)^4403 ≤ (8993232248703/20000000000000 : ℝ)^3379 := by
    have hnat : (1353797533 : ℕ)^4403*20000000000000^3379 ≤ 8993232248703^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353797533 2500000000 8993232248703 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325817597/2500000000 : ℝ), (-58534277/312500000 : ℝ), (1353797533/2500000000 : ℝ)] ![(8751797100531/20000000000000 : ℝ), (11274853236679/100000000000000 : ℝ), (8993232248703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325817597/2500000000 : ℝ)|^4403 ≤ (8751797100531/20000000000000 : ℝ)^3379
        have hw : |(1325817597/2500000000 : ℝ)|=(1325817597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58534277/312500000 : ℝ)|^4403 ≤ (11274853236679/100000000000000 : ℝ)^3379
        have hw : |(-58534277/312500000 : ℝ)|=(58534277/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353797533/2500000000 : ℝ)|^4403 ≤ (8993232248703/20000000000000 : ℝ)^3379
        have hw : |(1353797533/2500000000 : ℝ)|=(1353797533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_6 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303269129/10000000000 : ℝ)*x 0 + (5415191153/10000000000 : ℝ)*x 1 + (-1873097181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303269129/10000000000 : ℝ)^4403 ≤ (10939742991513/25000000000000 : ℝ)^3379 := by
    have hnat : (5303269129 : ℕ)^4403*25000000000000^3379 ≤ 10939742991513^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303269129 10000000000 10939742991513 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415191153/10000000000 : ℝ)^4403 ≤ (5620771536359/12500000000000 : ℝ)^3379 := by
    have hnat : (5415191153 : ℕ)^4403*12500000000000^3379 ≤ 5620771536359^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415191153 10000000000 5620771536359 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873097181/10000000000 : ℝ)^4403 ≤ (2818713930769/25000000000000 : ℝ)^3379 := by
    have hnat : (1873097181 : ℕ)^4403*25000000000000^3379 ≤ 2818713930769^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873097181 10000000000 2818713930769 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303269129/10000000000 : ℝ), (5415191153/10000000000 : ℝ), (-1873097181/10000000000 : ℝ)] ![(10939742991513/25000000000000 : ℝ), (5620771536359/12500000000000 : ℝ), (2818713930769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303269129/10000000000 : ℝ)|^4403 ≤ (10939742991513/25000000000000 : ℝ)^3379
        have hw : |(5303269129/10000000000 : ℝ)|=(5303269129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415191153/10000000000 : ℝ)|^4403 ≤ (5620771536359/12500000000000 : ℝ)^3379
        have hw : |(5415191153/10000000000 : ℝ)|=(5415191153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873097181/10000000000 : ℝ)|^4403 ≤ (2818713930769/25000000000000 : ℝ)^3379
        have hw : |(-1873097181/10000000000 : ℝ)|=(1873097181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s3_7 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150160163/5000000000 : ℝ)*x 0 + (561802131/1250000000 : ℝ)*x 1 + (2056909303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150160163/5000000000 : ℝ)^4403 ≤ (16649602756329/50000000000000 : ℝ)^3379 := by
    have hnat : (2150160163 : ℕ)^4403*50000000000000^3379 ≤ 16649602756329^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150160163 5000000000 16649602756329 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561802131/1250000000 : ℝ)^4403 ≤ (35270908424637/100000000000000 : ℝ)^3379 := by
    have hnat : (561802131 : ℕ)^4403*100000000000000^3379 ≤ 35270908424637^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561802131 1250000000 35270908424637 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056909303/5000000000 : ℝ)^4403 ≤ (3928735755919/12500000000000 : ℝ)^3379 := by
    have hnat : (2056909303 : ℕ)^4403*12500000000000^3379 ≤ 3928735755919^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056909303 5000000000 3928735755919 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150160163/5000000000 : ℝ), (561802131/1250000000 : ℝ), (2056909303/5000000000 : ℝ)] ![(16649602756329/50000000000000 : ℝ), (35270908424637/100000000000000 : ℝ), (3928735755919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150160163/5000000000 : ℝ)|^4403 ≤ (16649602756329/50000000000000 : ℝ)^3379
        have hw : |(2150160163/5000000000 : ℝ)|=(2150160163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561802131/1250000000 : ℝ)|^4403 ≤ (35270908424637/100000000000000 : ℝ)^3379
        have hw : |(561802131/1250000000 : ℝ)|=(561802131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2056909303/5000000000 : ℝ)|^4403 ≤ (3928735755919/12500000000000 : ℝ)^3379
        have hw : |(2056909303/5000000000 : ℝ)|=(2056909303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11203/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (747/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7879/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7879/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7879/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7879/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7879/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7879/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10441/100000 : ℝ) ^ (2201/512 : ℝ) ≤ (75622483599303/1250000000000000000 : ℝ) := by
    have hpowers : (10441/100000 : ℝ)^2201 ≤ (75622483599303/1250000000000000000 : ℝ)^512 := by
      have hnat : (10441 : ℕ)^2201*1250000000000000000^512 ≤ 75622483599303^512*100000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10441 100000 75622483599303 1250000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10441/100000 : ℝ)) (X := (75622483599303/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7879/50000 : ℝ) ^ (2201/512 : ℝ) ≤ (17748642679273263/50000000000000000000 : ℝ) := by
    have hpowers : (7879/50000 : ℝ)^2201 ≤ (17748642679273263/50000000000000000000 : ℝ)^512 := by
      have hnat : (7879 : ℕ)^2201*50000000000000000000^512 ≤ 17748642679273263^512*50000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7879 50000 17748642679273263 50000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7879/50000 : ℝ)) (X := (17748642679273263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (625075622483599303/625000000000000000 : ℝ) ≤ (10000281449626319/10000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (625075622483599303/625000000000000000 : ℝ)^512 ≤ (10000281449626319/10000000000000000 : ℝ)^2201 := by
      have hnat : (625075622483599303 : ℕ)^512*10000000000000000^2201 ≤ 10000281449626319^2201*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625075622483599303 625000000000000000 10000281449626319 10000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281449626319/10000000000000000 : ℝ)) (X := (625075622483599303/625000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020773542023245383/50000000000000000000 : ℝ) ≤ (10000966320619677/10000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (50020773542023245383/50000000000000000000 : ℝ)^512 ≤ (10000966320619677/10000000000000000 : ℝ)^2201 := by
      have hnat : (50020773542023245383 : ℕ)^512*10000000000000000^2201 ≤ 10000966320619677^2201*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020773542023245383 50000000000000000000 10000966320619677 10000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000966320619677/10000000000000000 : ℝ)) (X := (50020773542023245383/50000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017748642679273263/25000000000000000000 : ℝ) ≤ (2000330238322607/2000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25017748642679273263/25000000000000000000 : ℝ)^512 ≤ (2000330238322607/2000000000000000 : ℝ)^2201 := by
      have hnat : (25017748642679273263 : ℕ)^512*2000000000000000^2201 ≤ 2000330238322607^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017748642679273263 25000000000000000000 2000330238322607 2000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000330238322607/2000000000000000 : ℝ)) (X := (25017748642679273263/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(75622483599303/1250000000000000000 : ℝ) ≤ ((53157194991579836367/53170000000000000000 : ℝ)+2*(342435496679/265850000000000 : ℝ)*(10441/100000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (53157194991579836367/53170000000000000000 : ℝ)+2*(342435496679/265850000000000 : ℝ)*(10441/100000 : ℝ)=(10000281449626319/10000000000000000 : ℝ) by norm_num, show 1+2*(75622483599303/1250000000000000000 : ℝ)=(625075622483599303/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17748642679273263/50000000000000000000 : ℝ)+(75622483599303/1250000000000000000 : ℝ) ≤ ((53157194991579836367/53170000000000000000 : ℝ)+(342435496679/265850000000000 : ℝ)*((7879/50000 : ℝ)+(10441/100000 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (53157194991579836367/53170000000000000000 : ℝ)+(342435496679/265850000000000 : ℝ)*((7879/50000 : ℝ)+(10441/100000 : ℝ))=(10000966320619677/10000000000000000 : ℝ) by norm_num, show 1+(17748642679273263/50000000000000000000 : ℝ)+(75622483599303/1250000000000000000 : ℝ)=(50020773542023245383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17748642679273263/50000000000000000000 : ℝ) ≤ ((53157194991579836367/53170000000000000000 : ℝ)+2*(342435496679/265850000000000 : ℝ)*(7879/50000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (53157194991579836367/53170000000000000000 : ℝ)+2*(342435496679/265850000000000 : ℝ)*(7879/50000 : ℝ)=(2000330238322607/2000000000000000 : ℝ) by norm_num, show 1+2*(17748642679273263/50000000000000000000 : ℝ)=(25017748642679273263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53157194991579836367/53170000000000000000 : ℝ)*(X 1 0+X 2 0)+(342435496679/265850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (7879/50000 : ℝ)) (c := (53157194991579836367/53170000000000000000 : ℝ)) (alpha := (342435496679/265850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53157194991579836367/53170000000000000000 : ℝ)*(X 0 1+X 2 1)+(342435496679/265850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (7879/50000 : ℝ)) (c := (53157194991579836367/53170000000000000000 : ℝ)) (alpha := (342435496679/265850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53157194991579836367/53170000000000000000 : ℝ)*(X 0 2+X 1 2)+(342435496679/265850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (7879/50000 : ℝ)) (c := (53157194991579836367/53170000000000000000 : ℝ)) (alpha := (342435496679/265850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1958852479/10000000000 : ℝ)*X 0 0+(2707947389/5000000000 : ℝ)*X 0 1+(5239456127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337300373/2500000000 : ℝ)*X 1 0+(-1024415477/5000000000 : ℝ)*X 1 1+(5239455513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106984029/200000000 : ℝ)*X 2 0+(2619727813/5000000000 : ℝ)*X 2 1+(-102441543/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300288647/10000000000 : ℝ)*X 0 0+(4112285673/10000000000 : ℝ)*X 0 1+(4495940517/10000000000 : ℝ)*X 0 2+(4300288647/10000000000 : ℝ)*X 1 0+(4112285673/10000000000 : ℝ)*X 1 1+(4495940517/10000000000 : ℝ)*X 1 2+(4300288647/10000000000 : ℝ)*X 2 0+(4112285673/10000000000 : ℝ)*X 2 1+(4495940517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-195886707/1000000000 : ℝ)*X 0 0+(524015697/1000000000 : ℝ)*X 0 1+(676898773/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325817597/2500000000 : ℝ)*X 1 0+(-58534277/312500000 : ℝ)*X 1 1+(1353797533/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303269129/10000000000 : ℝ)*X 2 0+(5415191153/10000000000 : ℝ)*X 2 1+(-1873097181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150160163/5000000000 : ℝ)*X 0 0+(561802131/1250000000 : ℝ)*X 0 1+(2056909303/5000000000 : ℝ)*X 0 2+(2150160163/5000000000 : ℝ)*X 1 0+(561802131/1250000000 : ℝ)*X 1 1+(2056909303/5000000000 : ℝ)*X 1 2+(2150160163/5000000000 : ℝ)*X 2 0+(561802131/1250000000 : ℝ)*X 2 1+(2056909303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3343695234446939738202308211/664625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (848119763/100000000000000 : ℝ)*(base19) + (362217337/50000000000000 : ℝ)*(base23) + (46283409/100000000000000 : ℝ)*(lower2) + (9364879/100000000000000 : ℝ)*(upper5) + (2068553553323111/50000000000000 : ℝ)*(major0) + (2068553553323111/50000000000000 : ℝ)*(major1) + (2068553553323111/50000000000000 : ℝ)*(major2) + (5667695298320147/100000000000000 : ℝ)*(sp0) + (5667697622863477/100000000000000 : ℝ)*(sp1) + (5667698601328203/100000000000000 : ℝ)*(sp2) + (651628014696791/25000000000000 : ℝ)*(sp3) + (402744273/10000000000000 : ℝ)*(sp4) + (213694909/25000000000000 : ℝ)*(sp5) + (133052203/5000000000000 : ℝ)*(sp7) + (325814339978903/12500000000000 : ℝ)*(f.failure) + (5667699325762877/100000000000000 : ℝ)*(f.sum) + (23049540597801/26585000000000000000000000000 : ℝ)*base65 + (272078048513063251/204500000000000000000000000000000 : ℝ)*base68 + (1738179534198563251/204500000000000000000000000000000 : ℝ)*base70 + (1704483899277936749/204500000000000000000000000000000 : ℝ)*base71 + (29114568927413/13292500000000000000000000000 : ℝ)*base73 + (550218106486563251/204500000000000000000000000000000 : ℝ)*base76 + (150038235863063251/204500000000000000000000000000000 : ℝ)*base78 + (1312164969167063251/204500000000000000000000000000000 : ℝ)*base80 + (7872141419549/6646250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11164303/1250000000000000000000 : ℝ)*base89 + (11164303/1250000000000000000000 : ℝ)*base91 + (11164303/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (364868894683915595271291/26585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10809081/50000000000000 : ℝ)*(base8) + (17610237/2500000000000 : ℝ)*(base21) + (75385613/50000000000000 : ℝ)*(upper2) + (111940901/50000000000000 : ℝ)*(lower4) + (2085158813990367/50000000000000 : ℝ)*(major0) + (2085158813990367/50000000000000 : ℝ)*(major1) + (2085158813990367/50000000000000 : ℝ)*(major2) + (1724550671/100000000000000 : ℝ)*(sp0) + (175040253/25000000000000 : ℝ)*(sp1) + (3703738581/100000000000000 : ℝ)*(sp2) + (5713194602321673/100000000000000 : ℝ)*(sp4) + (1142639129665899/20000000000000 : ℝ)*(sp5) + (1142638388068489/20000000000000 : ℝ)*(sp6) + (2627438449983777/100000000000000 : ℝ)*(sp7) + (2627438449983777/100000000000000 : ℝ)*(f.failure) + (2856598174245253/50000000000000 : ℝ)*(f.sum) + (1080432766933717/26585000000000000000000000000 : ℝ)*base65 + (1765590307608547947/204500000000000000000000000000000 : ℝ)*base68 + (839292498539952053/204500000000000000000000000000000 : ℝ)*base69 + (2169424253557547947/204500000000000000000000000000000 : ℝ)*base72 + (7788677296627/6646250000000000000000000000 : ℝ)*base74 + (1448374041371547947/204500000000000000000000000000000 : ℝ)*base76 + (5267852423232952053/204500000000000000000000000000000 : ℝ)*base77 + (76997853547952053/204500000000000000000000000000000 : ℝ)*base79 + (74002723746573/26585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (106222377/10000000000000000000000 : ℝ)*base89 + (106222377/10000000000000000000000 : ℝ)*base91 + (106222377/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1443_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (747/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1443_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1443_s4_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959686117/10000000000 : ℝ)*x 0 + (5408741579/10000000000 : ℝ)*x 1 + (5246060023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959686117/10000000000 : ℝ)^4403 ≤ (2989681297697/25000000000000 : ℝ)^3379 := by
    have hnat : (1959686117 : ℕ)^4403*25000000000000^3379 ≤ 2989681297697^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959686117 10000000000 2989681297697 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408741579/10000000000 : ℝ)^4403 ≤ (44896399636129/100000000000000 : ℝ)^3379 := by
    have hnat : (5408741579 : ℕ)^4403*100000000000000^3379 ≤ 44896399636129^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408741579 10000000000 44896399636129 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246060023/10000000000 : ℝ)^4403 ≤ (43144875153903/100000000000000 : ℝ)^3379 := by
    have hnat : (5246060023 : ℕ)^4403*100000000000000^3379 ≤ 43144875153903^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246060023 10000000000 43144875153903 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959686117/10000000000 : ℝ), (5408741579/10000000000 : ℝ), (5246060023/10000000000 : ℝ)] ![(2989681297697/25000000000000 : ℝ), (44896399636129/100000000000000 : ℝ), (43144875153903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959686117/10000000000 : ℝ)|^4403 ≤ (2989681297697/25000000000000 : ℝ)^3379
        have hw : |(-1959686117/10000000000 : ℝ)|=(1959686117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408741579/10000000000 : ℝ)|^4403 ≤ (44896399636129/100000000000000 : ℝ)^3379
        have hw : |(5408741579/10000000000 : ℝ)|=(5408741579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246060023/10000000000 : ℝ)|^4403 ≤ (43144875153903/100000000000000 : ℝ)^3379
        have hw : |(5246060023/10000000000 : ℝ)|=(5246060023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347351579/10000000000 : ℝ)*x 0 + (-102126099/500000000 : ℝ)*x 1 + (2623030049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347351579/10000000000 : ℝ)^4403 ≤ (22116768243237/50000000000000 : ℝ)^3379 := by
    have hnat : (5347351579 : ℕ)^4403*50000000000000^3379 ≤ 22116768243237^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347351579 10000000000 22116768243237 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102126099/500000000 : ℝ)^4403 ≤ (3155396884011/25000000000000 : ℝ)^3379 := by
    have hnat : (102126099 : ℕ)^4403*25000000000000^3379 ≤ 3155396884011^3379*500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102126099 500000000 3155396884011 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623030049/5000000000 : ℝ)^4403 ≤ (21572437978823/50000000000000 : ℝ)^3379 := by
    have hnat : (2623030049 : ℕ)^4403*50000000000000^3379 ≤ 21572437978823^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623030049 5000000000 21572437978823 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347351579/10000000000 : ℝ), (-102126099/500000000 : ℝ), (2623030049/5000000000 : ℝ)] ![(22116768243237/50000000000000 : ℝ), (3155396884011/25000000000000 : ℝ), (21572437978823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347351579/10000000000 : ℝ)|^4403 ≤ (22116768243237/50000000000000 : ℝ)^3379
        have hw : |(5347351579/10000000000 : ℝ)|=(5347351579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102126099/500000000 : ℝ)|^4403 ≤ (3155396884011/25000000000000 : ℝ)^3379
        have hw : |(-102126099/500000000 : ℝ)|=(102126099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623030049/5000000000 : ℝ)|^4403 ≤ (21572437978823/50000000000000 : ℝ)^3379
        have hw : |(2623030049/5000000000 : ℝ)|=(2623030049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347351393/10000000000 : ℝ)*x 0 + (5246060183/10000000000 : ℝ)*x 1 + (-510630529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347351393/10000000000 : ℝ)^4403 ≤ (11058383620401/25000000000000 : ℝ)^3379 := by
    have hnat : (5347351393 : ℕ)^4403*25000000000000^3379 ≤ 11058383620401^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347351393 10000000000 11058383620401 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246060183/10000000000 : ℝ)^4403 ≤ (10786219217139/25000000000000 : ℝ)^3379 := by
    have hnat : (5246060183 : ℕ)^4403*25000000000000^3379 ≤ 10786219217139^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246060183 10000000000 10786219217139 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510630529/2500000000 : ℝ)^4403 ≤ (6310794315563/50000000000000 : ℝ)^3379 := by
    have hnat : (510630529 : ℕ)^4403*50000000000000^3379 ≤ 6310794315563^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510630529 2500000000 6310794315563 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347351393/10000000000 : ℝ), (5246060183/10000000000 : ℝ), (-510630529/2500000000 : ℝ)] ![(11058383620401/25000000000000 : ℝ), (10786219217139/25000000000000 : ℝ), (6310794315563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347351393/10000000000 : ℝ)|^4403 ≤ (11058383620401/25000000000000 : ℝ)^3379
        have hw : |(5347351393/10000000000 : ℝ)|=(5347351393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246060183/10000000000 : ℝ)|^4403 ≤ (10786219217139/25000000000000 : ℝ)^3379
        have hw : |(5246060183/10000000000 : ℝ)|=(5246060183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510630529/2500000000 : ℝ)|^4403 ≤ (6310794315563/50000000000000 : ℝ)^3379
        have hw : |(-510630529/2500000000 : ℝ)|=(510630529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300799937/10000000000 : ℝ)*x 0 + (4127181421/10000000000 : ℝ)*x 1 + (4480922007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300799937/10000000000 : ℝ)^4403 ≤ (6660808979217/20000000000000 : ℝ)^3379 := by
    have hnat : (4300799937 : ℕ)^4403*20000000000000^3379 ≤ 6660808979217^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300799937 10000000000 6660808979217 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127181421/10000000000 : ℝ)^4403 ≤ (1578149173729/5000000000000 : ℝ)^3379 := by
    have hnat : (4127181421 : ℕ)^4403*5000000000000^3379 ≤ 1578149173729^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127181421 10000000000 1578149173729 5000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480922007/10000000000 : ℝ)^4403 ≤ (8783242901579/25000000000000 : ℝ)^3379 := by
    have hnat : (4480922007 : ℕ)^4403*25000000000000^3379 ≤ 8783242901579^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480922007 10000000000 8783242901579 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300799937/10000000000 : ℝ), (4127181421/10000000000 : ℝ), (4480922007/10000000000 : ℝ)] ![(6660808979217/20000000000000 : ℝ), (1578149173729/5000000000000 : ℝ), (8783242901579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300799937/10000000000 : ℝ)|^4403 ≤ (6660808979217/20000000000000 : ℝ)^3379
        have hw : |(4300799937/10000000000 : ℝ)|=(4300799937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127181421/10000000000 : ℝ)|^4403 ≤ (1578149173729/5000000000000 : ℝ)^3379
        have hw : |(4127181421/10000000000 : ℝ)|=(4127181421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480922007/10000000000 : ℝ)|^4403 ≤ (8783242901579/25000000000000 : ℝ)^3379
        have hw : |(4480922007/10000000000 : ℝ)|=(4480922007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7838791/40000000 : ℝ)*x 0 + (2623328137/5000000000 : ℝ)*x 1 + (5408142249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7838791/40000000 : ℝ)^4403 ≤ (5979408846379/50000000000000 : ℝ)^3379 := by
    have hnat : (7838791 : ℕ)^4403*50000000000000^3379 ≤ 5979408846379^3379*40000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7838791 40000000 5979408846379 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623328137/5000000000 : ℝ)^4403 ≤ (10787816259771/25000000000000 : ℝ)^3379 := by
    have hnat : (2623328137 : ℕ)^4403*25000000000000^3379 ≤ 10787816259771^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623328137 5000000000 10787816259771 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408142249/10000000000 : ℝ)^4403 ≤ (44889917255891/100000000000000 : ℝ)^3379 := by
    have hnat : (5408142249 : ℕ)^4403*100000000000000^3379 ≤ 44889917255891^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408142249 10000000000 44889917255891 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7838791/40000000 : ℝ), (2623328137/5000000000 : ℝ), (5408142249/10000000000 : ℝ)] ![(5979408846379/50000000000000 : ℝ), (10787816259771/25000000000000 : ℝ), (44889917255891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7838791/40000000 : ℝ)|^4403 ≤ (5979408846379/50000000000000 : ℝ)^3379
        have hw : |(-7838791/40000000 : ℝ)|=(7838791/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623328137/5000000000 : ℝ)|^4403 ≤ (10787816259771/25000000000000 : ℝ)^3379
        have hw : |(2623328137/5000000000 : ℝ)|=(2623328137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408142249/10000000000 : ℝ)|^4403 ≤ (44889917255891/100000000000000 : ℝ)^3379
        have hw : |(5408142249/10000000000 : ℝ)|=(5408142249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305001553/10000000000 : ℝ)*x 0 + (-1880439969/10000000000 : ℝ)*x 1 + (676017779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305001553/10000000000 : ℝ)^4403 ≤ (5472199960339/12500000000000 : ℝ)^3379 := by
    have hnat : (5305001553 : ℕ)^4403*12500000000000^3379 ≤ 5472199960339^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305001553 10000000000 5472199960339 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880439969/10000000000 : ℝ)^4403 ≤ (11332483228953/100000000000000 : ℝ)^3379 := by
    have hnat : (1880439969 : ℕ)^4403*100000000000000^3379 ≤ 11332483228953^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880439969 10000000000 11332483228953 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676017779/1250000000 : ℝ)^4403 ≤ (44889917072021/100000000000000 : ℝ)^3379 := by
    have hnat : (676017779 : ℕ)^4403*100000000000000^3379 ≤ 44889917072021^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676017779 1250000000 44889917072021 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305001553/10000000000 : ℝ), (-1880439969/10000000000 : ℝ), (676017779/1250000000 : ℝ)] ![(5472199960339/12500000000000 : ℝ), (11332483228953/100000000000000 : ℝ), (44889917072021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305001553/10000000000 : ℝ)|^4403 ≤ (5472199960339/12500000000000 : ℝ)^3379
        have hw : |(5305001553/10000000000 : ℝ)|=(5305001553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1880439969/10000000000 : ℝ)|^4403 ≤ (11332483228953/100000000000000 : ℝ)^3379
        have hw : |(-1880439969/10000000000 : ℝ)|=(1880439969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676017779/1250000000 : ℝ)|^4403 ≤ (44889917072021/100000000000000 : ℝ)^3379
        have hw : |(676017779/1250000000 : ℝ)|=(676017779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_6 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305001551/10000000000 : ℝ)*x 0 + (5408142247/10000000000 : ℝ)*x 1 + (-117527497/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305001551/10000000000 : ℝ)^4403 ≤ (21888799830603/50000000000000 : ℝ)^3379 := by
    have hnat : (5305001551 : ℕ)^4403*50000000000000^3379 ≤ 21888799830603^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305001551 10000000000 21888799830603 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408142247/10000000000 : ℝ)^4403 ≤ (44889917234259/100000000000000 : ℝ)^3379 := by
    have hnat : (5408142247 : ℕ)^4403*100000000000000^3379 ≤ 44889917234259^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408142247 10000000000 44889917234259 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117527497/625000000 : ℝ)^4403 ≤ (2266496619091/20000000000000 : ℝ)^3379 := by
    have hnat : (117527497 : ℕ)^4403*20000000000000^3379 ≤ 2266496619091^3379*625000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117527497 625000000 2266496619091 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305001551/10000000000 : ℝ), (5408142247/10000000000 : ℝ), (-117527497/625000000 : ℝ)] ![(21888799830603/50000000000000 : ℝ), (44889917234259/100000000000000 : ℝ), (2266496619091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305001551/10000000000 : ℝ)|^4403 ≤ (21888799830603/50000000000000 : ℝ)^3379
        have hw : |(5305001551/10000000000 : ℝ)|=(5305001551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408142247/10000000000 : ℝ)|^4403 ≤ (44889917234259/100000000000000 : ℝ)^3379
        have hw : |(5408142247/10000000000 : ℝ)|=(5408142247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117527497/625000000 : ℝ)|^4403 ≤ (2266496619091/20000000000000 : ℝ)^3379
        have hw : |(-117527497/625000000 : ℝ)|=(117527497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s4_7 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300825637/10000000000 : ℝ)*x 0 + (4479625421/10000000000 : ℝ)*x 1 + (2064242291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300825637/10000000000 : ℝ)^4403 ≤ (4163038027439/12500000000000 : ℝ)^3379 := by
    have hnat : (4300825637 : ℕ)^4403*12500000000000^3379 ≤ 4163038027439^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300825637 10000000000 4163038027439 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479625421/10000000000 : ℝ)^4403 ≤ (35119725437721/100000000000000 : ℝ)^3379 := by
    have hnat : (4479625421 : ℕ)^4403*100000000000000^3379 ≤ 35119725437721^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479625421 10000000000 35119725437721 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064242291/5000000000 : ℝ)^4403 ≤ (15787985162409/50000000000000 : ℝ)^3379 := by
    have hnat : (2064242291 : ℕ)^4403*50000000000000^3379 ≤ 15787985162409^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064242291 5000000000 15787985162409 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300825637/10000000000 : ℝ), (4479625421/10000000000 : ℝ), (2064242291/5000000000 : ℝ)] ![(4163038027439/12500000000000 : ℝ), (35119725437721/100000000000000 : ℝ), (15787985162409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300825637/10000000000 : ℝ)|^4403 ≤ (4163038027439/12500000000000 : ℝ)^3379
        have hw : |(4300825637/10000000000 : ℝ)|=(4300825637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479625421/10000000000 : ℝ)|^4403 ≤ (35119725437721/100000000000000 : ℝ)^3379
        have hw : |(4479625421/10000000000 : ℝ)|=(4479625421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064242291/5000000000 : ℝ)|^4403 ≤ (15787985162409/50000000000000 : ℝ)^3379
        have hw : |(2064242291/5000000000 : ℝ)|=(2064242291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1479/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (2201/512 : ℝ) ≤ (8189392869430201/100000000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^2201 ≤ (8189392869430201/100000000000000000000 : ℝ)^512 := by
      have hnat : (11203 : ℕ)^2201*100000000000000000000^512 ≤ 8189392869430201^512*100000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 8189392869430201 100000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (8189392869430201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (747/5000 : ℝ) ^ (2201/512 : ℝ) ≤ (1129107048159283/4000000000000000000 : ℝ) := by
    have hpowers : (747/5000 : ℝ)^2201 ≤ (1129107048159283/4000000000000000000 : ℝ)^512 := by
      have hnat : (747 : ℕ)^2201*4000000000000000000^512 ≤ 1129107048159283^512*5000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        747 5000 1129107048159283 4000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (747/5000 : ℝ)) (X := (1129107048159283/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008189392869430201/50000000000000000000 : ℝ) ≤ (1000038098188761/1000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (50008189392869430201/50000000000000000000 : ℝ)^512 ≤ (1000038098188761/1000000000000000 : ℝ)^2201 := by
      have hnat : (50008189392869430201 : ℕ)^512*1000000000000000^2201 ≤ 1000038098188761^2201*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008189392869430201 50000000000000000000 1000038098188761 1000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000038098188761/1000000000000000 : ℝ)) (X := (50008189392869430201/50000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009104267268353069/25000000000000000000 : ℝ) ≤ (5000423510554601/5000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25009104267268353069/25000000000000000000 : ℝ)^512 ≤ (5000423510554601/5000000000000000 : ℝ)^2201 := by
      have hnat : (25009104267268353069 : ℕ)^512*5000000000000000^2201 ≤ 5000423510554601^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009104267268353069 25000000000000000000 5000423510554601 5000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000423510554601/5000000000000000 : ℝ)) (X := (25009104267268353069/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001129107048159283/2000000000000000000 : ℝ) ≤ (5000656530165397/5000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (2001129107048159283/2000000000000000000 : ℝ)^512 ≤ (5000656530165397/5000000000000000 : ℝ)^2201 := by
      have hnat : (2001129107048159283 : ℕ)^512*5000000000000000^2201 ≤ 5000656530165397^2201*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001129107048159283 2000000000000000000 5000656530165397 5000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000656530165397/5000000000000000 : ℝ)) (X := (2001129107048159283/2000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8189392869430201/100000000000000000000 : ℝ) ≤ ((18680490827257504109/18685000000000000000 : ℝ)+2*(58254902699/46712500000000 : ℝ)*(11203/100000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (18680490827257504109/18685000000000000000 : ℝ)+2*(58254902699/46712500000000 : ℝ)*(11203/100000 : ℝ)=(1000038098188761/1000000000000000 : ℝ) by norm_num, show 1+2*(8189392869430201/100000000000000000000 : ℝ)=(50008189392869430201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1129107048159283/4000000000000000000 : ℝ)+(8189392869430201/100000000000000000000 : ℝ) ≤ ((18680490827257504109/18685000000000000000 : ℝ)+(58254902699/46712500000000 : ℝ)*((747/5000 : ℝ)+(11203/100000 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (18680490827257504109/18685000000000000000 : ℝ)+(58254902699/46712500000000 : ℝ)*((747/5000 : ℝ)+(11203/100000 : ℝ))=(5000423510554601/5000000000000000 : ℝ) by norm_num, show 1+(1129107048159283/4000000000000000000 : ℝ)+(8189392869430201/100000000000000000000 : ℝ)=(25009104267268353069/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1129107048159283/4000000000000000000 : ℝ) ≤ ((18680490827257504109/18685000000000000000 : ℝ)+2*(58254902699/46712500000000 : ℝ)*(747/5000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (18680490827257504109/18685000000000000000 : ℝ)+2*(58254902699/46712500000000 : ℝ)*(747/5000 : ℝ)=(5000656530165397/5000000000000000 : ℝ) by norm_num, show 1+2*(1129107048159283/4000000000000000000 : ℝ)=(2001129107048159283/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18680490827257504109/18685000000000000000 : ℝ)*(X 1 0+X 2 0)+(58254902699/46712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (18680490827257504109/18685000000000000000 : ℝ)) (alpha := (58254902699/46712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18680490827257504109/18685000000000000000 : ℝ)*(X 0 1+X 2 1)+(58254902699/46712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (18680490827257504109/18685000000000000000 : ℝ)) (alpha := (58254902699/46712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18680490827257504109/18685000000000000000 : ℝ)*(X 0 2+X 1 2)+(58254902699/46712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (18680490827257504109/18685000000000000000 : ℝ)) (alpha := (58254902699/46712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1959686117/10000000000 : ℝ)*X 0 0+(5408741579/10000000000 : ℝ)*X 0 1+(5246060023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347351579/10000000000 : ℝ)*X 1 0+(-102126099/500000000 : ℝ)*X 1 1+(2623030049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347351393/10000000000 : ℝ)*X 2 0+(5246060183/10000000000 : ℝ)*X 2 1+(-510630529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300799937/10000000000 : ℝ)*X 0 0+(4127181421/10000000000 : ℝ)*X 0 1+(4480922007/10000000000 : ℝ)*X 0 2+(4300799937/10000000000 : ℝ)*X 1 0+(4127181421/10000000000 : ℝ)*X 1 1+(4480922007/10000000000 : ℝ)*X 1 2+(4300799937/10000000000 : ℝ)*X 2 0+(4127181421/10000000000 : ℝ)*X 2 1+(4480922007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7838791/40000000 : ℝ)*X 0 0+(2623328137/5000000000 : ℝ)*X 0 1+(5408142249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305001553/10000000000 : ℝ)*X 1 0+(-1880439969/10000000000 : ℝ)*X 1 1+(676017779/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305001551/10000000000 : ℝ)*X 2 0+(5408142247/10000000000 : ℝ)*X 2 1+(-117527497/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300825637/10000000000 : ℝ)*X 0 0+(4479625421/10000000000 : ℝ)*X 0 1+(2064242291/5000000000 : ℝ)*X 0 2+(4300825637/10000000000 : ℝ)*X 1 0+(4479625421/10000000000 : ℝ)*X 1 1+(2064242291/5000000000 : ℝ)*X 1 2+(4300825637/10000000000 : ℝ)*X 2 0+(4479625421/10000000000 : ℝ)*X 2 1+(2064242291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2332668445747722564387647247/467125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180714899/20000000000000 : ℝ)*(base19) + (367031179/50000000000000 : ℝ)*(base23) + (46600347/100000000000000 : ℝ)*(upper2) + (176460693/100000000000000 : ℝ)*(upper3) + (22909809/100000000000000 : ℝ)*(upper4) + (4486987764988961/100000000000000 : ℝ)*(major0) + (4486987764988961/100000000000000 : ℝ)*(major1) + (4486987764988961/100000000000000 : ℝ)*(major2) + (6147005762630153/100000000000000 : ℝ)*(sp0) + (614702331856737/10000000000000 : ℝ)*(sp1) + (6147023488079507/100000000000000 : ℝ)*(sp2) + (2826939883139689/100000000000000 : ℝ)*(sp3) + (18459511713/100000000000000 : ℝ)*(sp4) + (11258240669/100000000000000 : ℝ)*(sp7) + (1413475570690179/50000000000000 : ℝ)*(f.failure) + (1229404844428373/20000000000000 : ℝ)*(f.sum) + (31453092755837/18685000000000000000000000000 : ℝ)*base65 + (1819673483696759251/1868500000000000000000000000000000 : ℝ)*base68 + (15084722204241759251/1868500000000000000000000000000000 : ℝ)*base70 + (356403130063259251/1868500000000000000000000000000000 : ℝ)*base72 + (47668805910541/9342500000000000000000000000 : ℝ)*base73 + (25445908693584240749/1868500000000000000000000000000000 : ℝ)*base75 + (9070762050301759251/1868500000000000000000000000000000 : ℝ)*base78 + (1619371838288759251/1868500000000000000000000000000000 : ℝ)*base80 + (79417015511147/18685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (26107621/5000000000000000000000 : ℝ)*base90 + (26107621/5000000000000000000000 : ℝ)*base92 + (26107621/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2798350735969399966761602661/467125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37151823/4000000000000 : ℝ)*(base19) + (104005413/10000000000000 : ℝ)*(base23) + (108249179/100000000000000 : ℝ)*(upper3) + (51516613/100000000000000 : ℝ)*(lower4) + (130723711/100000000000000 : ℝ)*(upper5) + (4520173801868843/100000000000000 : ℝ)*(major0) + (4520173801868843/100000000000000 : ℝ)*(major1) + (4520173801868843/100000000000000 : ℝ)*(major2) + (4746255829/25000000000000 : ℝ)*(sp1) + (4209989199/20000000000000 : ℝ)*(sp2) + (1238497591707469/20000000000000 : ℝ)*(sp4) + (3096234022359227/50000000000000 : ℝ)*(sp5) + (6192465868537221/100000000000000 : ℝ)*(sp6) + (1423929722757129/50000000000000 : ℝ)*(sp7) + (1423929722757129/50000000000000 : ℝ)*(f.failure) + (1238497591707469/20000000000000 : ℝ)*(f.sum) + (8051677177051/4671250000000000000000000000 : ℝ)*base66 + (13221377746183624113/1868500000000000000000000000000000 : ℝ)*base68 + (17194843732624124113/1868500000000000000000000000000000 : ℝ)*base70 + (6582289048272375887/1868500000000000000000000000000000 : ℝ)*base71 + (23891047045291/4671250000000000000000000000 : ℝ)*base74 + (12627492405707624113/1868500000000000000000000000000000 : ℝ)*base76 + (12779249546657624113/1868500000000000000000000000000000 : ℝ)*base78 + (29373327301510624113/1868500000000000000000000000000000 : ℝ)*base80 + (5160094575573/2335625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (50469329/5000000000000000000000 : ℝ)*base89 + (50469329/5000000000000000000000 : ℝ)*base91 + (50469329/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1443_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1443_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1443_s5_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979904599/5000000000 : ℝ)*x 0 + (2703828361/5000000000 : ℝ)*x 1 + (2623531789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979904599/5000000000 : ℝ)^4403 ≤ (11959703900759/100000000000000 : ℝ)^3379 := by
    have hnat : (979904599 : ℕ)^4403*100000000000000^3379 ≤ 11959703900759^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979904599 5000000000 11959703900759 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703828361/5000000000 : ℝ)^4403 ≤ (11221166483409/25000000000000 : ℝ)^3379 := by
    have hnat : (2703828361 : ℕ)^4403*25000000000000^3379 ≤ 11221166483409^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703828361 5000000000 11221166483409 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623531789/5000000000 : ℝ)^4403 ≤ (21577815074563/50000000000000 : ℝ)^3379 := by
    have hnat : (2623531789 : ℕ)^4403*50000000000000^3379 ≤ 21577815074563^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623531789 5000000000 21577815074563 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979904599/5000000000 : ℝ), (2703828361/5000000000 : ℝ), (2623531789/5000000000 : ℝ)] ![(11959703900759/100000000000000 : ℝ), (11221166483409/25000000000000 : ℝ), (21577815074563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979904599/5000000000 : ℝ)|^4403 ≤ (11959703900759/100000000000000 : ℝ)^3379
        have hw : |(-979904599/5000000000 : ℝ)|=(979904599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703828361/5000000000 : ℝ)|^4403 ≤ (11221166483409/25000000000000 : ℝ)^3379
        have hw : |(2703828361/5000000000 : ℝ)|=(2703828361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623531789/5000000000 : ℝ)|^4403 ≤ (21577815074563/50000000000000 : ℝ)^3379
        have hw : |(2623531789/5000000000 : ℝ)|=(2623531789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336767531/2500000000 : ℝ)*x 0 + (-1020781329/5000000000 : ℝ)*x 1 + (5247063909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336767531/2500000000 : ℝ)^4403 ≤ (22115251371267/50000000000000 : ℝ)^3379 := by
    have hnat : (1336767531 : ℕ)^4403*50000000000000^3379 ≤ 22115251371267^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336767531 2500000000 22115251371267 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020781329/5000000000 : ℝ)^4403 ≤ (12613863554439/100000000000000 : ℝ)^3379 := by
    have hnat : (1020781329 : ℕ)^4403*100000000000000^3379 ≤ 12613863554439^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020781329 5000000000 12613863554439 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247063909/10000000000 : ℝ)^4403 ≤ (21577816848261/50000000000000 : ℝ)^3379 := by
    have hnat : (5247063909 : ℕ)^4403*50000000000000^3379 ≤ 21577816848261^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247063909 10000000000 21577816848261 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336767531/2500000000 : ℝ), (-1020781329/5000000000 : ℝ), (5247063909/10000000000 : ℝ)] ![(22115251371267/50000000000000 : ℝ), (12613863554439/100000000000000 : ℝ), (21577816848261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336767531/2500000000 : ℝ)|^4403 ≤ (22115251371267/50000000000000 : ℝ)^3379
        have hw : |(1336767531/2500000000 : ℝ)|=(1336767531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020781329/5000000000 : ℝ)|^4403 ≤ (12613863554439/100000000000000 : ℝ)^3379
        have hw : |(-1020781329/5000000000 : ℝ)|=(1020781329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247063909/10000000000 : ℝ)|^4403 ≤ (21577816848261/50000000000000 : ℝ)^3379
        have hw : |(5247063909/10000000000 : ℝ)|=(5247063909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347070097/10000000000 : ℝ)*x 0 + (131176593/250000000 : ℝ)*x 1 + (-31899421/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347070097/10000000000 : ℝ)^4403 ≤ (44230502451509/100000000000000 : ℝ)^3379 := by
    have hnat : (5347070097 : ℕ)^4403*100000000000000^3379 ≤ 44230502451509^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347070097 10000000000 44230502451509 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131176593/250000000 : ℝ)^4403 ≤ (4315563167097/10000000000000 : ℝ)^3379 := by
    have hnat : (131176593 : ℕ)^4403*10000000000000^3379 ≤ 4315563167097^3379*250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131176593 250000000 4315563167097 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31899421/156250000 : ℝ)^4403 ≤ (3153466464251/25000000000000 : ℝ)^3379 := by
    have hnat : (31899421 : ℕ)^4403*25000000000000^3379 ≤ 3153466464251^3379*156250000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31899421 156250000 3153466464251 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347070097/10000000000 : ℝ), (131176593/250000000 : ℝ), (-31899421/156250000 : ℝ)] ![(44230502451509/100000000000000 : ℝ), (4315563167097/10000000000000 : ℝ), (3153466464251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347070097/10000000000 : ℝ)|^4403 ≤ (44230502451509/100000000000000 : ℝ)^3379
        have hw : |(5347070097/10000000000 : ℝ)|=(5347070097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131176593/250000000 : ℝ)|^4403 ≤ (4315563167097/10000000000000 : ℝ)^3379
        have hw : |(131176593/250000000 : ℝ)|=(131176593/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31899421/156250000 : ℝ)|^4403 ≤ (3153466464251/25000000000000 : ℝ)^3379
        have hw : |(-31899421/156250000 : ℝ)|=(31899421/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150436933/5000000000 : ℝ)*x 0 + (2064721831/5000000000 : ℝ)*x 1 + (559830259/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150436933/5000000000 : ℝ)^4403 ≤ (16652395435479/50000000000000 : ℝ)^3379 := by
    have hnat : (2150436933 : ℕ)^4403*50000000000000^3379 ≤ 16652395435479^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150436933 5000000000 16652395435479 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064721831/5000000000 : ℝ)^4403 ≤ (31585528976863/100000000000000 : ℝ)^3379 := by
    have hnat : (2064721831 : ℕ)^4403*100000000000000^3379 ≤ 31585528976863^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064721831 5000000000 31585528976863 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559830259/1250000000 : ℝ)^4403 ≤ (8777420033113/25000000000000 : ℝ)^3379 := by
    have hnat : (559830259 : ℕ)^4403*25000000000000^3379 ≤ 8777420033113^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559830259 1250000000 8777420033113 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150436933/5000000000 : ℝ), (2064721831/5000000000 : ℝ), (559830259/1250000000 : ℝ)] ![(16652395435479/50000000000000 : ℝ), (31585528976863/100000000000000 : ℝ), (8777420033113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150436933/5000000000 : ℝ)|^4403 ≤ (16652395435479/50000000000000 : ℝ)^3379
        have hw : |(2150436933/5000000000 : ℝ)|=(2150436933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064721831/5000000000 : ℝ)|^4403 ≤ (31585528976863/100000000000000 : ℝ)^3379
        have hw : |(2064721831/5000000000 : ℝ)|=(2064721831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559830259/1250000000 : ℝ)|^4403 ≤ (8777420033113/25000000000000 : ℝ)^3379
        have hw : |(559830259/1250000000 : ℝ)|=(559830259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979910129/5000000000 : ℝ)*x 0 + (5247644921/10000000000 : ℝ)*x 1 + (1081414503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979910129/5000000000 : ℝ)^4403 ≤ (11959791848083/100000000000000 : ℝ)^3379 := by
    have hnat : (979910129 : ℕ)^4403*100000000000000^3379 ≤ 11959791848083^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979910129 5000000000 11959791848083 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247644921/10000000000 : ℝ)^4403 ≤ (43161860627139/100000000000000 : ℝ)^3379 := by
    have hnat : (5247644921 : ℕ)^4403*100000000000000^3379 ≤ 43161860627139^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247644921 10000000000 43161860627139 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081414503/2000000000 : ℝ)^4403 ≤ (22439173752949/50000000000000 : ℝ)^3379 := by
    have hnat : (1081414503 : ℕ)^4403*50000000000000^3379 ≤ 22439173752949^3379*2000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081414503 2000000000 22439173752949 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979910129/5000000000 : ℝ), (5247644921/10000000000 : ℝ), (1081414503/2000000000 : ℝ)] ![(11959791848083/100000000000000 : ℝ), (43161860627139/100000000000000 : ℝ), (22439173752949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979910129/5000000000 : ℝ)|^4403 ≤ (11959791848083/100000000000000 : ℝ)^3379
        have hw : |(-979910129/5000000000 : ℝ)|=(979910129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247644921/10000000000 : ℝ)|^4403 ≤ (43161860627139/100000000000000 : ℝ)^3379
        have hw : |(5247644921/10000000000 : ℝ)|=(5247644921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081414503/2000000000 : ℝ)|^4403 ≤ (22439173752949/50000000000000 : ℝ)^3379
        have hw : |(1081414503/2000000000 : ℝ)|=(1081414503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326316023/2500000000 : ℝ)*x 0 + (-1881553657/10000000000 : ℝ)*x 1 + (5407072523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326316023/2500000000 : ℝ)^4403 ≤ (8756084553611/20000000000000 : ℝ)^3379 := by
    have hnat : (1326316023 : ℕ)^4403*20000000000000^3379 ≤ 8756084553611^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326316023 2500000000 8756084553611 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881553657/10000000000 : ℝ)^4403 ≤ (708826850899/6250000000000 : ℝ)^3379 := by
    have hnat : (1881553657 : ℕ)^4403*6250000000000^3379 ≤ 708826850899^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881553657 10000000000 708826850899 6250000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407072523/10000000000 : ℝ)^4403 ≤ (44878347592419/100000000000000 : ℝ)^3379 := by
    have hnat : (5407072523 : ℕ)^4403*100000000000000^3379 ≤ 44878347592419^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407072523 10000000000 44878347592419 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326316023/2500000000 : ℝ), (-1881553657/10000000000 : ℝ), (5407072523/10000000000 : ℝ)] ![(8756084553611/20000000000000 : ℝ), (708826850899/6250000000000 : ℝ), (44878347592419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326316023/2500000000 : ℝ)|^4403 ≤ (8756084553611/20000000000000 : ℝ)^3379
        have hw : |(1326316023/2500000000 : ℝ)|=(1326316023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881553657/10000000000 : ℝ)|^4403 ≤ (708826850899/6250000000000 : ℝ)^3379
        have hw : |(-1881553657/10000000000 : ℝ)|=(1881553657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407072523/10000000000 : ℝ)|^4403 ≤ (44878347592419/100000000000000 : ℝ)^3379
        have hw : |(5407072523/10000000000 : ℝ)|=(5407072523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_6 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305264059/10000000000 : ℝ)*x 0 + (5407072433/10000000000 : ℝ)*x 1 + (-470388457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305264059/10000000000 : ℝ)^4403 ≤ (43780422413203/100000000000000 : ℝ)^3379 := by
    have hnat : (5305264059 : ℕ)^4403*100000000000000^3379 ≤ 43780422413203^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305264059 10000000000 43780422413203 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407072433/10000000000 : ℝ)^4403 ≤ (897566932381/2000000000000 : ℝ)^3379 := by
    have hnat : (5407072433 : ℕ)^4403*2000000000000^3379 ≤ 897566932381^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407072433 10000000000 897566932381 2000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470388457/2500000000 : ℝ)^4403 ≤ (11341230957459/100000000000000 : ℝ)^3379 := by
    have hnat : (470388457 : ℕ)^4403*100000000000000^3379 ≤ 11341230957459^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470388457 2500000000 11341230957459 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305264059/10000000000 : ℝ), (5407072433/10000000000 : ℝ), (-470388457/2500000000 : ℝ)] ![(43780422413203/100000000000000 : ℝ), (897566932381/2000000000000 : ℝ), (11341230957459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305264059/10000000000 : ℝ)|^4403 ≤ (43780422413203/100000000000000 : ℝ)^3379
        have hw : |(5305264059/10000000000 : ℝ)|=(5305264059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407072433/10000000000 : ℝ)|^4403 ≤ (897566932381/2000000000000 : ℝ)^3379
        have hw : |(5407072433/10000000000 : ℝ)|=(5407072433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470388457/2500000000 : ℝ)|^4403 ≤ (11341230957459/100000000000000 : ℝ)^3379
        have hw : |(-470388457/2500000000 : ℝ)|=(470388457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s5_7 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300898587/10000000000 : ℝ)*x 0 + (895475739/2000000000 : ℝ)*x 1 + (4130713363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300898587/10000000000 : ℝ)^4403 ≤ (33305040317169/100000000000000 : ℝ)^3379 := by
    have hnat : (4300898587 : ℕ)^4403*100000000000000^3379 ≤ 33305040317169^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300898587 10000000000 33305040317169 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895475739/2000000000 : ℝ)^4403 ≤ (7019355041921/20000000000000 : ℝ)^3379 := by
    have hnat : (895475739 : ℕ)^4403*20000000000000^3379 ≤ 7019355041921^3379*2000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895475739 2000000000 7019355041921 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130713363/10000000000 : ℝ)^4403 ≤ (7899546115487/25000000000000 : ℝ)^3379 := by
    have hnat : (4130713363 : ℕ)^4403*25000000000000^3379 ≤ 7899546115487^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130713363 10000000000 7899546115487 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300898587/10000000000 : ℝ), (895475739/2000000000 : ℝ), (4130713363/10000000000 : ℝ)] ![(33305040317169/100000000000000 : ℝ), (7019355041921/20000000000000 : ℝ), (7899546115487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300898587/10000000000 : ℝ)|^4403 ≤ (33305040317169/100000000000000 : ℝ)^3379
        have hw : |(4300898587/10000000000 : ℝ)|=(4300898587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895475739/2000000000 : ℝ)|^4403 ≤ (7019355041921/20000000000000 : ℝ)^3379
        have hw : |(895475739/2000000000 : ℝ)|=(895475739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130713363/10000000000 : ℝ)|^4403 ≤ (7899546115487/25000000000000 : ℝ)^3379
        have hw : |(4130713363/10000000000 : ℝ)|=(4130713363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/6250 : ℝ) ^ (2201/512 : ℝ) ≤ (864176461010193/10000000000000000000 : ℝ) := by
    have hpowers : (709/6250 : ℝ)^2201 ≤ (864176461010193/10000000000000000000 : ℝ)^512 := by
      have hnat : (709 : ℕ)^2201*10000000000000000000^512 ≤ 864176461010193^512*6250^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 6250 864176461010193 10000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/6250 : ℝ)) (X := (864176461010193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1479/10000 : ℝ) ^ (2201/512 : ℝ) ≤ (6757341231024077/25000000000000000000 : ℝ) := by
    have hpowers : (1479/10000 : ℝ)^2201 ≤ (6757341231024077/25000000000000000000 : ℝ)^512 := by
      have hnat : (1479 : ℕ)^2201*25000000000000000000^512 ≤ 6757341231024077^512*10000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1479 10000 6757341231024077 25000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1479/10000 : ℝ)) (X := (6757341231024077/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000864176461010193/5000000000000000000 : ℝ) ≤ (2000080405090301/2000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (5000864176461010193/5000000000000000000 : ℝ)^512 ≤ (2000080405090301/2000000000000000 : ℝ)^2201 := by
      have hnat : (5000864176461010193 : ℕ)^512*2000000000000000^2201 ≤ 2000080405090301^2201*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000864176461010193 5000000000000000000 2000080405090301 2000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080405090301/2000000000000000 : ℝ)) (X := (5000864176461010193/5000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017835564767099119/50000000000000000000 : ℝ) ≤ (2500207418436769/2500000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (50017835564767099119/50000000000000000000 : ℝ)^512 ≤ (2500207418436769/2500000000000000 : ℝ)^2201 := by
      have hnat : (50017835564767099119 : ℕ)^512*2500000000000000^2201 ≤ 2500207418436769^2201*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017835564767099119 50000000000000000000 2500207418436769 2500000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500207418436769/2500000000000000 : ℝ)) (X := (50017835564767099119/50000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506757341231024077/12500000000000000000 : ℝ) ≤ (10001257322042647/10000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (12506757341231024077/12500000000000000000 : ℝ)^512 ≤ (10001257322042647/10000000000000000 : ℝ)^2201 := by
      have hnat : (12506757341231024077 : ℕ)^512*10000000000000000^2201 ≤ 10001257322042647^2201*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506757341231024077 12500000000000000000 10001257322042647 10000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001257322042647/10000000000000000 : ℝ)) (X := (12506757341231024077/12500000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(864176461010193/10000000000000000000 : ℝ) ≤ ((17225841447587985691/17230000000000000000 : ℝ)+2*(427648295571/344600000000000 : ℝ)*(709/6250 : ℝ))^(2201/512 : ℝ) := by
    rw [show (17225841447587985691/17230000000000000000 : ℝ)+2*(427648295571/344600000000000 : ℝ)*(709/6250 : ℝ)=(2000080405090301/2000000000000000 : ℝ) by norm_num, show 1+2*(864176461010193/10000000000000000000 : ℝ)=(5000864176461010193/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6757341231024077/25000000000000000000 : ℝ)+(864176461010193/10000000000000000000 : ℝ) ≤ ((17225841447587985691/17230000000000000000 : ℝ)+(427648295571/344600000000000 : ℝ)*((1479/10000 : ℝ)+(709/6250 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (17225841447587985691/17230000000000000000 : ℝ)+(427648295571/344600000000000 : ℝ)*((1479/10000 : ℝ)+(709/6250 : ℝ))=(2500207418436769/2500000000000000 : ℝ) by norm_num, show 1+(6757341231024077/25000000000000000000 : ℝ)+(864176461010193/10000000000000000000 : ℝ)=(50017835564767099119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6757341231024077/25000000000000000000 : ℝ) ≤ ((17225841447587985691/17230000000000000000 : ℝ)+2*(427648295571/344600000000000 : ℝ)*(1479/10000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (17225841447587985691/17230000000000000000 : ℝ)+2*(427648295571/344600000000000 : ℝ)*(1479/10000 : ℝ)=(10001257322042647/10000000000000000 : ℝ) by norm_num, show 1+2*(6757341231024077/25000000000000000000 : ℝ)=(12506757341231024077/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17225841447587985691/17230000000000000000 : ℝ)*(X 1 0+X 2 0)+(427648295571/344600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (17225841447587985691/17230000000000000000 : ℝ)) (alpha := (427648295571/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17225841447587985691/17230000000000000000 : ℝ)*(X 0 1+X 2 1)+(427648295571/344600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (17225841447587985691/17230000000000000000 : ℝ)) (alpha := (427648295571/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17225841447587985691/17230000000000000000 : ℝ)*(X 0 2+X 1 2)+(427648295571/344600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (17225841447587985691/17230000000000000000 : ℝ)) (alpha := (427648295571/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-979904599/5000000000 : ℝ)*X 0 0+(2703828361/5000000000 : ℝ)*X 0 1+(2623531789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336767531/2500000000 : ℝ)*X 1 0+(-1020781329/5000000000 : ℝ)*X 1 1+(5247063909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347070097/10000000000 : ℝ)*X 2 0+(131176593/250000000 : ℝ)*X 2 1+(-31899421/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150436933/5000000000 : ℝ)*X 0 0+(2064721831/5000000000 : ℝ)*X 0 1+(559830259/1250000000 : ℝ)*X 0 2+(2150436933/5000000000 : ℝ)*X 1 0+(2064721831/5000000000 : ℝ)*X 1 1+(559830259/1250000000 : ℝ)*X 1 2+(2150436933/5000000000 : ℝ)*X 2 0+(2064721831/5000000000 : ℝ)*X 2 1+(559830259/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-979910129/5000000000 : ℝ)*X 0 0+(5247644921/10000000000 : ℝ)*X 0 1+(1081414503/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326316023/2500000000 : ℝ)*X 1 0+(-1881553657/10000000000 : ℝ)*X 1 1+(5407072523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305264059/10000000000 : ℝ)*X 2 0+(5407072433/10000000000 : ℝ)*X 2 1+(-470388457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300898587/10000000000 : ℝ)*X 0 0+(895475739/2000000000 : ℝ)*X 0 1+(4130713363/10000000000 : ℝ)*X 0 2+(4300898587/10000000000 : ℝ)*X 1 0+(895475739/2000000000 : ℝ)*X 1 1+(4130713363/10000000000 : ℝ)*X 1 2+(4300898587/10000000000 : ℝ)*X 2 0+(895475739/2000000000 : ℝ)*X 2 1+(4130713363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8522849072363973833324531217/861500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1432556689/100000000000000 : ℝ)*(base19) + (680225641/50000000000000 : ℝ)*(base23) + (19172627/50000000000000 : ℝ)*(upper2) + (8016861/2000000000000 : ℝ)*(upper3) + (12017529/20000000000000 : ℝ)*(upper4) + (4545359888725729/100000000000000 : ℝ)*(major0) + (4545359888725729/100000000000000 : ℝ)*(major1) + (4545359888725729/100000000000000 : ℝ)*(major2) + (6226961548919951/100000000000000 : ℝ)*(sp0) + (1556747624845061/25000000000000 : ℝ)*(sp1) + (6226990571485651/100000000000000 : ℝ)*(sp2) + (715927863971241/25000000000000 : ℝ)*(sp3) + (15191508491/50000000000000 : ℝ)*(sp4) + (8029930871/50000000000000 : ℝ)*(sp7) + (572745503149341/20000000000000 : ℝ)*(f.failure) + (6226991931936933/100000000000000 : ℝ)*(f.sum) + (83924968968261/17230000000000000000000000000 : ℝ)*base66 + (2567570526957506261/1723000000000000000000000000000000 : ℝ)*base68 + (33123535546937506261/1723000000000000000000000000000000 : ℝ)*base70 + (4972785023193506261/1723000000000000000000000000000000 : ℝ)*base72 + (39781322706121/17230000000000000000000000000 : ℝ)*base74 + (20496363347538493739/1723000000000000000000000000000000 : ℝ)*base75 + (25852870739386506261/1723000000000000000000000000000000 : ℝ)*base78 + (13372638752294493739/1723000000000000000000000000000000 : ℝ)*base79 + (75812541982041/17230000000000000000000000000 : ℝ)*base82 + (4516859/2000000000000000000000 : ℝ)*base90 + (4516859/2000000000000000000000 : ℝ)*base92 + (4516859/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54383159348056533779091243/26921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751890121/100000000000000 : ℝ)*(base19) + (756131057/100000000000000 : ℝ)*(base23) + (4269393/25000000000000 : ℝ)*(upper3) + (42708833/100000000000000 : ℝ)*(lower4) + (71539569415333/1562500000000 : ℝ)*(major0) + (71539569415333/1562500000000 : ℝ)*(major1) + (71539569415333/1562500000000 : ℝ)*(major2) + (20828757431/100000000000000 : ℝ)*(sp1) + (100638733/625000000000 : ℝ)*(sp2) + (122697261/20000000000000 : ℝ)*(sp3) + (313621874635003/5000000000000 : ℝ)*(sp4) + (6272415912052507/100000000000000 : ℝ)*(sp5) + (3136210317185861/50000000000000 : ℝ)*(sp6) + (288462671164171/10000000000000 : ℝ)*(sp7) + (576925465025603/20000000000000 : ℝ)*(f.failure) + (313621874635003/5000000000000 : ℝ)*(f.sum) + (2425536567819/2153750000000000000000000000 : ℝ)*base65 + (87613527206912397/26921875000000000000000000000000 : ℝ)*base68 + (434185096071131147/26921875000000000000000000000000 : ℝ)*base70 + (30556015207912397/26921875000000000000000000000000 : ℝ)*base72 + (30937395517831/8615000000000000000000000000 : ℝ)*base73 + (559668978539493853/26921875000000000000000000000000 : ℝ)*base75 + (135726472542443647/26921875000000000000000000000000 : ℝ)*base78 + (19098701864681353/26921875000000000000000000000000 : ℝ)*base79 + (554354230933/4307500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20728997/2000000000000000000000 : ℝ)*base90 + (20728997/2000000000000000000000 : ℝ)*base92 + (20728997/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1443_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1443_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1443_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1443_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1443_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1443_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1443_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

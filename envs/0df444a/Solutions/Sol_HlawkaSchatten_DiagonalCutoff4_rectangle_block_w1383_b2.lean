-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1383_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:11.043583+00:00
-- url     : https://prove2.me/submissions/05d8aaf8-1903-4807-9949-ff13bb168288

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
theorem support_rectangle_w1383_s6_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-251133757/1250000000 : ℝ)*x 0 + (1352650063/2500000000 : ℝ)*x 1 + (5245776207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251133757/1250000000 : ℝ)^4343 ≤ (3061191413643/25000000000000 : ℝ)^3319 := by
    have hnat : (251133757 : ℕ)^4343*25000000000000^3319 ≤ 3061191413643^3319*1250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251133757 1250000000 3061191413643 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352650063/2500000000 : ℝ)^4343 ≤ (44765615105243/100000000000000 : ℝ)^3319 := by
    have hnat : (1352650063 : ℕ)^4343*100000000000000^3319 ≤ 44765615105243^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352650063 2500000000 44765615105243 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245776207/10000000000 : ℝ)^4343 ≤ (42989619225733/100000000000000 : ℝ)^3319 := by
    have hnat : (5245776207 : ℕ)^4343*100000000000000^3319 ≤ 42989619225733^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245776207 10000000000 42989619225733 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251133757/1250000000 : ℝ), (1352650063/2500000000 : ℝ), (5245776207/10000000000 : ℝ)] ![(3061191413643/25000000000000 : ℝ), (44765615105243/100000000000000 : ℝ), (42989619225733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251133757/1250000000 : ℝ)|^4343 ≤ (3061191413643/25000000000000 : ℝ)^3319
        have hw : |(-251133757/1250000000 : ℝ)|=(251133757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352650063/2500000000 : ℝ)|^4343 ≤ (44765615105243/100000000000000 : ℝ)^3319
        have hw : |(1352650063/2500000000 : ℝ)|=(1352650063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245776207/10000000000 : ℝ)|^4343 ≤ (42989619225733/100000000000000 : ℝ)^3319
        have hw : |(5245776207/10000000000 : ℝ)|=(5245776207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348254811/10000000000 : ℝ)*x 0 + (-2093017981/10000000000 : ℝ)*x 1 + (1049155231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348254811/10000000000 : ℝ)^4343 ≤ (44091845128661/100000000000000 : ℝ)^3319 := by
    have hnat : (5348254811 : ℕ)^4343*100000000000000^3319 ≤ 44091845128661^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348254811 10000000000 44091845128661 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093017981/10000000000 : ℝ)^4343 ≤ (6459268091693/50000000000000 : ℝ)^3319 := by
    have hnat : (2093017981 : ℕ)^4343*50000000000000^3319 ≤ 6459268091693^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093017981 10000000000 6459268091693 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049155231/2000000000 : ℝ)^4343 ≤ (42989618668111/100000000000000 : ℝ)^3319 := by
    have hnat : (1049155231 : ℕ)^4343*100000000000000^3319 ≤ 42989618668111^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049155231 2000000000 42989618668111 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348254811/10000000000 : ℝ), (-2093017981/10000000000 : ℝ), (1049155231/2000000000 : ℝ)] ![(44091845128661/100000000000000 : ℝ), (6459268091693/50000000000000 : ℝ), (42989618668111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348254811/10000000000 : ℝ)|^4343 ≤ (44091845128661/100000000000000 : ℝ)^3319
        have hw : |(5348254811/10000000000 : ℝ)|=(5348254811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093017981/10000000000 : ℝ)|^4343 ≤ (6459268091693/50000000000000 : ℝ)^3319
        have hw : |(-2093017981/10000000000 : ℝ)|=(2093017981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049155231/2000000000 : ℝ)|^4343 ≤ (42989618668111/100000000000000 : ℝ)^3319
        have hw : |(1049155231/2000000000 : ℝ)|=(1049155231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069650947/2000000000 : ℝ)*x 0 + (1311444051/2500000000 : ℝ)*x 1 + (-2093018019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069650947/2000000000 : ℝ)^4343 ≤ (11022961077199/25000000000000 : ℝ)^3319 := by
    have hnat : (1069650947 : ℕ)^4343*25000000000000^3319 ≤ 11022961077199^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069650947 2000000000 11022961077199 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311444051/2500000000 : ℝ)^4343 ≤ (21494809596781/50000000000000 : ℝ)^3319 := by
    have hnat : (1311444051 : ℕ)^4343*50000000000000^3319 ≤ 21494809596781^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311444051 2500000000 21494809596781 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093018019/10000000000 : ℝ)^4343 ≤ (3229634122573/25000000000000 : ℝ)^3319 := by
    have hnat : (2093018019 : ℕ)^4343*25000000000000^3319 ≤ 3229634122573^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093018019 10000000000 3229634122573 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069650947/2000000000 : ℝ), (1311444051/2500000000 : ℝ), (-2093018019/10000000000 : ℝ)] ![(11022961077199/25000000000000 : ℝ), (21494809596781/50000000000000 : ℝ), (3229634122573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069650947/2000000000 : ℝ)|^4343 ≤ (11022961077199/25000000000000 : ℝ)^3319
        have hw : |(1069650947/2000000000 : ℝ)|=(1069650947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311444051/2500000000 : ℝ)|^4343 ≤ (21494809596781/50000000000000 : ℝ)^3319
        have hw : |(1311444051/2500000000 : ℝ)|=(1311444051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093018019/10000000000 : ℝ)|^4343 ≤ (3229634122573/25000000000000 : ℝ)^3319
        have hw : |(-2093018019/10000000000 : ℝ)|=(2093018019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17264043/40000000 : ℝ)*x 0 + (828798669/2000000000 : ℝ)*x 1 + (89891243/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17264043/40000000 : ℝ)^4343 ≤ (666078997201/2000000000000 : ℝ)^3319 := by
    have hnat : (17264043 : ℕ)^4343*2000000000000^3319 ≤ 666078997201^3319*40000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17264043 40000000 666078997201 2000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828798669/2000000000 : ℝ)^4343 ≤ (15788927441877/50000000000000 : ℝ)^3319 := by
    have hnat : (828798669 : ℕ)^4343*50000000000000^3319 ≤ 15788927441877^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828798669 2000000000 15788927441877 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89891243/200000000 : ℝ)^4343 ≤ (4389774405723/12500000000000 : ℝ)^3319 := by
    have hnat : (89891243 : ℕ)^4343*12500000000000^3319 ≤ 4389774405723^3319*200000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89891243 200000000 4389774405723 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17264043/40000000 : ℝ), (828798669/2000000000 : ℝ), (89891243/200000000 : ℝ)] ![(666078997201/2000000000000 : ℝ), (15788927441877/50000000000000 : ℝ), (4389774405723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17264043/40000000 : ℝ)|^4343 ≤ (666078997201/2000000000000 : ℝ)^3319
        have hw : |(17264043/40000000 : ℝ)|=(17264043/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828798669/2000000000 : ℝ)|^4343 ≤ (15788927441877/50000000000000 : ℝ)^3319
        have hw : |(828798669/2000000000 : ℝ)|=(828798669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89891243/200000000 : ℝ)|^4343 ≤ (4389774405723/12500000000000 : ℝ)^3319
        have hw : |(89891243/200000000 : ℝ)|=(89891243/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15695953/78125000 : ℝ)*x 0 + (5246368313/10000000000 : ℝ)*x 1 + (1352501241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15695953/78125000 : ℝ)^4343 ≤ (6122430391027/50000000000000 : ℝ)^3319 := by
    have hnat : (15695953 : ℕ)^4343*50000000000000^3319 ≤ 6122430391027^3319*78125000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15695953 78125000 6122430391027 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246368313/10000000000 : ℝ)^4343 ≤ (5374496097867/12500000000000 : ℝ)^3319 := by
    have hnat : (5246368313 : ℕ)^4343*12500000000000^3319 ≤ 5374496097867^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246368313 10000000000 5374496097867 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352501241/2500000000 : ℝ)^4343 ≤ (44759170424003/100000000000000 : ℝ)^3319 := by
    have hnat : (1352501241 : ℕ)^4343*100000000000000^3319 ≤ 44759170424003^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352501241 2500000000 44759170424003 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15695953/78125000 : ℝ), (5246368313/10000000000 : ℝ), (1352501241/2500000000 : ℝ)] ![(6122430391027/50000000000000 : ℝ), (5374496097867/12500000000000 : ℝ), (44759170424003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15695953/78125000 : ℝ)|^4343 ≤ (6122430391027/50000000000000 : ℝ)^3319
        have hw : |(-15695953/78125000 : ℝ)|=(15695953/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246368313/10000000000 : ℝ)|^4343 ≤ (5374496097867/12500000000000 : ℝ)^3319
        have hw : |(5246368313/10000000000 : ℝ)|=(5246368313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352501241/2500000000 : ℝ)|^4343 ≤ (44759170424003/100000000000000 : ℝ)^3319
        have hw : |(1352501241/2500000000 : ℝ)|=(1352501241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305606051/10000000000 : ℝ)*x 0 + (-482197319/2500000000 : ℝ)*x 1 + (2705002483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305606051/10000000000 : ℝ)^4343 ≤ (436323302193/1000000000000 : ℝ)^3319 := by
    have hnat : (5305606051 : ℕ)^4343*1000000000000^3319 ≤ 436323302193^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305606051 10000000000 436323302193 1000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482197319/2500000000 : ℝ)^4343 ≤ (5804249663599/50000000000000 : ℝ)^3319 := by
    have hnat : (482197319 : ℕ)^4343*50000000000000^3319 ≤ 5804249663599^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482197319 2500000000 5804249663599 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705002483/5000000000 : ℝ)^4343 ≤ (8951834089131/20000000000000 : ℝ)^3319 := by
    have hnat : (2705002483 : ℕ)^4343*20000000000000^3319 ≤ 8951834089131^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705002483 5000000000 8951834089131 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305606051/10000000000 : ℝ), (-482197319/2500000000 : ℝ), (2705002483/5000000000 : ℝ)] ![(436323302193/1000000000000 : ℝ), (5804249663599/50000000000000 : ℝ), (8951834089131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305606051/10000000000 : ℝ)|^4343 ≤ (436323302193/1000000000000 : ℝ)^3319
        have hw : |(5305606051/10000000000 : ℝ)|=(5305606051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482197319/2500000000 : ℝ)|^4343 ≤ (5804249663599/50000000000000 : ℝ)^3319
        have hw : |(-482197319/2500000000 : ℝ)|=(482197319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705002483/5000000000 : ℝ)|^4343 ≤ (8951834089131/20000000000000 : ℝ)^3319
        have hw : |(2705002483/5000000000 : ℝ)|=(2705002483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326401517/2500000000 : ℝ)*x 0 + (1082000991/2000000000 : ℝ)*x 1 + (-1928789267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326401517/2500000000 : ℝ)^4343 ≤ (21816165201119/50000000000000 : ℝ)^3319 := by
    have hnat : (1326401517 : ℕ)^4343*50000000000000^3319 ≤ 21816165201119^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326401517 2500000000 21816165201119 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082000991/2000000000 : ℝ)^4343 ≤ (44759170326569/100000000000000 : ℝ)^3319 := by
    have hnat : (1082000991 : ℕ)^4343*100000000000000^3319 ≤ 44759170326569^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082000991 2000000000 44759170326569 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928789267/10000000000 : ℝ)^4343 ≤ (11608499256319/100000000000000 : ℝ)^3319 := by
    have hnat : (1928789267 : ℕ)^4343*100000000000000^3319 ≤ 11608499256319^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928789267 10000000000 11608499256319 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326401517/2500000000 : ℝ), (1082000991/2000000000 : ℝ), (-1928789267/10000000000 : ℝ)] ![(21816165201119/50000000000000 : ℝ), (44759170326569/100000000000000 : ℝ), (11608499256319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326401517/2500000000 : ℝ)|^4343 ≤ (21816165201119/50000000000000 : ℝ)^3319
        have hw : |(1326401517/2500000000 : ℝ)|=(1326401517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082000991/2000000000 : ℝ)|^4343 ≤ (44759170326569/100000000000000 : ℝ)^3319
        have hw : |(1082000991/2000000000 : ℝ)|=(1082000991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1928789267/10000000000 : ℝ)|^4343 ≤ (11608499256319/100000000000000 : ℝ)^3319
        have hw : |(-1928789267/10000000000 : ℝ)|=(1928789267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s6_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431603603/1000000000 : ℝ)*x 0 + (28083141/62500000 : ℝ)*x 1 + (2072629589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431603603/1000000000 : ℝ)^4343 ≤ (33304205114467/100000000000000 : ℝ)^3319 := by
    have hnat : (431603603 : ℕ)^4343*100000000000000^3319 ≤ 33304205114467^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431603603 1000000000 33304205114467 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28083141/62500000 : ℝ)^4343 ≤ (35105317560627/100000000000000 : ℝ)^3319 := by
    have hnat : (28083141 : ℕ)^4343*100000000000000^3319 ≤ 35105317560627^3319*62500000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28083141 62500000 35105317560627 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072629589/5000000000 : ℝ)^4343 ≤ (31590477315427/100000000000000 : ℝ)^3319 := by
    have hnat : (2072629589 : ℕ)^4343*100000000000000^3319 ≤ 31590477315427^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072629589 5000000000 31590477315427 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431603603/1000000000 : ℝ), (28083141/62500000 : ℝ), (2072629589/5000000000 : ℝ)] ![(33304205114467/100000000000000 : ℝ), (35105317560627/100000000000000 : ℝ), (31590477315427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431603603/1000000000 : ℝ)|^4343 ≤ (33304205114467/100000000000000 : ℝ)^3319
        have hw : |(431603603/1000000000 : ℝ)|=(431603603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28083141/62500000 : ℝ)|^4343 ≤ (35105317560627/100000000000000 : ℝ)^3319
        have hw : |(28083141/62500000 : ℝ)|=(28083141/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072629589/5000000000 : ℝ)|^4343 ≤ (31590477315427/100000000000000 : ℝ)^3319
        have hw : |(2072629589/5000000000 : ℝ)|=(2072629589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5621/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (2171/512 : ℝ) ≤ (9430508504284953/100000000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^2171 ≤ (9430508504284953/100000000000000000000 : ℝ)^512 := by
      have hnat : (11237 : ℕ)^2171*100000000000000000000^512 ≤ 9430508504284953^512*100000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 9430508504284953 100000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (9430508504284953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (2171/512 : ℝ) ≤ (7446026417947823/25000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^2171 ≤ (7446026417947823/25000000000000000000 : ℝ)^512 := by
      have hnat : (7369 : ℕ)^2171*25000000000000000000^512 ≤ 7446026417947823^512*50000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 7446026417947823 25000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (7446026417947823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009430508504284953/50000000000000000000 : ℝ) ≤ (10000444778667421/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (50009430508504284953/50000000000000000000 : ℝ)^512 ≤ (10000444778667421/10000000000000000 : ℝ)^2171 := by
      have hnat : (50009430508504284953 : ℕ)^512*10000000000000000^2171 ≤ 10000444778667421^2171*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009430508504284953 50000000000000000000 10000444778667421 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000444778667421/10000000000000000 : ℝ)) (X := (50009430508504284953/50000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007842922835215249/20000000000000000000 : ℝ) ≤ (5000462341659209/5000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (20007842922835215249/20000000000000000000 : ℝ)^512 ≤ (5000462341659209/5000000000000000 : ℝ)^2171 := by
      have hnat : (20007842922835215249 : ℕ)^512*5000000000000000^2171 ≤ 5000462341659209^2171*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007842922835215249 20000000000000000000 5000462341659209 5000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000462341659209/5000000000000000 : ℝ)) (X := (20007842922835215249/20000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507446026417947823/12500000000000000000 : ℝ) ≤ (2000280917593883/2000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (12507446026417947823/12500000000000000000 : ℝ)^512 ≤ (2000280917593883/2000000000000000 : ℝ)^2171 := by
      have hnat : (12507446026417947823 : ℕ)^512*2000000000000000^2171 ≤ 2000280917593883^2171*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507446026417947823 12500000000000000000 2000280917593883 2000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000280917593883/2000000000000000 : ℝ)) (X := (12507446026417947823/12500000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9430508504284953/100000000000000000000 : ℝ) ≤ ((11666923930996044781/11670000000000000000 : ℝ)+2*(159968216999/116700000000000 : ℝ)*(11237/100000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (11666923930996044781/11670000000000000000 : ℝ)+2*(159968216999/116700000000000 : ℝ)*(11237/100000 : ℝ)=(10000444778667421/10000000000000000 : ℝ) by norm_num, show 1+2*(9430508504284953/100000000000000000000 : ℝ)=(50009430508504284953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7446026417947823/25000000000000000000 : ℝ)+(9430508504284953/100000000000000000000 : ℝ) ≤ ((11666923930996044781/11670000000000000000 : ℝ)+(159968216999/116700000000000 : ℝ)*((7369/50000 : ℝ)+(11237/100000 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (11666923930996044781/11670000000000000000 : ℝ)+(159968216999/116700000000000 : ℝ)*((7369/50000 : ℝ)+(11237/100000 : ℝ))=(5000462341659209/5000000000000000 : ℝ) by norm_num, show 1+(7446026417947823/25000000000000000000 : ℝ)+(9430508504284953/100000000000000000000 : ℝ)=(20007842922835215249/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7446026417947823/25000000000000000000 : ℝ) ≤ ((11666923930996044781/11670000000000000000 : ℝ)+2*(159968216999/116700000000000 : ℝ)*(7369/50000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (11666923930996044781/11670000000000000000 : ℝ)+2*(159968216999/116700000000000 : ℝ)*(7369/50000 : ℝ)=(2000280917593883/2000000000000000 : ℝ) by norm_num, show 1+2*(7446026417947823/25000000000000000000 : ℝ)=(12507446026417947823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11666923930996044781/11670000000000000000 : ℝ)*(X 1 0+X 2 0)+(159968216999/116700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (11666923930996044781/11670000000000000000 : ℝ)) (alpha := (159968216999/116700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11666923930996044781/11670000000000000000 : ℝ)*(X 0 1+X 2 1)+(159968216999/116700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (11666923930996044781/11670000000000000000 : ℝ)) (alpha := (159968216999/116700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11666923930996044781/11670000000000000000 : ℝ)*(X 0 2+X 1 2)+(159968216999/116700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (11666923930996044781/11670000000000000000 : ℝ)) (alpha := (159968216999/116700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-251133757/1250000000 : ℝ)*X 0 0+(1352650063/2500000000 : ℝ)*X 0 1+(5245776207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348254811/10000000000 : ℝ)*X 1 0+(-2093017981/10000000000 : ℝ)*X 1 1+(1049155231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069650947/2000000000 : ℝ)*X 2 0+(1311444051/2500000000 : ℝ)*X 2 1+(-2093018019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17264043/40000000 : ℝ)*X 0 0+(828798669/2000000000 : ℝ)*X 0 1+(89891243/200000000 : ℝ)*X 0 2+(17264043/40000000 : ℝ)*X 1 0+(828798669/2000000000 : ℝ)*X 1 1+(89891243/200000000 : ℝ)*X 1 2+(17264043/40000000 : ℝ)*X 2 0+(828798669/2000000000 : ℝ)*X 2 1+(89891243/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15695953/78125000 : ℝ)*X 0 0+(5246368313/10000000000 : ℝ)*X 0 1+(1352501241/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305606051/10000000000 : ℝ)*X 1 0+(-482197319/2500000000 : ℝ)*X 1 1+(2705002483/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326401517/2500000000 : ℝ)*X 2 0+(1082000991/2000000000 : ℝ)*X 2 1+(-1928789267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431603603/1000000000 : ℝ)*X 0 0+(28083141/62500000 : ℝ)*X 0 1+(2072629589/5000000000 : ℝ)*X 0 2+(431603603/1000000000 : ℝ)*X 1 0+(28083141/62500000 : ℝ)*X 1 1+(2072629589/5000000000 : ℝ)*X 1 2+(431603603/1000000000 : ℝ)*X 2 0+(28083141/62500000 : ℝ)*X 2 1+(2072629589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (760723873009437070367255219/97250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616987523/50000000000000 : ℝ)*(base19) + (514367681/50000000000000 : ℝ)*(base23) + (138271/195312500000 : ℝ)*(lower2) + (74303657/50000000000000 : ℝ)*(upper3) + (7137523/100000000000000 : ℝ)*(lower4) + (1114957780011639/25000000000000 : ℝ)*(major0) + (1114957780011639/25000000000000 : ℝ)*(major1) + (2229915560023279/50000000000000 : ℝ)*(major2) + (1213421085474273/20000000000000 : ℝ)*(sp0) + (6067128945636757/100000000000000 : ℝ)*(sp1) + (6067129150876441/100000000000000 : ℝ)*(sp2) + (713129553840307/25000000000000 : ℝ)*(sp3) + (12376120219/50000000000000 : ℝ)*(sp4) + (13584374961/100000000000000 : ℝ)*(sp7) + (2852531799736189/100000000000000 : ℝ)*(f.failure) + (6067130179611803/100000000000000 : ℝ)*(f.sum) + (36077895450113/5835000000000000000000000000 : ℝ)*base65 + (1464646746693243941/291750000000000000000000000000000 : ℝ)*base68 + (767795651801156899/583500000000000000000000000000000 : ℝ)*base69 + (3550453811526506059/291750000000000000000000000000000 : ℝ)*base71 + (5059103431031/2917500000000000000000000000 : ℝ)*base74 + (1706949085043156899/583500000000000000000000000000000 : ℝ)*base75 + (948422650835814647/97250000000000000000000000000000 : ℝ)*base78 + (13868999733564647/97250000000000000000000000000000 : ℝ)*base80 + (851635230493/1945000000000000000000000000 : ℝ)*base81 + (24175967/2500000000000000000000 : ℝ)*base89 + (24175967/2500000000000000000000 : ℝ)*base91 + (25824033/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (905291777297722751098846791/194500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (793122567/100000000000000 : ℝ)*(base19) + (220613351/25000000000000 : ℝ)*(base23) + (47402449/50000000000000 : ℝ)*(upper3) + (6207761/20000000000000 : ℝ)*(lower4) + (51836533/50000000000000 : ℝ)*(upper5) + (4492152582941789/100000000000000 : ℝ)*(major0) + (4492152582941789/100000000000000 : ℝ)*(major1) + (4492152582941789/100000000000000 : ℝ)*(major2) + (16468498101/100000000000000 : ℝ)*(sp1) + (17867815771/100000000000000 : ℝ)*(sp2) + (3055550115367737/50000000000000 : ℝ)*(sp4) + (3055541484557403/50000000000000 : ℝ)*(sp5) + (6111081480466299/100000000000000 : ℝ)*(sp6) + (2873204779999549/100000000000000 : ℝ)*(sp7) + (2873204779999549/100000000000000 : ℝ)*(f.failure) + (3055550115367737/50000000000000 : ℝ)*(f.sum) + (34133104206121/5835000000000000000000000000 : ℝ)*base65 + (472235379915784403/389000000000000000000000000000000 : ℝ)*base67 + (4198885388931784403/389000000000000000000000000000000 : ℝ)*base69 + (2344930127450784403/389000000000000000000000000000000 : ℝ)*base71 + (2908155526103/2917500000000000000000000000 : ℝ)*base73 + (3319039231396784403/389000000000000000000000000000000 : ℝ)*base75 + (2073107419549215597/389000000000000000000000000000000 : ℝ)*base78 + (612914922747215597/389000000000000000000000000000000 : ℝ)*base80 + (23620358670811/5835000000000000000000000000 : ℝ)*base81 + (13057953/2500000000000000000000 : ℝ)*base90 + (13057953/2500000000000000000000 : ℝ)*base92 + (13057953/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1383_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1383_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1383_s7_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009076741/10000000000 : ℝ)*x 0 + (1082111163/2000000000 : ℝ)*x 1 + (2622908049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009076741/10000000000 : ℝ)^4343 ≤ (765301185523/6250000000000 : ℝ)^3319 := by
    have hnat : (2009076741 : ℕ)^4343*6250000000000^3319 ≤ 765301185523^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009076741 10000000000 765301185523 6250000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082111163/2000000000 : ℝ)^4343 ≤ (11191283503939/25000000000000 : ℝ)^3319 := by
    have hnat : (1082111163 : ℕ)^4343*25000000000000^3319 ≤ 11191283503939^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082111163 2000000000 11191283503939 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622908049/5000000000 : ℝ)^4343 ≤ (8598009399447/20000000000000 : ℝ)^3319 := by
    have hnat : (2622908049 : ℕ)^4343*20000000000000^3319 ≤ 8598009399447^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622908049 5000000000 8598009399447 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009076741/10000000000 : ℝ), (1082111163/2000000000 : ℝ), (2622908049/5000000000 : ℝ)] ![(765301185523/6250000000000 : ℝ), (11191283503939/25000000000000 : ℝ), (8598009399447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009076741/10000000000 : ℝ)|^4343 ≤ (765301185523/6250000000000 : ℝ)^3319
        have hw : |(-2009076741/10000000000 : ℝ)|=(2009076741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082111163/2000000000 : ℝ)|^4343 ≤ (11191283503939/25000000000000 : ℝ)^3319
        have hw : |(1082111163/2000000000 : ℝ)|=(1082111163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622908049/5000000000 : ℝ)|^4343 ≤ (8598009399447/20000000000000 : ℝ)^3319
        have hw : |(2622908049/5000000000 : ℝ)|=(2622908049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213929723/400000000 : ℝ)*x 0 + (-2092981743/10000000000 : ℝ)*x 1 + (1049163051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213929723/400000000 : ℝ)^4343 ≤ (22045859262143/50000000000000 : ℝ)^3319 := by
    have hnat : (213929723 : ℕ)^4343*50000000000000^3319 ≤ 22045859262143^3319*400000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213929723 400000000 22045859262143 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092981743/10000000000 : ℝ)^4343 ≤ (2583648701629/20000000000000 : ℝ)^3319 := by
    have hnat : (2092981743 : ℕ)^4343*20000000000000^3319 ≤ 2583648701629^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092981743 10000000000 2583648701629 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049163051/2000000000 : ℝ)^4343 ≤ (42990037957307/100000000000000 : ℝ)^3319 := by
    have hnat : (1049163051 : ℕ)^4343*100000000000000^3319 ≤ 42990037957307^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049163051 2000000000 42990037957307 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213929723/400000000 : ℝ), (-2092981743/10000000000 : ℝ), (1049163051/2000000000 : ℝ)] ![(22045859262143/50000000000000 : ℝ), (2583648701629/20000000000000 : ℝ), (42990037957307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213929723/400000000 : ℝ)|^4343 ≤ (22045859262143/50000000000000 : ℝ)^3319
        have hw : |(213929723/400000000 : ℝ)|=(213929723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092981743/10000000000 : ℝ)|^4343 ≤ (2583648701629/20000000000000 : ℝ)^3319
        have hw : |(-2092981743/10000000000 : ℝ)|=(2092981743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049163051/2000000000 : ℝ)|^4343 ≤ (42990037957307/100000000000000 : ℝ)^3319
        have hw : |(1049163051/2000000000 : ℝ)|=(1049163051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348242973/10000000000 : ℝ)*x 0 + (1311453921/2500000000 : ℝ)*x 1 + (-523245327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348242973/10000000000 : ℝ)^4343 ≤ (22045858711971/50000000000000 : ℝ)^3319 := by
    have hnat : (5348242973 : ℕ)^4343*50000000000000^3319 ≤ 22045858711971^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348242973 10000000000 22045858711971 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311453921/2500000000 : ℝ)^4343 ≤ (42990042557697/100000000000000 : ℝ)^3319 := by
    have hnat : (1311453921 : ℕ)^4343*100000000000000^3319 ≤ 42990042557697^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311453921 2500000000 42990042557697 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523245327/2500000000 : ℝ)^4343 ≤ (12918239994889/100000000000000 : ℝ)^3319 := by
    have hnat : (523245327 : ℕ)^4343*100000000000000^3319 ≤ 12918239994889^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523245327 2500000000 12918239994889 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348242973/10000000000 : ℝ), (1311453921/2500000000 : ℝ), (-523245327/2500000000 : ℝ)] ![(22045858711971/50000000000000 : ℝ), (42990042557697/100000000000000 : ℝ), (12918239994889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348242973/10000000000 : ℝ)|^4343 ≤ (22045858711971/50000000000000 : ℝ)^3319
        have hw : |(5348242973/10000000000 : ℝ)|=(5348242973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311453921/2500000000 : ℝ)|^4343 ≤ (42990042557697/100000000000000 : ℝ)^3319
        have hw : |(1311453921/2500000000 : ℝ)|=(1311453921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523245327/2500000000 : ℝ)|^4343 ≤ (12918239994889/100000000000000 : ℝ)^3319
        have hw : |(-523245327/2500000000 : ℝ)|=(523245327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43160139/100000000 : ℝ)*x 0 + (1036020317/2500000000 : ℝ)*x 1 + (4494473291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43160139/100000000 : ℝ)^4343 ≤ (520374713529/1562500000000 : ℝ)^3319 := by
    have hnat : (43160139 : ℕ)^4343*1562500000000^3319 ≤ 520374713529^3319*100000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43160139 100000000 520374713529 1562500000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036020317/2500000000 : ℝ)^4343 ≤ (7894682895467/25000000000000 : ℝ)^3319 := by
    have hnat : (1036020317 : ℕ)^4343*25000000000000^3319 ≤ 7894682895467^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036020317 2500000000 7894682895467 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494473291/10000000000 : ℝ)^4343 ≤ (8779321685117/25000000000000 : ℝ)^3319 := by
    have hnat : (4494473291 : ℕ)^4343*25000000000000^3319 ≤ 8779321685117^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494473291 10000000000 8779321685117 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43160139/100000000 : ℝ), (1036020317/2500000000 : ℝ), (4494473291/10000000000 : ℝ)] ![(520374713529/1562500000000 : ℝ), (7894682895467/25000000000000 : ℝ), (8779321685117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43160139/100000000 : ℝ)|^4343 ≤ (520374713529/1562500000000 : ℝ)^3319
        have hw : |(43160139/100000000 : ℝ)|=(43160139/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036020317/2500000000 : ℝ)|^4343 ≤ (7894682895467/25000000000000 : ℝ)^3319
        have hw : |(1036020317/2500000000 : ℝ)|=(1036020317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494473291/10000000000 : ℝ)|^4343 ≤ (8779321685117/25000000000000 : ℝ)^3319
        have hw : |(4494473291/10000000000 : ℝ)|=(4494473291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-502272139/2500000000 : ℝ)*x 0 + (5246407111/10000000000 : ℝ)*x 1 + (540996169/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502272139/2500000000 : ℝ)^4343 ≤ (2448982638951/20000000000000 : ℝ)^3319 := by
    have hnat : (502272139 : ℕ)^4343*20000000000000^3319 ≤ 2448982638951^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502272139 2500000000 2448982638951 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246407111/10000000000 : ℝ)^4343 ≤ (21498192424059/50000000000000 : ℝ)^3319 := by
    have hnat : (5246407111 : ℕ)^4343*50000000000000^3319 ≤ 21498192424059^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246407111 10000000000 21498192424059 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540996169/1000000000 : ℝ)^4343 ≤ (44758701941423/100000000000000 : ℝ)^3319 := by
    have hnat : (540996169 : ℕ)^4343*100000000000000^3319 ≤ 44758701941423^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540996169 1000000000 44758701941423 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502272139/2500000000 : ℝ), (5246407111/10000000000 : ℝ), (540996169/1000000000 : ℝ)] ![(2448982638951/20000000000000 : ℝ), (21498192424059/50000000000000 : ℝ), (44758701941423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502272139/2500000000 : ℝ)|^4343 ≤ (2448982638951/20000000000000 : ℝ)^3319
        have hw : |(-502272139/2500000000 : ℝ)|=(502272139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246407111/10000000000 : ℝ)|^4343 ≤ (21498192424059/50000000000000 : ℝ)^3319
        have hw : |(5246407111/10000000000 : ℝ)|=(5246407111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540996169/1000000000 : ℝ)|^4343 ≤ (44758701941423/100000000000000 : ℝ)^3319
        have hw : |(540996169/1000000000 : ℝ)|=(540996169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061123171/2000000000 : ℝ)*x 0 + (-1928835309/10000000000 : ℝ)*x 1 + (5409961733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061123171/2000000000 : ℝ)^4343 ≤ (10908108930247/25000000000000 : ℝ)^3319 := by
    have hnat : (1061123171 : ℕ)^4343*25000000000000^3319 ≤ 10908108930247^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061123171 2000000000 10908108930247 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928835309/10000000000 : ℝ)^4343 ≤ (11608861857867/100000000000000 : ℝ)^3319 := by
    have hnat : (1928835309 : ℕ)^4343*100000000000000^3319 ≤ 11608861857867^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928835309 10000000000 11608861857867 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409961733/10000000000 : ℝ)^4343 ≤ (44758702406939/100000000000000 : ℝ)^3319 := by
    have hnat : (5409961733 : ℕ)^4343*100000000000000^3319 ≤ 44758702406939^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409961733 10000000000 44758702406939 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061123171/2000000000 : ℝ), (-1928835309/10000000000 : ℝ), (5409961733/10000000000 : ℝ)] ![(10908108930247/25000000000000 : ℝ), (11608861857867/100000000000000 : ℝ), (44758702406939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061123171/2000000000 : ℝ)|^4343 ≤ (10908108930247/25000000000000 : ℝ)^3319
        have hw : |(1061123171/2000000000 : ℝ)|=(1061123171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1928835309/10000000000 : ℝ)|^4343 ≤ (11608861857867/100000000000000 : ℝ)^3319
        have hw : |(-1928835309/10000000000 : ℝ)|=(1928835309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409961733/10000000000 : ℝ)|^4343 ≤ (44758702406939/100000000000000 : ℝ)^3319
        have hw : |(5409961733/10000000000 : ℝ)|=(5409961733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652807957/5000000000 : ℝ)*x 0 + (540996169/1000000000 : ℝ)*x 1 + (-1928835287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652807957/5000000000 : ℝ)^4343 ≤ (10908109088973/25000000000000 : ℝ)^3319 := by
    have hnat : (2652807957 : ℕ)^4343*25000000000000^3319 ≤ 10908109088973^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652807957 5000000000 10908109088973 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540996169/1000000000 : ℝ)^4343 ≤ (44758701941423/100000000000000 : ℝ)^3319 := by
    have hnat : (540996169 : ℕ)^4343*100000000000000^3319 ≤ 44758701941423^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540996169 1000000000 44758701941423 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928835287/10000000000 : ℝ)^4343 ≤ (11608861684607/100000000000000 : ℝ)^3319 := by
    have hnat : (1928835287 : ℕ)^4343*100000000000000^3319 ≤ 11608861684607^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928835287 10000000000 11608861684607 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652807957/5000000000 : ℝ), (540996169/1000000000 : ℝ), (-1928835287/10000000000 : ℝ)] ![(10908109088973/25000000000000 : ℝ), (44758701941423/100000000000000 : ℝ), (11608861684607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652807957/5000000000 : ℝ)|^4343 ≤ (10908109088973/25000000000000 : ℝ)^3319
        have hw : |(2652807957/5000000000 : ℝ)|=(2652807957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540996169/1000000000 : ℝ)|^4343 ≤ (44758701941423/100000000000000 : ℝ)^3319
        have hw : |(540996169/1000000000 : ℝ)|=(540996169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1928835287/10000000000 : ℝ)|^4343 ≤ (11608861684607/100000000000000 : ℝ)^3319
        have hw : |(-1928835287/10000000000 : ℝ)|=(1928835287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s7_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316038931/10000000000 : ℝ)*x 0 + (898642983/2000000000 : ℝ)*x 1 + (1036336523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316038931/10000000000 : ℝ)^4343 ≤ (4163029300769/12500000000000 : ℝ)^3319 := by
    have hnat : (4316038931 : ℕ)^4343*12500000000000^3319 ≤ 4163029300769^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316038931 10000000000 4163029300769 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898642983/2000000000 : ℝ)^4343 ≤ (35104421544847/100000000000000 : ℝ)^3319 := by
    have hnat : (898642983 : ℕ)^4343*100000000000000^3319 ≤ 35104421544847^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898642983 2000000000 35104421544847 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036336523/2500000000 : ℝ)^4343 ≤ (7897836008557/25000000000000 : ℝ)^3319 := by
    have hnat : (1036336523 : ℕ)^4343*25000000000000^3319 ≤ 7897836008557^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036336523 2500000000 7897836008557 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316038931/10000000000 : ℝ), (898642983/2000000000 : ℝ), (1036336523/2500000000 : ℝ)] ![(4163029300769/12500000000000 : ℝ), (35104421544847/100000000000000 : ℝ), (7897836008557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316038931/10000000000 : ℝ)|^4343 ≤ (4163029300769/12500000000000 : ℝ)^3319
        have hw : |(4316038931/10000000000 : ℝ)|=(4316038931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898642983/2000000000 : ℝ)|^4343 ≤ (35104421544847/100000000000000 : ℝ)^3319
        have hw : |(898642983/2000000000 : ℝ)|=(898642983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036336523/2500000000 : ℝ)|^4343 ≤ (7897836008557/25000000000000 : ℝ)^3319
        have hw : |(1036336523/2500000000 : ℝ)|=(1036336523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5621/50000 : ℝ) ^ (2171/512 : ℝ) ≤ (2362078536851929/25000000000000000000 : ℝ) := by
    have hpowers : (5621/50000 : ℝ)^2171 ≤ (2362078536851929/25000000000000000000 : ℝ)^512 := by
      have hnat : (5621 : ℕ)^2171*25000000000000000000^512 ≤ 2362078536851929^512*50000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5621 50000 2362078536851929 25000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5621/50000 : ℝ)) (X := (2362078536851929/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (2171/512 : ℝ) ≤ (5946544978878781/20000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^2171 ≤ (5946544978878781/20000000000000000000 : ℝ)^512 := by
      have hnat : (3683 : ℕ)^2171*20000000000000000000^512 ≤ 5946544978878781^512*25000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 5946544978878781 20000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (5946544978878781/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502362078536851929/12500000000000000000 : ℝ) ≤ (10000445618388683/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (12502362078536851929/12500000000000000000 : ℝ)^512 ≤ (10000445618388683/10000000000000000 : ℝ)^2171 := by
      have hnat : (12502362078536851929 : ℕ)^512*10000000000000000^2171 ≤ 10000445618388683^2171*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502362078536851929 12500000000000000000 10000445618388683 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445618388683/10000000000000000 : ℝ)) (X := (12502362078536851929/12500000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039181039041801621/100000000000000000000 : ℝ) ≤ (1000092389173291/1000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (100039181039041801621/100000000000000000000 : ℝ)^512 ≤ (1000092389173291/1000000000000000 : ℝ)^2171 := by
      have hnat : (100039181039041801621 : ℕ)^512*1000000000000000^2171 ≤ 1000092389173291^2171*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039181039041801621 100000000000000000000 1000092389173291 1000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000092389173291/1000000000000000 : ℝ)) (X := (100039181039041801621/100000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005946544978878781/10000000000000000000 : ℝ) ≤ (10001402165077137/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (10005946544978878781/10000000000000000000 : ℝ)^512 ≤ (10001402165077137/10000000000000000 : ℝ)^2171 := by
      have hnat : (10005946544978878781 : ℕ)^512*10000000000000000^2171 ≤ 10001402165077137^2171*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005946544978878781 10000000000000000000 10001402165077137 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001402165077137/10000000000000000 : ℝ)) (X := (10005946544978878781/10000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2362078536851929/25000000000000000000 : ℝ) ≤ ((17445400855152451901/17450000000000000000 : ℝ)+2*(478273344227/349000000000000 : ℝ)*(5621/50000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (17445400855152451901/17450000000000000000 : ℝ)+2*(478273344227/349000000000000 : ℝ)*(5621/50000 : ℝ)=(10000445618388683/10000000000000000 : ℝ) by norm_num, show 1+2*(2362078536851929/25000000000000000000 : ℝ)=(12502362078536851929/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5946544978878781/20000000000000000000 : ℝ)+(2362078536851929/25000000000000000000 : ℝ) ≤ ((17445400855152451901/17450000000000000000 : ℝ)+(478273344227/349000000000000 : ℝ)*((3683/25000 : ℝ)+(5621/50000 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (17445400855152451901/17450000000000000000 : ℝ)+(478273344227/349000000000000 : ℝ)*((3683/25000 : ℝ)+(5621/50000 : ℝ))=(1000092389173291/1000000000000000 : ℝ) by norm_num, show 1+(5946544978878781/20000000000000000000 : ℝ)+(2362078536851929/25000000000000000000 : ℝ)=(100039181039041801621/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5946544978878781/20000000000000000000 : ℝ) ≤ ((17445400855152451901/17450000000000000000 : ℝ)+2*(478273344227/349000000000000 : ℝ)*(3683/25000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (17445400855152451901/17450000000000000000 : ℝ)+2*(478273344227/349000000000000 : ℝ)*(3683/25000 : ℝ)=(10001402165077137/10000000000000000 : ℝ) by norm_num, show 1+2*(5946544978878781/20000000000000000000 : ℝ)=(10005946544978878781/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17445400855152451901/17450000000000000000 : ℝ)*(X 1 0+X 2 0)+(478273344227/349000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17445400855152451901/17450000000000000000 : ℝ)) (alpha := (478273344227/349000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17445400855152451901/17450000000000000000 : ℝ)*(X 0 1+X 2 1)+(478273344227/349000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17445400855152451901/17450000000000000000 : ℝ)) (alpha := (478273344227/349000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17445400855152451901/17450000000000000000 : ℝ)*(X 0 2+X 1 2)+(478273344227/349000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17445400855152451901/17450000000000000000 : ℝ)) (alpha := (478273344227/349000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2009076741/10000000000 : ℝ)*X 0 0+(1082111163/2000000000 : ℝ)*X 0 1+(2622908049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213929723/400000000 : ℝ)*X 1 0+(-2092981743/10000000000 : ℝ)*X 1 1+(1049163051/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348242973/10000000000 : ℝ)*X 2 0+(1311453921/2500000000 : ℝ)*X 2 1+(-523245327/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43160139/100000000 : ℝ)*X 0 0+(1036020317/2500000000 : ℝ)*X 0 1+(4494473291/10000000000 : ℝ)*X 0 2+(43160139/100000000 : ℝ)*X 1 0+(1036020317/2500000000 : ℝ)*X 1 1+(4494473291/10000000000 : ℝ)*X 1 2+(43160139/100000000 : ℝ)*X 2 0+(1036020317/2500000000 : ℝ)*X 2 1+(4494473291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502272139/2500000000 : ℝ)*X 0 0+(5246407111/10000000000 : ℝ)*X 0 1+(540996169/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061123171/2000000000 : ℝ)*X 1 0+(-1928835309/10000000000 : ℝ)*X 1 1+(5409961733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652807957/5000000000 : ℝ)*X 2 0+(540996169/1000000000 : ℝ)*X 2 1+(-1928835287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316038931/10000000000 : ℝ)*X 0 0+(898642983/2000000000 : ℝ)*X 0 1+(1036336523/2500000000 : ℝ)*X 0 2+(4316038931/10000000000 : ℝ)*X 1 0+(898642983/2000000000 : ℝ)*X 1 1+(1036336523/2500000000 : ℝ)*X 1 2+(4316038931/10000000000 : ℝ)*X 2 0+(898642983/2000000000 : ℝ)*X 2 1+(1036336523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2519877101025556646691695337/436250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1072020073/100000000000000 : ℝ)*(base19) + (900986353/100000000000000 : ℝ)*(base23) + (12487233/20000000000000 : ℝ)*(lower2) + (94499597/50000000000000 : ℝ)*(upper5) + (4462079139255547/100000000000000 : ℝ)*(major0) + (4462079139255547/100000000000000 : ℝ)*(major1) + (1115519784813887/25000000000000 : ℝ)*(major2) + (3035090426678199/50000000000000 : ℝ)*(sp0) + (303508982797827/5000000000000 : ℝ)*(sp1) + (6070187540157367/100000000000000 : ℝ)*(sp2) + (1426979578018079/50000000000000 : ℝ)*(sp3) + (3793893661/50000000000000 : ℝ)*(sp4) + (7713167107/100000000000000 : ℝ)*(sp5) + (10488790451/100000000000000 : ℝ)*(sp7) + (285396964482661/10000000000000 : ℝ)*(f.failure) + (6070188441143721/100000000000000 : ℝ)*(f.sum) + (135436469383/20000000000000000000000000 : ℝ)*base66 + (19539960431789744847/1745000000000000000000000000000000 : ℝ)*base67 + (3407460979911461687/436250000000000000000000000000000 : ℝ)*base69 + (5806426627764744847/1745000000000000000000000000000000 : ℝ)*base71 + (81151198717/20000000000000000000000000 : ℝ)*base73 + (5847867496782711687/436250000000000000000000000000000 : ℝ)*base75 + (4644266725583394847/1745000000000000000000000000000000 : ℝ)*base77 + (17293016376158394847/1745000000000000000000000000000000 : ℝ)*base79 + (4307303546131/17450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3390583/250000000000000000000 : ℝ)*base89 + (3390583/250000000000000000000 : ℝ)*base91 + (890583/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64303132720491874232117133/17450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (658154963/100000000000000 : ℝ)*(base19) + (194523601/25000000000000 : ℝ)*(base23) + (249848453/100000000000000 : ℝ)*(lower1) + (78538069/100000000000000 : ℝ)*(upper3) + (10112879/50000000000000 : ℝ)*(lower4) + (43124729/50000000000000 : ℝ)*(upper5) + (179775837339811/4000000000000 : ℝ)*(major0) + (179775837339811/4000000000000 : ℝ)*(major1) + (179775837339811/4000000000000 : ℝ)*(major2) + (34419441/2000000000000 : ℝ)*(sp2) + (764269013145553/12500000000000 : ℝ)*(sp4) + (6114151447009461/100000000000000 : ℝ)*(sp5) + (611414960609797/10000000000000 : ℝ)*(sp6) + (2874639638992979/100000000000000 : ℝ)*(sp7) + (2874639638992979/100000000000000 : ℝ)*(f.failure) + (764269013145553/12500000000000 : ℝ)*(f.sum) + (916806395007/698000000000000000000000000 : ℝ)*base65 + (1216599607235419289/69800000000000000000000000000000 : ℝ)*base68 + (340742491009619289/69800000000000000000000000000000 : ℝ)*base70 + (8406611666334419289/69800000000000000000000000000000 : ℝ)*base72 + (4490103767431/698000000000000000000000000 : ℝ)*base74 + (14574956362150980711/69800000000000000000000000000000 : ℝ)*base75 + (421519242569419289/69800000000000000000000000000000 : ℝ)*base78 + (225759461268219289/69800000000000000000000000000000 : ℝ)*base80 + (1674383785053/698000000000000000000000000 : ℝ)*base81 + (14960337/2500000000000000000000 : ℝ)*base89 + (14960337/2500000000000000000000 : ℝ)*base91 + (14960337/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1383_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1383_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1383_box_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-369002211/2000000000 : ℝ)*x 0 + (5388214279/10000000000 : ℝ)*x 1 + (2694107139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (369002211/2000000000 : ℝ)^4343 ≤ (342286764013/3125000000000 : ℝ)^3319 := by
    have hnat : (369002211 : ℕ)^4343*3125000000000^3319 ≤ 342286764013^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369002211 2000000000 342286764013 3125000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388214279/10000000000 : ℝ)^4343 ≤ (44523411771251/100000000000000 : ℝ)^3319 := by
    have hnat : (5388214279 : ℕ)^4343*100000000000000^3319 ≤ 44523411771251^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388214279 10000000000 44523411771251 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694107139/5000000000 : ℝ)^4343 ≤ (22261705880219/50000000000000 : ℝ)^3319 := by
    have hnat : (2694107139 : ℕ)^4343*50000000000000^3319 ≤ 22261705880219^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694107139 5000000000 22261705880219 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-369002211/2000000000 : ℝ), (5388214279/10000000000 : ℝ), (2694107139/5000000000 : ℝ)] ![(342286764013/3125000000000 : ℝ), (44523411771251/100000000000000 : ℝ), (22261705880219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-369002211/2000000000 : ℝ)|^4343 ≤ (342286764013/3125000000000 : ℝ)^3319
        have hw : |(-369002211/2000000000 : ℝ)|=(369002211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388214279/10000000000 : ℝ)|^4343 ≤ (44523411771251/100000000000000 : ℝ)^3319
        have hw : |(5388214279/10000000000 : ℝ)|=(5388214279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694107139/5000000000 : ℝ)|^4343 ≤ (22261705880219/50000000000000 : ℝ)^3319
        have hw : |(2694107139/5000000000 : ℝ)|=(2694107139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285661237/10000000000 : ℝ)*x 0 + (-992852407/5000000000 : ℝ)*x 1 + (5388214399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285661237/10000000000 : ℝ)^4343 ≤ (8683565398143/20000000000000 : ℝ)^3319 := by
    have hnat : (5285661237 : ℕ)^4343*20000000000000^3319 ≤ 8683565398143^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285661237 10000000000 8683565398143 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992852407/5000000000 : ℝ)^4343 ≤ (12058759933193/100000000000000 : ℝ)^3319 := by
    have hnat : (992852407 : ℕ)^4343*100000000000000^3319 ≤ 12058759933193^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992852407 5000000000 12058759933193 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388214399/10000000000 : ℝ)^4343 ≤ (44523413068751/100000000000000 : ℝ)^3319 := by
    have hnat : (5388214399 : ℕ)^4343*100000000000000^3319 ≤ 44523413068751^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388214399 10000000000 44523413068751 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285661237/10000000000 : ℝ), (-992852407/5000000000 : ℝ), (5388214399/10000000000 : ℝ)] ![(8683565398143/20000000000000 : ℝ), (12058759933193/100000000000000 : ℝ), (44523413068751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285661237/10000000000 : ℝ)|^4343 ≤ (8683565398143/20000000000000 : ℝ)^3319
        have hw : |(5285661237/10000000000 : ℝ)|=(5285661237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992852407/5000000000 : ℝ)|^4343 ≤ (12058759933193/100000000000000 : ℝ)^3319
        have hw : |(-992852407/5000000000 : ℝ)|=(992852407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388214399/10000000000 : ℝ)|^4343 ≤ (44523413068751/100000000000000 : ℝ)^3319
        have hw : |(5388214399/10000000000 : ℝ)|=(5388214399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285660741/10000000000 : ℝ)*x 0 + (5388214783/10000000000 : ℝ)*x 1 + (-992852481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285660741/10000000000 : ℝ)^4343 ≤ (43417821659417/100000000000000 : ℝ)^3319 := by
    have hnat : (5285660741 : ℕ)^4343*100000000000000^3319 ≤ 43417821659417^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285660741 10000000000 43417821659417 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388214783/10000000000 : ℝ)^4343 ≤ (44523417220751/100000000000000 : ℝ)^3319 := by
    have hnat : (5388214783 : ℕ)^4343*100000000000000^3319 ≤ 44523417220751^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388214783 10000000000 44523417220751 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992852481/5000000000 : ℝ)^4343 ≤ (12058761109261/100000000000000 : ℝ)^3319 := by
    have hnat : (992852481 : ℕ)^4343*100000000000000^3319 ≤ 12058761109261^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992852481 5000000000 12058761109261 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285660741/10000000000 : ℝ), (5388214783/10000000000 : ℝ), (-992852481/5000000000 : ℝ)] ![(43417821659417/100000000000000 : ℝ), (44523417220751/100000000000000 : ℝ), (12058761109261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285660741/10000000000 : ℝ)|^4343 ≤ (43417821659417/100000000000000 : ℝ)^3319
        have hw : |(5285660741/10000000000 : ℝ)|=(5285660741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388214783/10000000000 : ℝ)|^4343 ≤ (44523417220751/100000000000000 : ℝ)^3319
        have hw : |(5388214783/10000000000 : ℝ)|=(5388214783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992852481/5000000000 : ℝ)|^4343 ≤ (12058761109261/100000000000000 : ℝ)^3319
        have hw : |(-992852481/5000000000 : ℝ)|=(992852481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44632709/100000000 : ℝ)*x 0 + (212309297/500000000 : ℝ)*x 1 + (4246186793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44632709/100000000 : ℝ)^4343 ≤ (34798612841063/100000000000000 : ℝ)^3319 := by
    have hnat : (44632709 : ℕ)^4343*100000000000000^3319 ≤ 34798612841063^3319*100000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44632709 100000000 34798612841063 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212309297/500000000 : ℝ)^4343 ≤ (32600689289379/100000000000000 : ℝ)^3319 := by
    have hnat : (212309297 : ℕ)^4343*100000000000000^3319 ≤ 32600689289379^3319*500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212309297 500000000 32600689289379 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246186793/10000000000 : ℝ)^4343 ≤ (32600697858957/100000000000000 : ℝ)^3319 := by
    have hnat : (4246186793 : ℕ)^4343*100000000000000^3319 ≤ 32600697858957^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246186793 10000000000 32600697858957 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44632709/100000000 : ℝ), (212309297/500000000 : ℝ), (4246186793/10000000000 : ℝ)] ![(34798612841063/100000000000000 : ℝ), (32600689289379/100000000000000 : ℝ), (32600697858957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44632709/100000000 : ℝ)|^4343 ≤ (34798612841063/100000000000000 : ℝ)^3319
        have hw : |(44632709/100000000 : ℝ)|=(44632709/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212309297/500000000 : ℝ)|^4343 ≤ (32600689289379/100000000000000 : ℝ)^3319
        have hw : |(212309297/500000000 : ℝ)|=(212309297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246186793/10000000000 : ℝ)|^4343 ≤ (32600697858957/100000000000000 : ℝ)^3319
        have hw : |(4246186793/10000000000 : ℝ)|=(4246186793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087943217/5000000000 : ℝ)*x 0 + (5265761727/10000000000 : ℝ)*x 1 + (263288117/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087943217/5000000000 : ℝ)^4343 ≤ (13591873943141/100000000000000 : ℝ)^3319 := by
    have hnat : (1087943217 : ℕ)^4343*100000000000000^3319 ≤ 13591873943141^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087943217 5000000000 13591873943141 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265761727/10000000000 : ℝ)^4343 ≤ (43204059726493/100000000000000 : ℝ)^3319 := by
    have hnat : (5265761727 : ℕ)^4343*100000000000000^3319 ≤ 43204059726493^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265761727 10000000000 43204059726493 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263288117/500000000 : ℝ)^4343 ≤ (43204066307713/100000000000000 : ℝ)^3319 := by
    have hnat : (263288117 : ℕ)^4343*100000000000000^3319 ≤ 43204066307713^3319*500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263288117 500000000 43204066307713 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087943217/5000000000 : ℝ), (5265761727/10000000000 : ℝ), (263288117/500000000 : ℝ)] ![(13591873943141/100000000000000 : ℝ), (43204059726493/100000000000000 : ℝ), (43204066307713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087943217/5000000000 : ℝ)|^4343 ≤ (13591873943141/100000000000000 : ℝ)^3319
        have hw : |(-1087943217/5000000000 : ℝ)|=(1087943217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265761727/10000000000 : ℝ)|^4343 ≤ (43204059726493/100000000000000 : ℝ)^3319
        have hw : |(5265761727/10000000000 : ℝ)|=(5265761727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263288117/500000000 : ℝ)|^4343 ≤ (43204066307713/100000000000000 : ℝ)^3319
        have hw : |(263288117/500000000 : ℝ)|=(263288117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371521657/10000000000 : ℝ)*x 0 + (-2035119993/10000000000 : ℝ)*x 1 + (5265761677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371521657/10000000000 : ℝ)^4343 ≤ (2771438068751/6250000000000 : ℝ)^3319 := by
    have hnat : (5371521657 : ℕ)^4343*6250000000000^3319 ≤ 2771438068751^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371521657 10000000000 2771438068751 6250000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035119993/10000000000 : ℝ)^4343 ≤ (498117267857/4000000000000 : ℝ)^3319 := by
    have hnat : (2035119993 : ℕ)^4343*4000000000000^3319 ≤ 498117267857^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035119993 10000000000 498117267857 4000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265761677/10000000000 : ℝ)^4343 ≤ (43204059189689/100000000000000 : ℝ)^3319 := by
    have hnat : (5265761677 : ℕ)^4343*100000000000000^3319 ≤ 43204059189689^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265761677 10000000000 43204059189689 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371521657/10000000000 : ℝ), (-2035119993/10000000000 : ℝ), (5265761677/10000000000 : ℝ)] ![(2771438068751/6250000000000 : ℝ), (498117267857/4000000000000 : ℝ), (43204059189689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371521657/10000000000 : ℝ)|^4343 ≤ (2771438068751/6250000000000 : ℝ)^3319
        have hw : |(5371521657/10000000000 : ℝ)|=(5371521657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2035119993/10000000000 : ℝ)|^4343 ≤ (498117267857/4000000000000 : ℝ)^3319
        have hw : |(-2035119993/10000000000 : ℝ)|=(2035119993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265761677/10000000000 : ℝ)|^4343 ≤ (43204059189689/100000000000000 : ℝ)^3319
        have hw : |(5265761677/10000000000 : ℝ)|=(5265761677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371522137/10000000000 : ℝ)*x 0 + (2632880923/5000000000 : ℝ)*x 1 + (-2035119119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371522137/10000000000 : ℝ)^4343 ≤ (886860285701/2000000000000 : ℝ)^3319 := by
    have hnat : (5371522137 : ℕ)^4343*2000000000000^3319 ≤ 886860285701^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371522137 10000000000 886860285701 2000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632880923/5000000000 : ℝ)^4343 ≤ (43204061004087/100000000000000 : ℝ)^3319 := by
    have hnat : (2632880923 : ℕ)^4343*100000000000000^3319 ≤ 43204061004087^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632880923 5000000000 43204061004087 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035119119/10000000000 : ℝ)^4343 ≤ (6226462349199/50000000000000 : ℝ)^3319 := by
    have hnat : (2035119119 : ℕ)^4343*50000000000000^3319 ≤ 6226462349199^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035119119 10000000000 6226462349199 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371522137/10000000000 : ℝ), (2632880923/5000000000 : ℝ), (-2035119119/10000000000 : ℝ)] ![(886860285701/2000000000000 : ℝ), (43204061004087/100000000000000 : ℝ), (6226462349199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371522137/10000000000 : ℝ)|^4343 ≤ (886860285701/2000000000000 : ℝ)^3319
        have hw : |(5371522137/10000000000 : ℝ)|=(5371522137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632880923/5000000000 : ℝ)|^4343 ≤ (43204061004087/100000000000000 : ℝ)^3319
        have hw : |(2632880923/5000000000 : ℝ)|=(2632880923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035119119/10000000000 : ℝ)|^4343 ≤ (6226462349199/50000000000000 : ℝ)^3319
        have hw : |(-2035119119/10000000000 : ℝ)|=(2035119119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4167773009/10000000000 : ℝ)*x 0 + (34327211/78125000 : ℝ)*x 1 + (43938831/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167773009/10000000000 : ℝ)^4343 ≤ (31815175590937/100000000000000 : ℝ)^3319 := by
    have hnat : (4167773009 : ℕ)^4343*100000000000000^3319 ≤ 31815175590937^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167773009 10000000000 31815175590937 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34327211/78125000 : ℝ)^4343 ≤ (1065387866629/3125000000000 : ℝ)^3319 := by
    have hnat : (34327211 : ℕ)^4343*3125000000000^3319 ≤ 1065387866629^3319*78125000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34327211 78125000 1065387866629 3125000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43938831/100000000 : ℝ)^4343 ≤ (34092412666199/100000000000000 : ℝ)^3319 := by
    have hnat : (43938831 : ℕ)^4343*100000000000000^3319 ≤ 34092412666199^3319*100000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43938831 100000000 34092412666199 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167773009/10000000000 : ℝ), (34327211/78125000 : ℝ), (43938831/100000000 : ℝ)] ![(31815175590937/100000000000000 : ℝ), (1065387866629/3125000000000 : ℝ), (34092412666199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167773009/10000000000 : ℝ)|^4343 ≤ (31815175590937/100000000000000 : ℝ)^3319
        have hw : |(4167773009/10000000000 : ℝ)|=(4167773009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34327211/78125000 : ℝ)|^4343 ≤ (1065387866629/3125000000000 : ℝ)^3319
        have hw : |(34327211/78125000 : ℝ)|=(34327211/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43938831/100000000 : ℝ)|^4343 ≤ (34092412666199/100000000000000 : ℝ)^3319
        have hw : |(43938831/100000000 : ℝ)|=(43938831/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_8 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106300239/10000000000 : ℝ)*x 0 + (5181272789/10000000000 : ℝ)*x 1 + (5402214703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106300239/10000000000 : ℝ)^4343 ≤ (13025915135531/100000000000000 : ℝ)^3319 := by
    have hnat : (2106300239 : ℕ)^4343*100000000000000^3319 ≤ 13025915135531^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106300239 10000000000 13025915135531 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181272789/10000000000 : ℝ)^4343 ≤ (21149616423403/50000000000000 : ℝ)^3319 := by
    have hnat : (5181272789 : ℕ)^4343*50000000000000^3319 ≤ 21149616423403^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181272789 10000000000 21149616423403 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402214703/10000000000 : ℝ)^4343 ≤ (8934970401751/20000000000000 : ℝ)^3319 := by
    have hnat : (5402214703 : ℕ)^4343*20000000000000^3319 ≤ 8934970401751^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402214703 10000000000 8934970401751 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106300239/10000000000 : ℝ), (5181272789/10000000000 : ℝ), (5402214703/10000000000 : ℝ)] ![(13025915135531/100000000000000 : ℝ), (21149616423403/50000000000000 : ℝ), (8934970401751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106300239/10000000000 : ℝ)|^4343 ≤ (13025915135531/100000000000000 : ℝ)^3319
        have hw : |(-2106300239/10000000000 : ℝ)|=(2106300239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181272789/10000000000 : ℝ)|^4343 ≤ (21149616423403/50000000000000 : ℝ)^3319
        have hw : |(5181272789/10000000000 : ℝ)|=(5181272789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402214703/10000000000 : ℝ)|^4343 ≤ (8934970401751/20000000000000 : ℝ)^3319
        have hw : |(5402214703/10000000000 : ℝ)|=(5402214703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_9 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329740021/625000000 : ℝ)*x 0 + (-1979925939/10000000000 : ℝ)*x 1 + (168819187/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329740021/625000000 : ℝ)^4343 ≤ (43312296461159/100000000000000 : ℝ)^3319 := by
    have hnat : (329740021 : ℕ)^4343*100000000000000^3319 ≤ 43312296461159^3319*625000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329740021 625000000 43312296461159 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1979925939/10000000000 : ℝ)^4343 ≤ (6006429649303/50000000000000 : ℝ)^3319 := by
    have hnat : (1979925939 : ℕ)^4343*50000000000000^3319 ≤ 6006429649303^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979925939 10000000000 6006429649303 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168819187/312500000 : ℝ)^4343 ≤ (2233742211417/5000000000000 : ℝ)^3319 := by
    have hnat : (168819187 : ℕ)^4343*5000000000000^3319 ≤ 2233742211417^3319*312500000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168819187 312500000 2233742211417 5000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329740021/625000000 : ℝ), (-1979925939/10000000000 : ℝ), (168819187/312500000 : ℝ)] ![(43312296461159/100000000000000 : ℝ), (6006429649303/50000000000000 : ℝ), (2233742211417/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329740021/625000000 : ℝ)|^4343 ≤ (43312296461159/100000000000000 : ℝ)^3319
        have hw : |(329740021/625000000 : ℝ)|=(329740021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1979925939/10000000000 : ℝ)|^4343 ≤ (6006429649303/50000000000000 : ℝ)^3319
        have hw : |(-1979925939/10000000000 : ℝ)|=(1979925939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168819187/312500000 : ℝ)|^4343 ≤ (2233742211417/5000000000000 : ℝ)^3319
        have hw : |(168819187/312500000 : ℝ)|=(168819187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_10 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275839809/10000000000 : ℝ)*x 0 + (675276813/1250000000 : ℝ)*x 1 + (-1979925943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275839809/10000000000 : ℝ)^4343 ≤ (1353509087497/3125000000000 : ℝ)^3319 := by
    have hnat : (5275839809 : ℕ)^4343*3125000000000^3319 ≤ 1353509087497^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275839809 10000000000 1353509087497 3125000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675276813/1250000000 : ℝ)^4343 ≤ (2792178115959/6250000000000 : ℝ)^3319 := by
    have hnat : (675276813 : ℕ)^4343*6250000000000^3319 ≤ 2792178115959^3319*1250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675276813 1250000000 2792178115959 6250000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979925943/10000000000 : ℝ)^4343 ≤ (12012859330363/100000000000000 : ℝ)^3319 := by
    have hnat : (1979925943 : ℕ)^4343*100000000000000^3319 ≤ 12012859330363^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979925943 10000000000 12012859330363 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275839809/10000000000 : ℝ), (675276813/1250000000 : ℝ), (-1979925943/10000000000 : ℝ)] ![(1353509087497/3125000000000 : ℝ), (2792178115959/6250000000000 : ℝ), (12012859330363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275839809/10000000000 : ℝ)|^4343 ≤ (1353509087497/3125000000000 : ℝ)^3319
        have hw : |(5275839809/10000000000 : ℝ)|=(5275839809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675276813/1250000000 : ℝ)|^4343 ≤ (2792178115959/6250000000000 : ℝ)^3319
        have hw : |(675276813/1250000000 : ℝ)|=(675276813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1979925943/10000000000 : ℝ)|^4343 ≤ (12012859330363/100000000000000 : ℝ)^3319
        have hw : |(-1979925943/10000000000 : ℝ)|=(1979925943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_11 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4496497031/10000000000 : ℝ)*x 0 + (2114643041/5000000000 : ℝ)*x 1 + (845857197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496497031/10000000000 : ℝ)^4343 ≤ (35137979080417/100000000000000 : ℝ)^3319 := by
    have hnat : (4496497031 : ℕ)^4343*100000000000000^3319 ≤ 35137979080417^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496497031 10000000000 35137979080417 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114643041/5000000000 : ℝ)^4343 ≤ (1621550546887/5000000000000 : ℝ)^3319 := by
    have hnat : (2114643041 : ℕ)^4343*5000000000000^3319 ≤ 1621550546887^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114643041 5000000000 1621550546887 5000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845857197/2000000000 : ℝ)^4343 ≤ (32431009964437/100000000000000 : ℝ)^3319 := by
    have hnat : (845857197 : ℕ)^4343*100000000000000^3319 ≤ 32431009964437^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845857197 2000000000 32431009964437 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496497031/10000000000 : ℝ), (2114643041/5000000000 : ℝ), (845857197/2000000000 : ℝ)] ![(35137979080417/100000000000000 : ℝ), (1621550546887/5000000000000 : ℝ), (32431009964437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496497031/10000000000 : ℝ)|^4343 ≤ (35137979080417/100000000000000 : ℝ)^3319
        have hw : |(4496497031/10000000000 : ℝ)|=(4496497031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114643041/5000000000 : ℝ)|^4343 ≤ (1621550546887/5000000000000 : ℝ)^3319
        have hw : |(2114643041/5000000000 : ℝ)|=(2114643041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845857197/2000000000 : ℝ)|^4343 ≤ (32431009964437/100000000000000 : ℝ)^3319
        have hw : |(845857197/2000000000 : ℝ)|=(845857197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_12 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-59839279/312500000 : ℝ)*x 0 + (547058729/1000000000 : ℝ)*x 1 + (5254662681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59839279/312500000 : ℝ)^4343 ≤ (11498898665771/100000000000000 : ℝ)^3319 := by
    have hnat : (59839279 : ℕ)^4343*100000000000000^3319 ≤ 11498898665771^3319*312500000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59839279 312500000 11498898665771 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547058729/1000000000 : ℝ)^4343 ≤ (45416163126803/100000000000000 : ℝ)^3319 := by
    have hnat : (547058729 : ℕ)^4343*100000000000000^3319 ≤ 45416163126803^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547058729 1000000000 45416163126803 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254662681/10000000000 : ℝ)^4343 ≤ (43084938192109/100000000000000 : ℝ)^3319 := by
    have hnat : (5254662681 : ℕ)^4343*100000000000000^3319 ≤ 43084938192109^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254662681 10000000000 43084938192109 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59839279/312500000 : ℝ), (547058729/1000000000 : ℝ), (5254662681/10000000000 : ℝ)] ![(11498898665771/100000000000000 : ℝ), (45416163126803/100000000000000 : ℝ), (43084938192109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59839279/312500000 : ℝ)|^4343 ≤ (11498898665771/100000000000000 : ℝ)^3319
        have hw : |(-59839279/312500000 : ℝ)|=(59839279/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547058729/1000000000 : ℝ)|^4343 ≤ (45416163126803/100000000000000 : ℝ)^3319
        have hw : |(547058729/1000000000 : ℝ)|=(547058729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254662681/10000000000 : ℝ)|^4343 ≤ (43084938192109/100000000000000 : ℝ)^3319
        have hw : |(5254662681/10000000000 : ℝ)|=(5254662681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_13 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689651351/5000000000 : ℝ)*x 0 + (-2039496429/10000000000 : ℝ)*x 1 + (5254662391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689651351/5000000000 : ℝ)^4343 ≤ (44427079930721/100000000000000 : ℝ)^3319 := by
    have hnat : (2689651351 : ℕ)^4343*100000000000000^3319 ≤ 44427079930721^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689651351 5000000000 44427079930721 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039496429/10000000000 : ℝ)^4343 ≤ (19512476533/156250000000 : ℝ)^3319 := by
    have hnat : (2039496429 : ℕ)^4343*156250000000^3319 ≤ 19512476533^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039496429 10000000000 19512476533 156250000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254662391/10000000000 : ℝ)^4343 ≤ (4308493508067/10000000000000 : ℝ)^3319 := by
    have hnat : (5254662391 : ℕ)^4343*10000000000000^3319 ≤ 4308493508067^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254662391 10000000000 4308493508067 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689651351/5000000000 : ℝ), (-2039496429/10000000000 : ℝ), (5254662391/10000000000 : ℝ)] ![(44427079930721/100000000000000 : ℝ), (19512476533/156250000000 : ℝ), (4308493508067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689651351/5000000000 : ℝ)|^4343 ≤ (44427079930721/100000000000000 : ℝ)^3319
        have hw : |(2689651351/5000000000 : ℝ)|=(2689651351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039496429/10000000000 : ℝ)|^4343 ≤ (19512476533/156250000000 : ℝ)^3319
        have hw : |(-2039496429/10000000000 : ℝ)|=(2039496429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254662391/10000000000 : ℝ)|^4343 ≤ (4308493508067/10000000000000 : ℝ)^3319
        have hw : |(5254662391/10000000000 : ℝ)|=(5254662391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_14 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379303031/10000000000 : ℝ)*x 0 + (105093239/200000000 : ℝ)*x 1 + (-1019748287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379303031/10000000000 : ℝ)^4343 ≤ (22213541743109/50000000000000 : ℝ)^3319 := by
    have hnat : (5379303031 : ℕ)^4343*50000000000000^3319 ≤ 22213541743109^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379303031 10000000000 22213541743109 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105093239/200000000 : ℝ)^4343 ≤ (21542465174569/50000000000000 : ℝ)^3319 := by
    have hnat : (105093239 : ℕ)^4343*50000000000000^3319 ≤ 21542465174569^3319*200000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105093239 200000000 21542465174569 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019748287/5000000000 : ℝ)^4343 ≤ (1248798614289/10000000000000 : ℝ)^3319 := by
    have hnat : (1019748287 : ℕ)^4343*10000000000000^3319 ≤ 1248798614289^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019748287 5000000000 1248798614289 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379303031/10000000000 : ℝ), (105093239/200000000 : ℝ), (-1019748287/5000000000 : ℝ)] ![(22213541743109/50000000000000 : ℝ), (21542465174569/50000000000000 : ℝ), (1248798614289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379303031/10000000000 : ℝ)|^4343 ≤ (22213541743109/50000000000000 : ℝ)^3319
        have hw : |(5379303031/10000000000 : ℝ)|=(5379303031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105093239/200000000 : ℝ)|^4343 ≤ (21542465174569/50000000000000 : ℝ)^3319
        have hw : |(105093239/200000000 : ℝ)|=(105093239/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019748287/5000000000 : ℝ)|^4343 ≤ (1248798614289/10000000000000 : ℝ)^3319
        have hw : |(-1019748287/5000000000 : ℝ)|=(1019748287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_box_15 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035134857/2500000000 : ℝ)*x 0 + (4407260457/10000000000 : ℝ)*x 1 + (110181483/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035134857/2500000000 : ℝ)^4343 ≤ (7885854929147/25000000000000 : ℝ)^3319 := by
    have hnat : (1035134857 : ℕ)^4343*25000000000000^3319 ≤ 7885854929147^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035134857 2500000000 7885854929147 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407260457/10000000000 : ℝ)^4343 ≤ (6845659182449/20000000000000 : ℝ)^3319 := by
    have hnat : (4407260457 : ℕ)^4343*20000000000000^3319 ≤ 6845659182449^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407260457 10000000000 6845659182449 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110181483/250000000 : ℝ)^4343 ≤ (34228284357521/100000000000000 : ℝ)^3319 := by
    have hnat : (110181483 : ℕ)^4343*100000000000000^3319 ≤ 34228284357521^3319*250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110181483 250000000 34228284357521 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035134857/2500000000 : ℝ), (4407260457/10000000000 : ℝ), (110181483/250000000 : ℝ)] ![(7885854929147/25000000000000 : ℝ), (6845659182449/20000000000000 : ℝ), (34228284357521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035134857/2500000000 : ℝ)|^4343 ≤ (7885854929147/25000000000000 : ℝ)^3319
        have hw : |(1035134857/2500000000 : ℝ)|=(1035134857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407260457/10000000000 : ℝ)|^4343 ≤ (6845659182449/20000000000000 : ℝ)^3319
        have hw : |(4407260457/10000000000 : ℝ)|=(4407260457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110181483/250000000 : ℝ)|^4343 ≤ (34228284357521/100000000000000 : ℝ)^3319
        have hw : |(110181483/250000000 : ℝ)|=(110181483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31437/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29511/50000 : ℝ) ∧ (80191/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8451/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (2171/512 : ℝ) ≤ (9451878356660671/100000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^2171 ≤ (9451878356660671/100000000000000000000 : ℝ)^512 := by
      have hnat : (11243 : ℕ)^2171*100000000000000000000^512 ≤ 9451878356660671^512*100000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 9451878356660671 100000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (9451878356660671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (2171/512 : ℝ) ≤ (14862084010521683/50000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^2171 ≤ (14862084010521683/50000000000000000000 : ℝ)^512 := by
      have hnat : (14731 : ℕ)^2171*50000000000000000000^512 ≤ 14862084010521683^512*100000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 14862084010521683 50000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (14862084010521683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009451878356660671/50000000000000000000 : ℝ) ≤ (625027861654887/625000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (50009451878356660671/50000000000000000000 : ℝ)^512 ≤ (625027861654887/625000000000000 : ℝ)^2171 := by
      have hnat : (50009451878356660671 : ℕ)^512*625000000000000^2171 ≤ 625027861654887^2171*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009451878356660671 50000000000000000000 625027861654887 625000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625027861654887/625000000000000 : ℝ)) (X := (50009451878356660671/50000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039176046377704037/100000000000000000000 : ℝ) ≤ (10000923774023147/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (100039176046377704037/100000000000000000000 : ℝ)^512 ≤ (10000923774023147/10000000000000000 : ℝ)^2171 := by
      have hnat : (100039176046377704037 : ℕ)^512*10000000000000000^2171 ≤ 10000923774023147^2171*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039176046377704037 100000000000000000000 10000923774023147 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000923774023147/10000000000000000 : ℝ)) (X := (100039176046377704037/100000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014862084010521683/25000000000000000000 : ℝ) ≤ (5000700880784051/5000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (25014862084010521683/25000000000000000000 : ℝ)^512 ≤ (5000700880784051/5000000000000000 : ℝ)^2171 := by
      have hnat : (25014862084010521683 : ℕ)^512*5000000000000000^2171 ≤ 5000700880784051^2171*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014862084010521683 25000000000000000000 5000700880784051 5000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000700880784051/5000000000000000 : ℝ)) (X := (25014862084010521683/25000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9451878356660671/100000000000000000000 : ℝ) ≤ ((17435403437650037783/17440000000000000000 : ℝ)+2*(95597508991/69760000000000 : ℝ)*(11243/100000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (17435403437650037783/17440000000000000000 : ℝ)+2*(95597508991/69760000000000 : ℝ)*(11243/100000 : ℝ)=(625027861654887/625000000000000 : ℝ) by norm_num, show 1+2*(9451878356660671/100000000000000000000 : ℝ)=(50009451878356660671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14862084010521683/50000000000000000000 : ℝ)+(9451878356660671/100000000000000000000 : ℝ) ≤ ((17435403437650037783/17440000000000000000 : ℝ)+(95597508991/69760000000000 : ℝ)*((14731/100000 : ℝ)+(11243/100000 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (17435403437650037783/17440000000000000000 : ℝ)+(95597508991/69760000000000 : ℝ)*((14731/100000 : ℝ)+(11243/100000 : ℝ))=(10000923774023147/10000000000000000 : ℝ) by norm_num, show 1+(14862084010521683/50000000000000000000 : ℝ)+(9451878356660671/100000000000000000000 : ℝ)=(100039176046377704037/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14862084010521683/50000000000000000000 : ℝ) ≤ ((17435403437650037783/17440000000000000000 : ℝ)+2*(95597508991/69760000000000 : ℝ)*(14731/100000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (17435403437650037783/17440000000000000000 : ℝ)+2*(95597508991/69760000000000 : ℝ)*(14731/100000 : ℝ)=(5000700880784051/5000000000000000 : ℝ) by norm_num, show 1+2*(14862084010521683/50000000000000000000 : ℝ)=(25014862084010521683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17435403437650037783/17440000000000000000 : ℝ)*(X 1 0+X 2 0)+(95597508991/69760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (17435403437650037783/17440000000000000000 : ℝ)) (alpha := (95597508991/69760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17435403437650037783/17440000000000000000 : ℝ)*(X 0 1+X 2 1)+(95597508991/69760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (17435403437650037783/17440000000000000000 : ℝ)) (alpha := (95597508991/69760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17435403437650037783/17440000000000000000 : ℝ)*(X 0 2+X 1 2)+(95597508991/69760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (17435403437650037783/17440000000000000000 : ℝ)) (alpha := (95597508991/69760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-369002211/2000000000 : ℝ)*X 0 0+(5388214279/10000000000 : ℝ)*X 0 1+(2694107139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285661237/10000000000 : ℝ)*X 1 0+(-992852407/5000000000 : ℝ)*X 1 1+(5388214399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285660741/10000000000 : ℝ)*X 2 0+(5388214783/10000000000 : ℝ)*X 2 1+(-992852481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((44632709/100000000 : ℝ)*X 0 0+(212309297/500000000 : ℝ)*X 0 1+(4246186793/10000000000 : ℝ)*X 0 2+(44632709/100000000 : ℝ)*X 1 0+(212309297/500000000 : ℝ)*X 1 1+(4246186793/10000000000 : ℝ)*X 1 2+(44632709/100000000 : ℝ)*X 2 0+(212309297/500000000 : ℝ)*X 2 1+(4246186793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087943217/5000000000 : ℝ)*X 0 0+(5265761727/10000000000 : ℝ)*X 0 1+(263288117/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371521657/10000000000 : ℝ)*X 1 0+(-2035119993/10000000000 : ℝ)*X 1 1+(5265761677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371522137/10000000000 : ℝ)*X 2 0+(2632880923/5000000000 : ℝ)*X 2 1+(-2035119119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4167773009/10000000000 : ℝ)*X 0 0+(34327211/78125000 : ℝ)*X 0 1+(43938831/100000000 : ℝ)*X 0 2+(4167773009/10000000000 : ℝ)*X 1 0+(34327211/78125000 : ℝ)*X 1 1+(43938831/100000000 : ℝ)*X 1 2+(4167773009/10000000000 : ℝ)*X 2 0+(34327211/78125000 : ℝ)*X 2 1+(43938831/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2106300239/10000000000 : ℝ)*X 0 0+(5181272789/10000000000 : ℝ)*X 0 1+(5402214703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((329740021/625000000 : ℝ)*X 1 0+(-1979925939/10000000000 : ℝ)*X 1 1+(168819187/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275839809/10000000000 : ℝ)*X 2 0+(675276813/1250000000 : ℝ)*X 2 1+(-1979925943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4496497031/10000000000 : ℝ)*X 0 0+(2114643041/5000000000 : ℝ)*X 0 1+(845857197/2000000000 : ℝ)*X 0 2+(4496497031/10000000000 : ℝ)*X 1 0+(2114643041/5000000000 : ℝ)*X 1 1+(845857197/2000000000 : ℝ)*X 1 2+(4496497031/10000000000 : ℝ)*X 2 0+(2114643041/5000000000 : ℝ)*X 2 1+(845857197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-59839279/312500000 : ℝ)*X 0 0+(547058729/1000000000 : ℝ)*X 0 1+(5254662681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689651351/5000000000 : ℝ)*X 1 0+(-2039496429/10000000000 : ℝ)*X 1 1+(5254662391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379303031/10000000000 : ℝ)*X 2 0+(105093239/200000000 : ℝ)*X 2 1+(-1019748287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1035134857/2500000000 : ℝ)*X 0 0+(4407260457/10000000000 : ℝ)*X 0 1+(110181483/250000000 : ℝ)*X 0 2+(1035134857/2500000000 : ℝ)*X 1 0+(4407260457/10000000000 : ℝ)*X 1 1+(110181483/250000000 : ℝ)*X 1 2+(1035134857/2500000000 : ℝ)*X 2 0+(4407260457/10000000000 : ℝ)*X 2 1+(110181483/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31437/50000 : ℝ) ≤ (-274118206960460963155308849912747/436000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56519327/100000000000000 : ℝ)*(upper0) + (31533857/100000000000000 : ℝ)*(lower1) + (84335569/25000000000000 : ℝ)*(lower2) + (9704261/10000000000000 : ℝ)*(lower3) + (10478989/10000000000000 : ℝ)*(upper5) + (2966339768007303/100000000000000 : ℝ)*(major0) + (2966339768007303/100000000000000 : ℝ)*(major1) + (2966339768007303/100000000000000 : ℝ)*(major2) + (8306358461/50000000000000 : ℝ)*(sp1) + (2028174914850101/50000000000000 : ℝ)*(sp4) + (50704165212291/1250000000000 : ℝ)*(sp5) + (2028174914850101/50000000000000 : ℝ)*(sp6) + (948634056091093/50000000000000 : ℝ)*(sp7) + (18643594021/100000000000000 : ℝ)*(sp15) + (118580422236013/6250000000000 : ℝ)*(f.failure) + (2028174914850101/50000000000000 : ℝ)*(f.sum) + (2908819401799/3488000000000000000000000000 : ℝ)*base66 + (706875911272179249/1744000000000000000000000000000000 : ℝ)*base67 + (930486252888179249/1744000000000000000000000000000000 : ℝ)*base69 + (12900168415704179249/1744000000000000000000000000000000 : ℝ)*base71 + (27042198704217/3488000000000000000000000000 : ℝ)*base73 + (1238951442936179249/1744000000000000000000000000000000 : ℝ)*base75 + (5446928189095820751/1744000000000000000000000000000000 : ℝ)*base78 + (1170214789000179249/1744000000000000000000000000000000 : ℝ)*base79 + (29360404617657/3488000000000000000000000000 : ℝ)*base81 + (1496339/156250000000000000000 : ℝ)*base89 + (1496339/156250000000000000000 : ℝ)*base91 + (1496339/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29511/50000 : ℝ) ≤ (257344793868759646855897489185669/436000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20865911/25000000000000 : ℝ)*(lower1) + (22895603/20000000000000 : ℝ)*(upper2) + (26161533/50000000000000 : ℝ)*(lower4) + (1518207442244319/50000000000000 : ℝ)*(major0) + (1518207442244319/50000000000000 : ℝ)*(major1) + (1518207442244319/50000000000000 : ℝ)*(major2) + (1027759802368561/25000000000000 : ℝ)*(sp0) + (411104117403833/10000000000000 : ℝ)*(sp1) + (164441474095779/4000000000000 : ℝ)*(sp2) + (1942104039024773/100000000000000 : ℝ)*(sp3) + (6742032071/100000000000000 : ℝ)*(sp5) + (5531837963/50000000000000 : ℝ)*(sp6) + (3135451759/100000000000000 : ℝ)*(sp7) + (4353298079/50000000000000 : ℝ)*(sp12) + (485526793619133/25000000000000 : ℝ)*(f.failure) + (2055523958035201/50000000000000 : ℝ)*(f.sum) + (3107323490801/1744000000000000000000000000 : ℝ)*base65 + (1062069572963354777/872000000000000000000000000000000 : ℝ)*base67 + (8009753416468645223/872000000000000000000000000000000 : ℝ)*base70 + (5843690467363354777/872000000000000000000000000000000 : ℝ)*base71 + (791713395793/1744000000000000000000000000 : ℝ)*base73 + (3550363996172645223/872000000000000000000000000000000 : ℝ)*base76 + (7363146996803354777/872000000000000000000000000000000 : ℝ)*base77 + (7984980970363354777/872000000000000000000000000000000 : ℝ)*base79 + (7194054191151/1744000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2724801/625000000000000000000 : ℝ)*base90 + (2724801/625000000000000000000 : ℝ)*base92 + (2724801/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80191/100000 : ℝ) ≤ (349643561030913499258173765327639/436000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382859/20000000000000 : ℝ)*(upper1) + (61841/80000000000 : ℝ)*(upper2) + (5776229/5000000000000 : ℝ)*(lower5) + (1673350849239211/50000000000000 : ℝ)*(major0) + (1673350849239211/50000000000000 : ℝ)*(major1) + (1673350849239211/50000000000000 : ℝ)*(major2) + (20520510221/12500000000000 : ℝ)*(sp2) + (61204018313/100000000000000 : ℝ)*(sp3) + (12646430481/100000000000000 : ℝ)*(sp4) + (1131520270893631/25000000000000 : ℝ)*(sp8) + (4526103960230633/100000000000000 : ℝ)*(sp9) + (905187959229773/20000000000000 : ℝ)*(sp10) + (214050707360767/10000000000000 : ℝ)*(sp11) + (2557556407/25000000000000 : ℝ)*(sp12) + (1070284138812991/50000000000000 : ℝ)*(f.failure) + (4526103960230633/100000000000000 : ℝ)*(f.sum) + (599041704277/1744000000000000000000000000 : ℝ)*base65 + (367490433064359213/872000000000000000000000000000000 : ℝ)*base67 + (8705740491927640787/872000000000000000000000000000000 : ℝ)*base70 + (1451560649295640787/872000000000000000000000000000000 : ℝ)*base72 + (1617335265989/1744000000000000000000000000 : ℝ)*base73 + (10597519458551640787/872000000000000000000000000000000 : ℝ)*base76 + (1300101461384359213/872000000000000000000000000000000 : ℝ)*base77 + (822456516127640787/872000000000000000000000000000000 : ℝ)*base80 + (11274188692011/1744000000000000000000000000 : ℝ)*base82 + (4540427/1250000000000000000000 : ℝ)*base90 + (4540427/1250000000000000000000 : ℝ)*base92 + (4540427/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-8451/10000 : ℝ) ≤ (-368454677058509559073163197313157/436000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359823053/100000000000000 : ℝ)*(lower0) + (30710431/25000000000000 : ℝ)*(lower1) + (1045519/500000000000 : ℝ)*(lower2) + (96089323/50000000000000 : ℝ)*(lower4) + (1691816824783393/50000000000000 : ℝ)*(major0) + (1691816824783393/50000000000000 : ℝ)*(major1) + (1691816824783393/50000000000000 : ℝ)*(major2) + (11865756031/100000000000000 : ℝ)*(sp0) + (374453760261/100000000000000 : ℝ)*(sp5) + (548532094709/100000000000000 : ℝ)*(sp6) + (2315617300218963/50000000000000 : ℝ)*(sp12) + (4630872012433697/100000000000000 : ℝ)*(sp13) + (289418620881203/6250000000000 : ℝ)*(sp14) + (270523768844691/12500000000000 : ℝ)*(sp15) + (270523768844691/12500000000000 : ℝ)*(f.failure) + (2315623233096979/50000000000000 : ℝ)*(f.sum) + (68930608111919/1744000000000000000000000000 : ℝ)*base65 + (284675276936687719/872000000000000000000000000000000 : ℝ)*base67 + (4668645468591312281/872000000000000000000000000000000 : ℝ)*base70 + (34654783505496687719/872000000000000000000000000000000 : ℝ)*base71 + (2119714981377/1744000000000000000000000000 : ℝ)*base74 + (5905365572591312281/872000000000000000000000000000000 : ℝ)*base76 + (20284335077896687719/872000000000000000000000000000000 : ℝ)*base77 + (2616613232736687719/872000000000000000000000000000000 : ℝ)*base79 + (645882716227/348800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (475327/312500000000000000000 : ℝ)*base90 + (475327/312500000000000000000 : ℝ)*base92 + (475327/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1383_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29511/50000 : ℝ) else (80191/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8451/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1383_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1383_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29511/50000 : ℝ) else (80191/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8451/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1383_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1383_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1383_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29511/50000 : ℝ) else (80191/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8451/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1383_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

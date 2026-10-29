-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1713_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:42.958833+00:00
-- url     : https://prove2.me/submissions/aed1ed65-698f-4dad-82c4-304c1b453fd8

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
theorem support_rectangle_w1713_s3_0 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-700655351/5000000000 : ℝ)*x 0 + (5468112891/10000000000 : ℝ)*x 1 + (256933093/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (700655351/5000000000 : ℝ)^5327 ≤ (8778741202527/100000000000000 : ℝ)^4303 := by
    have hnat : (700655351 : ℕ)^5327*100000000000000^4303 ≤ 8778741202527^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700655351 5000000000 8778741202527 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468112891/10000000000 : ℝ)^5327 ≤ (47364148711547/100000000000000 : ℝ)^4303 := by
    have hnat : (5468112891 : ℕ)^5327*100000000000000^4303 ≤ 47364148711547^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468112891 10000000000 47364148711547 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256933093/500000000 : ℝ)^5327 ≤ (10964277519509/25000000000000 : ℝ)^4303 := by
    have hnat : (256933093 : ℕ)^5327*25000000000000^4303 ≤ 10964277519509^4303*500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256933093 500000000 10964277519509 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-700655351/5000000000 : ℝ), (5468112891/10000000000 : ℝ), (256933093/500000000 : ℝ)] ![(8778741202527/100000000000000 : ℝ), (47364148711547/100000000000000 : ℝ), (10964277519509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-700655351/5000000000 : ℝ)|^5327 ≤ (8778741202527/100000000000000 : ℝ)^4303
        have hw : |(-700655351/5000000000 : ℝ)|=(700655351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468112891/10000000000 : ℝ)|^5327 ≤ (47364148711547/100000000000000 : ℝ)^4303
        have hw : |(5468112891/10000000000 : ℝ)|=(5468112891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256933093/500000000 : ℝ)|^5327 ≤ (10964277519509/25000000000000 : ℝ)^4303
        have hw : |(256933093/500000000 : ℝ)|=(256933093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_1 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335627073/2500000000 : ℝ)*x 0 + (-786048711/5000000000 : ℝ)*x 1 + (513866187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335627073/2500000000 : ℝ)^5327 ≤ (46020970884009/100000000000000 : ℝ)^4303 := by
    have hnat : (1335627073 : ℕ)^5327*100000000000000^4303 ≤ 46020970884009^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335627073 2500000000 46020970884009 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786048711/5000000000 : ℝ)^5327 ≤ (10121918910299/100000000000000 : ℝ)^4303 := by
    have hnat : (786048711 : ℕ)^5327*100000000000000^4303 ≤ 10121918910299^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786048711 5000000000 10121918910299 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513866187/1000000000 : ℝ)^5327 ≤ (21928555091847/50000000000000 : ℝ)^4303 := by
    have hnat : (513866187 : ℕ)^5327*50000000000000^4303 ≤ 21928555091847^4303*1000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513866187 1000000000 21928555091847 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335627073/2500000000 : ℝ), (-786048711/5000000000 : ℝ), (513866187/1000000000 : ℝ)] ![(46020970884009/100000000000000 : ℝ), (10121918910299/100000000000000 : ℝ), (21928555091847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335627073/2500000000 : ℝ)|^5327 ≤ (46020970884009/100000000000000 : ℝ)^4303
        have hw : |(1335627073/2500000000 : ℝ)|=(1335627073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-786048711/5000000000 : ℝ)|^5327 ≤ (10121918910299/100000000000000 : ℝ)^4303
        have hw : |(-786048711/5000000000 : ℝ)|=(786048711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513866187/1000000000 : ℝ)|^5327 ≤ (21928555091847/50000000000000 : ℝ)^4303
        have hw : |(513866187/1000000000 : ℝ)|=(513866187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_2 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068501659/2000000000 : ℝ)*x 0 + (5138661873/10000000000 : ℝ)*x 1 + (-314419483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068501659/2000000000 : ℝ)^5327 ≤ (46020970916001/100000000000000 : ℝ)^4303 := by
    have hnat : (1068501659 : ℕ)^5327*100000000000000^4303 ≤ 46020970916001^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068501659 2000000000 46020970916001 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138661873/10000000000 : ℝ)^5327 ≤ (43857110215391/100000000000000 : ℝ)^4303 := by
    have hnat : (5138661873 : ℕ)^5327*100000000000000^4303 ≤ 43857110215391^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138661873 10000000000 43857110215391 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314419483/2000000000 : ℝ)^5327 ≤ (1265239856813/12500000000000 : ℝ)^4303 := by
    have hnat : (314419483 : ℕ)^5327*12500000000000^4303 ≤ 1265239856813^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314419483 2000000000 1265239856813 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068501659/2000000000 : ℝ), (5138661873/10000000000 : ℝ), (-314419483/2000000000 : ℝ)] ![(46020970916001/100000000000000 : ℝ), (43857110215391/100000000000000 : ℝ), (1265239856813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068501659/2000000000 : ℝ)|^5327 ≤ (46020970916001/100000000000000 : ℝ)^4303
        have hw : |(1068501659/2000000000 : ℝ)|=(1068501659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138661873/10000000000 : ℝ)|^5327 ≤ (43857110215391/100000000000000 : ℝ)^4303
        have hw : |(5138661873/10000000000 : ℝ)|=(5138661873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314419483/2000000000 : ℝ)|^5327 ≤ (1265239856813/12500000000000 : ℝ)^4303
        have hw : |(-314419483/2000000000 : ℝ)|=(314419483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_3 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025218739/2500000000 : ℝ)*x 0 + (3637720997/10000000000 : ℝ)*x 1 + (287463451/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025218739/2500000000 : ℝ)^5327 ≤ (33170452534283/100000000000000 : ℝ)^4303 := by
    have hnat : (1025218739 : ℕ)^5327*100000000000000^4303 ≤ 33170452534283^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025218739 2500000000 33170452534283 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3637720997/10000000000 : ℝ)^5327 ≤ (1143874575637/4000000000000 : ℝ)^4303 := by
    have hnat : (3637720997 : ℕ)^5327*4000000000000^4303 ≤ 1143874575637^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637720997 10000000000 1143874575637 4000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287463451/625000000 : ℝ)^5327 ≤ (19116341533199/50000000000000 : ℝ)^4303 := by
    have hnat : (287463451 : ℕ)^5327*50000000000000^4303 ≤ 19116341533199^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287463451 625000000 19116341533199 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025218739/2500000000 : ℝ), (3637720997/10000000000 : ℝ), (287463451/625000000 : ℝ)] ![(33170452534283/100000000000000 : ℝ), (1143874575637/4000000000000 : ℝ), (19116341533199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025218739/2500000000 : ℝ)|^5327 ≤ (33170452534283/100000000000000 : ℝ)^4303
        have hw : |(1025218739/2500000000 : ℝ)|=(1025218739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3637720997/10000000000 : ℝ)|^5327 ≤ (1143874575637/4000000000000 : ℝ)^4303
        have hw : |(3637720997/10000000000 : ℝ)|=(3637720997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287463451/625000000 : ℝ)|^5327 ≤ (19116341533199/50000000000000 : ℝ)^4303
        have hw : |(287463451/625000000 : ℝ)|=(287463451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_4 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-280291917/2000000000 : ℝ)*x 0 + (1285579969/2500000000 : ℝ)*x 1 + (1092880057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280291917/2000000000 : ℝ)^5327 ≤ (8779895877517/100000000000000 : ℝ)^4303 := by
    have hnat : (280291917 : ℕ)^5327*100000000000000^4303 ≤ 8779895877517^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280291917 2000000000 8779895877517 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285579969/2500000000 : ℝ)^5327 ≤ (21947881560927/50000000000000 : ℝ)^4303 := by
    have hnat : (1285579969 : ℕ)^5327*50000000000000^4303 ≤ 21947881560927^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285579969 2500000000 21947881560927 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092880057/2000000000 : ℝ)^5327 ≤ (236621704921/500000000000 : ℝ)^4303 := by
    have hnat : (1092880057 : ℕ)^5327*500000000000^4303 ≤ 236621704921^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092880057 2000000000 236621704921 500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280291917/2000000000 : ℝ), (1285579969/2500000000 : ℝ), (1092880057/2000000000 : ℝ)] ![(8779895877517/100000000000000 : ℝ), (21947881560927/50000000000000 : ℝ), (236621704921/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280291917/2000000000 : ℝ)|^5327 ≤ (8779895877517/100000000000000 : ℝ)^4303
        have hw : |(-280291917/2000000000 : ℝ)|=(280291917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285579969/2500000000 : ℝ)|^5327 ≤ (21947881560927/50000000000000 : ℝ)^4303
        have hw : |(1285579969/2500000000 : ℝ)|=(1285579969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092880057/2000000000 : ℝ)|^5327 ≤ (236621704921/500000000000 : ℝ)^4303
        have hw : |(1092880057/2000000000 : ℝ)|=(1092880057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_5 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627159303/5000000000 : ℝ)*x 0 + (-1246358789/10000000000 : ℝ)*x 1 + (136610007/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627159303/5000000000 : ℝ)^5327 ≤ (45082367194363/100000000000000 : ℝ)^4303 := by
    have hnat : (2627159303 : ℕ)^5327*100000000000000^4303 ≤ 45082367194363^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627159303 5000000000 45082367194363 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246358789/10000000000 : ℝ)^5327 ≤ (7593291860309/100000000000000 : ℝ)^4303 := by
    have hnat : (1246358789 : ℕ)^5327*100000000000000^4303 ≤ 7593291860309^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246358789 10000000000 7593291860309 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136610007/250000000 : ℝ)^5327 ≤ (47324340930593/100000000000000 : ℝ)^4303 := by
    have hnat : (136610007 : ℕ)^5327*100000000000000^4303 ≤ 47324340930593^4303*250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136610007 250000000 47324340930593 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627159303/5000000000 : ℝ), (-1246358789/10000000000 : ℝ), (136610007/250000000 : ℝ)] ![(45082367194363/100000000000000 : ℝ), (7593291860309/100000000000000 : ℝ), (47324340930593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627159303/5000000000 : ℝ)|^5327 ≤ (45082367194363/100000000000000 : ℝ)^4303
        have hw : |(2627159303/5000000000 : ℝ)|=(2627159303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1246358789/10000000000 : ℝ)|^5327 ≤ (7593291860309/100000000000000 : ℝ)^4303
        have hw : |(-1246358789/10000000000 : ℝ)|=(1246358789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136610007/250000000 : ℝ)|^5327 ≤ (47324340930593/100000000000000 : ℝ)^4303
        have hw : |(136610007/250000000 : ℝ)|=(136610007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_6 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627159187/5000000000 : ℝ)*x 0 + (5464400449/10000000000 : ℝ)*x 1 + (-9970871/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627159187/5000000000 : ℝ)^5327 ≤ (9016472946017/20000000000000 : ℝ)^4303 := by
    have hnat : (2627159187 : ℕ)^5327*20000000000000^4303 ≤ 9016472946017^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627159187 5000000000 9016472946017 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464400449/10000000000 : ℝ)^5327 ≤ (23662171371259/50000000000000 : ℝ)^4303 := by
    have hnat : (5464400449 : ℕ)^5327*50000000000000^4303 ≤ 23662171371259^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464400449 10000000000 23662171371259 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9970871/80000000 : ℝ)^5327 ≤ (7593292508939/100000000000000 : ℝ)^4303 := by
    have hnat : (9970871 : ℕ)^5327*100000000000000^4303 ≤ 7593292508939^4303*80000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9970871 80000000 7593292508939 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627159187/5000000000 : ℝ), (5464400449/10000000000 : ℝ), (-9970871/80000000 : ℝ)] ![(9016472946017/20000000000000 : ℝ), (23662171371259/50000000000000 : ℝ), (7593292508939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627159187/5000000000 : ℝ)|^5327 ≤ (9016472946017/20000000000000 : ℝ)^4303
        have hw : |(2627159187/5000000000 : ℝ)|=(2627159187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464400449/10000000000 : ℝ)|^5327 ≤ (23662171371259/50000000000000 : ℝ)^4303
        have hw : |(5464400449/10000000000 : ℝ)|=(5464400449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9970871/80000000 : ℝ)|^5327 ≤ (7593292508939/100000000000000 : ℝ)^4303
        have hw : |(-9970871/80000000 : ℝ)|=(9970871/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s3_7 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4101308837/10000000000 : ℝ)*x 0 + (4588737339/10000000000 : ℝ)*x 1 + (729711697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4101308837/10000000000 : ℝ)^5327 ≤ (33174797259553/100000000000000 : ℝ)^4303 := by
    have hnat : (4101308837 : ℕ)^5327*100000000000000^4303 ≤ 33174797259553^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101308837 10000000000 33174797259553 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4588737339/10000000000 : ℝ)^5327 ≤ (9530707741303/25000000000000 : ℝ)^4303 := by
    have hnat : (4588737339 : ℕ)^5327*25000000000000^4303 ≤ 9530707741303^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4588737339 10000000000 9530707741303 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729711697/2000000000 : ℝ)^5327 ≤ (14351185882799/50000000000000 : ℝ)^4303 := by
    have hnat : (729711697 : ℕ)^5327*50000000000000^4303 ≤ 14351185882799^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729711697 2000000000 14351185882799 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4101308837/10000000000 : ℝ), (4588737339/10000000000 : ℝ), (729711697/2000000000 : ℝ)] ![(33174797259553/100000000000000 : ℝ), (9530707741303/25000000000000 : ℝ), (14351185882799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4101308837/10000000000 : ℝ)|^5327 ≤ (33174797259553/100000000000000 : ℝ)^4303
        have hw : |(4101308837/10000000000 : ℝ)|=(4101308837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4588737339/10000000000 : ℝ)|^5327 ≤ (9530707741303/25000000000000 : ℝ)^4303
        have hw : |(4588737339/10000000000 : ℝ)|=(4588737339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729711697/2000000000 : ℝ)|^5327 ≤ (14351185882799/50000000000000 : ℝ)^4303
        have hw : |(729711697/2000000000 : ℝ)|=(729711697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1713_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5017/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (401/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (401/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (401/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (401/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (401/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (401/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (401/4000 : ℝ) ^ (5319/1024 : ℝ) ≤ (647584884548231/100000000000000000000 : ℝ) := by
    have hpowers : (401/4000 : ℝ)^5319 ≤ (647584884548231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (401 : ℕ)^5319*100000000000000000000^1024 ≤ 647584884548231^1024*4000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401 4000 647584884548231 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (401/4000 : ℝ)) (X := (647584884548231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17081/100000 : ℝ) ^ (5319/1024 : ℝ) ≤ (515687042278609/5000000000000000000 : ℝ) := by
    have hpowers : (17081/100000 : ℝ)^5319 ≤ (515687042278609/5000000000000000000 : ℝ)^1024 := by
      have hnat : (17081 : ℕ)^5319*5000000000000000000^1024 ≤ 515687042278609^1024*100000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17081 100000 515687042278609 5000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17081/100000 : ℝ)) (X := (515687042278609/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000647584884548231/50000000000000000000 : ℝ) ≤ (2000004986828007/2000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50000647584884548231/50000000000000000000 : ℝ)^1024 ≤ (2000004986828007/2000000000000000 : ℝ)^5319 := by
      have hnat : (50000647584884548231 : ℕ)^1024*2000000000000000^5319 ≤ 2000004986828007^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000647584884548231 50000000000000000000 2000004986828007 2000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000004986828007/2000000000000000 : ℝ)) (X := (50000647584884548231/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010961325730120411/100000000000000000000 : ℝ) ≤ (156253297113191/156250000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (100010961325730120411/100000000000000000000 : ℝ)^1024 ≤ (156253297113191/156250000000000 : ℝ)^5319 := by
      have hnat : (100010961325730120411 : ℕ)^1024*156250000000000^5319 ≤ 156253297113191^5319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010961325730120411 100000000000000000000 156253297113191 156250000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156253297113191/156250000000000 : ℝ)) (X := (100010961325730120411/100000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500515687042278609/2500000000000000000 : ℝ) ≤ (10000397096348413/10000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (2500515687042278609/2500000000000000000 : ℝ)^1024 ≤ (10000397096348413/10000000000000000 : ℝ)^5319 := by
      have hnat : (2500515687042278609 : ℕ)^1024*10000000000000000^5319 ≤ 10000397096348413^5319*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500515687042278609 2500000000000000000 10000397096348413 10000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000397096348413/10000000000000000 : ℝ)) (X := (2500515687042278609/2500000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(647584884548231/100000000000000000000 : ℝ) ≤ ((7055644500915309751/7056000000000000000 : ℝ)+2*(186081104189/705600000000000 : ℝ)*(401/4000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (7055644500915309751/7056000000000000000 : ℝ)+2*(186081104189/705600000000000 : ℝ)*(401/4000 : ℝ)=(2000004986828007/2000000000000000 : ℝ) by norm_num, show 1+2*(647584884548231/100000000000000000000 : ℝ)=(50000647584884548231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(515687042278609/5000000000000000000 : ℝ)+(647584884548231/100000000000000000000 : ℝ) ≤ ((7055644500915309751/7056000000000000000 : ℝ)+(186081104189/705600000000000 : ℝ)*((17081/100000 : ℝ)+(401/4000 : ℝ)))^(5319/1024 : ℝ) := by
    rw [show (7055644500915309751/7056000000000000000 : ℝ)+(186081104189/705600000000000 : ℝ)*((17081/100000 : ℝ)+(401/4000 : ℝ))=(156253297113191/156250000000000 : ℝ) by norm_num, show 1+(515687042278609/5000000000000000000 : ℝ)+(647584884548231/100000000000000000000 : ℝ)=(100010961325730120411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(515687042278609/5000000000000000000 : ℝ) ≤ ((7055644500915309751/7056000000000000000 : ℝ)+2*(186081104189/705600000000000 : ℝ)*(17081/100000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (7055644500915309751/7056000000000000000 : ℝ)+2*(186081104189/705600000000000 : ℝ)*(17081/100000 : ℝ)=(10000397096348413/10000000000000000 : ℝ) by norm_num, show 1+2*(515687042278609/5000000000000000000 : ℝ)=(2500515687042278609/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7055644500915309751/7056000000000000000 : ℝ)*(X 1 0+X 2 0)+(186081104189/705600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (401/4000 : ℝ)) (hi := (17081/100000 : ℝ)) (c := (7055644500915309751/7056000000000000000 : ℝ)) (alpha := (186081104189/705600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7055644500915309751/7056000000000000000 : ℝ)*(X 0 1+X 2 1)+(186081104189/705600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (401/4000 : ℝ)) (hi := (17081/100000 : ℝ)) (c := (7055644500915309751/7056000000000000000 : ℝ)) (alpha := (186081104189/705600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7055644500915309751/7056000000000000000 : ℝ)*(X 0 2+X 1 2)+(186081104189/705600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (401/4000 : ℝ)) (hi := (17081/100000 : ℝ)) (c := (7055644500915309751/7056000000000000000 : ℝ)) (alpha := (186081104189/705600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-700655351/5000000000 : ℝ)*X 0 0+(5468112891/10000000000 : ℝ)*X 0 1+(256933093/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335627073/2500000000 : ℝ)*X 1 0+(-786048711/5000000000 : ℝ)*X 1 1+(513866187/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068501659/2000000000 : ℝ)*X 2 0+(5138661873/10000000000 : ℝ)*X 2 1+(-314419483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1025218739/2500000000 : ℝ)*X 0 0+(3637720997/10000000000 : ℝ)*X 0 1+(287463451/625000000 : ℝ)*X 0 2+(1025218739/2500000000 : ℝ)*X 1 0+(3637720997/10000000000 : ℝ)*X 1 1+(287463451/625000000 : ℝ)*X 1 2+(1025218739/2500000000 : ℝ)*X 2 0+(3637720997/10000000000 : ℝ)*X 2 1+(287463451/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-280291917/2000000000 : ℝ)*X 0 0+(1285579969/2500000000 : ℝ)*X 0 1+(1092880057/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627159303/5000000000 : ℝ)*X 1 0+(-1246358789/10000000000 : ℝ)*X 1 1+(136610007/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627159187/5000000000 : ℝ)*X 2 0+(5464400449/10000000000 : ℝ)*X 2 1+(-9970871/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4101308837/10000000000 : ℝ)*X 0 0+(4588737339/10000000000 : ℝ)*X 0 1+(729711697/2000000000 : ℝ)*X 0 2+(4101308837/10000000000 : ℝ)*X 1 0+(4588737339/10000000000 : ℝ)*X 1 1+(729711697/2000000000 : ℝ)*X 1 2+(4101308837/10000000000 : ℝ)*X 2 0+(4588737339/10000000000 : ℝ)*X 2 1+(729711697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (179940514557061160736283707/19600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1337508611/100000000000000 : ℝ)*(base19) + (157099/12500000000 : ℝ)*(base23) + (4403353/10000000000000 : ℝ)*(lower2) + (219094351/100000000000000 : ℝ)*(upper3) + (165453121/100000000000000 : ℝ)*(upper5) + (1018805100252957/50000000000000 : ℝ)*(major0) + (1018805100252957/50000000000000 : ℝ)*(major1) + (1018805100252957/50000000000000 : ℝ)*(major2) + (94855186333537/3125000000000 : ℝ)*(sp0) + (3035377953318561/100000000000000 : ℝ)*(sp1) + (758844508508793/25000000000000 : ℝ)*(sp2) + (16247435989147/1562500000000 : ℝ)*(sp3) + (3332038497/25000000000000 : ℝ)*(sp4) + (4900857961/100000000000000 : ℝ)*(sp7) + (1039840804163369/100000000000000 : ℝ)*(f.failure) + (758844822706793/25000000000000 : ℝ)*(f.sum) + (5975487120377/1960000000000000000000000000 : ℝ)*base65 + (128357030481798477/39200000000000000000000000000000 : ℝ)*base68 + (257656193884998477/39200000000000000000000000000000 : ℝ)*base70 + (108872013097798477/39200000000000000000000000000000 : ℝ)*base72 + (6843699390617/1960000000000000000000000000 : ℝ)*base73 + (436303147684998477/39200000000000000000000000000000 : ℝ)*base76 + (17604375075398477/39200000000000000000000000000000 : ℝ)*base78 + (111340966062598477/39200000000000000000000000000000 : ℝ)*base80 + (1653915311417/1960000000000000000000000000 : ℝ)*base81 + (29684557/10000000000000000000000 : ℝ)*base89 + (29684557/10000000000000000000000 : ℝ)*base91 + (29684557/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425565309780375694800415219/117600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36984571/6250000000000 : ℝ)*(base19) + (282924743/50000000000000 : ℝ)*(base23) + (100813599/50000000000000 : ℝ)*(lower1) + (14642917/25000000000000 : ℝ)*(upper2) + (32329551/50000000000000 : ℝ)*(upper3) + (16738091/25000000000000 : ℝ)*(upper5) + (2084216157577531/100000000000000 : ℝ)*(major0) + (2084216157577531/100000000000000 : ℝ)*(major1) + (2084216157577531/100000000000000 : ℝ)*(major2) + (17094407/100000000000000 : ℝ)*(sp1) + (1552403632641571/50000000000000 : ℝ)*(sp4) + (3104806656435599/100000000000000 : ℝ)*(sp5) + (388100837429207/12500000000000 : ℝ)*(sp6) + (531812464623411/50000000000000 : ℝ)*(sp7) + (531812464623411/50000000000000 : ℝ)*(f.failure) + (1552403632641571/50000000000000 : ℝ)*(f.sum) + (188665782353039/35280000000000000000000000000 : ℝ)*base65 + (91152660014535073/235200000000000000000000000000000 : ℝ)*base68 + (3913441781217464927/235200000000000000000000000000000 : ℝ)*base69 + (1665149996155064927/235200000000000000000000000000000 : ℝ)*base71 + (27568454599681/35280000000000000000000000000 : ℝ)*base74 + (6926700350535073/235200000000000000000000000000000 : ℝ)*base76 + (370605078743864927/235200000000000000000000000000000 : ℝ)*base77 + (1786265213035064927/235200000000000000000000000000000 : ℝ)*base79 + (586972123379759/35280000000000000000000000000 : ℝ)*base81 + (45865217/5000000000000000000000 : ℝ)*base90 + (45865217/5000000000000000000000 : ℝ)*base92 + (45865217/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1713_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1713_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1713_box_0 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084996361/10000000000 : ℝ)*x 0 + (5415644839/10000000000 : ℝ)*x 1 + (5415644617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084996361/10000000000 : ℝ)^5327 ≤ (6395665876109/100000000000000 : ℝ)^4303 := by
    have hnat : (1084996361 : ℕ)^5327*100000000000000^4303 ≤ 6395665876109^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084996361 10000000000 6395665876109 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415644839/10000000000 : ℝ)^5327 ≤ (23401084124187/50000000000000 : ℝ)^4303 := by
    have hnat : (5415644839 : ℕ)^5327*50000000000000^4303 ≤ 23401084124187^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415644839 10000000000 23401084124187 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415644617/10000000000 : ℝ)^5327 ≤ (46802165873283/100000000000000 : ℝ)^4303 := by
    have hnat : (5415644617 : ℕ)^5327*100000000000000^4303 ≤ 46802165873283^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415644617 10000000000 46802165873283 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084996361/10000000000 : ℝ), (5415644839/10000000000 : ℝ), (5415644617/10000000000 : ℝ)] ![(6395665876109/100000000000000 : ℝ), (23401084124187/50000000000000 : ℝ), (46802165873283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084996361/10000000000 : ℝ)|^5327 ≤ (6395665876109/100000000000000 : ℝ)^4303
        have hw : |(-1084996361/10000000000 : ℝ)|=(1084996361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415644839/10000000000 : ℝ)|^5327 ≤ (23401084124187/50000000000000 : ℝ)^4303
        have hw : |(5415644839/10000000000 : ℝ)|=(5415644839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415644617/10000000000 : ℝ)|^5327 ≤ (46802165873283/100000000000000 : ℝ)^4303
        have hw : |(5415644617/10000000000 : ℝ)|=(5415644617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_1 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612626361/5000000000 : ℝ)*x 0 + (-677694449/5000000000 : ℝ)*x 1 + (2707822417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612626361/5000000000 : ℝ)^5327 ≤ (22386918085283/50000000000000 : ℝ)^4303 := by
    have hnat : (2612626361 : ℕ)^5327*50000000000000^4303 ≤ 22386918085283^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612626361 5000000000 22386918085283 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677694449/5000000000 : ℝ)^5327 ≤ (4211997809131/50000000000000 : ℝ)^4303 := by
    have hnat : (677694449 : ℕ)^5327*50000000000000^4303 ≤ 4211997809131^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677694449 5000000000 4211997809131 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707822417/5000000000 : ℝ)^5327 ≤ (46802168194881/100000000000000 : ℝ)^4303 := by
    have hnat : (2707822417 : ℕ)^5327*100000000000000^4303 ≤ 46802168194881^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707822417 5000000000 46802168194881 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612626361/5000000000 : ℝ), (-677694449/5000000000 : ℝ), (2707822417/5000000000 : ℝ)] ![(22386918085283/50000000000000 : ℝ), (4211997809131/50000000000000 : ℝ), (46802168194881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612626361/5000000000 : ℝ)|^5327 ≤ (22386918085283/50000000000000 : ℝ)^4303
        have hw : |(2612626361/5000000000 : ℝ)|=(2612626361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-677694449/5000000000 : ℝ)|^5327 ≤ (4211997809131/50000000000000 : ℝ)^4303
        have hw : |(-677694449/5000000000 : ℝ)|=(677694449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707822417/5000000000 : ℝ)|^5327 ≤ (46802168194881/100000000000000 : ℝ)^4303
        have hw : |(2707822417/5000000000 : ℝ)|=(2707822417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_2 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612626479/5000000000 : ℝ)*x 0 + (1083128919/2000000000 : ℝ)*x 1 + (-677694453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612626479/5000000000 : ℝ)^5327 ≤ (5596729834253/12500000000000 : ℝ)^4303 := by
    have hnat : (2612626479 : ℕ)^5327*12500000000000^4303 ≤ 5596729834253^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612626479 5000000000 5596729834253 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083128919/2000000000 : ℝ)^5327 ≤ (23401082818957/50000000000000 : ℝ)^4303 := by
    have hnat : (1083128919 : ℕ)^5327*50000000000000^4303 ≤ 23401082818957^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083128919 2000000000 23401082818957 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677694453/5000000000 : ℝ)^5327 ≤ (1052999459977/12500000000000 : ℝ)^4303 := by
    have hnat : (677694453 : ℕ)^5327*12500000000000^4303 ≤ 1052999459977^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677694453 5000000000 1052999459977 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612626479/5000000000 : ℝ), (1083128919/2000000000 : ℝ), (-677694453/5000000000 : ℝ)] ![(5596729834253/12500000000000 : ℝ), (23401082818957/50000000000000 : ℝ), (1052999459977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612626479/5000000000 : ℝ)|^5327 ≤ (5596729834253/12500000000000 : ℝ)^4303
        have hw : |(2612626479/5000000000 : ℝ)|=(2612626479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083128919/2000000000 : ℝ)|^5327 ≤ (23401082818957/50000000000000 : ℝ)^4303
        have hw : |(1083128919/2000000000 : ℝ)|=(1083128919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-677694453/5000000000 : ℝ)|^5327 ≤ (1052999459977/12500000000000 : ℝ)^4303
        have hw : |(-677694453/5000000000 : ℝ)|=(677694453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_3 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482419511/10000000000 : ℝ)*x 0 + (3931597537/10000000000 : ℝ)*x 1 + (3931597587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482419511/10000000000 : ℝ)^5327 ≤ (18516193544201/50000000000000 : ℝ)^4303 := by
    have hnat : (4482419511 : ℕ)^5327*50000000000000^4303 ≤ 18516193544201^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482419511 10000000000 18516193544201 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3931597537/10000000000 : ℝ)^5327 ≤ (15741903099409/50000000000000 : ℝ)^4303 := by
    have hnat : (3931597537 : ℕ)^5327*50000000000000^4303 ≤ 15741903099409^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931597537 10000000000 15741903099409 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3931597587/10000000000 : ℝ)^5327 ≤ (983868959203/3125000000000 : ℝ)^4303 := by
    have hnat : (3931597587 : ℕ)^5327*3125000000000^4303 ≤ 983868959203^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931597587 10000000000 983868959203 3125000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482419511/10000000000 : ℝ), (3931597537/10000000000 : ℝ), (3931597587/10000000000 : ℝ)] ![(18516193544201/50000000000000 : ℝ), (15741903099409/50000000000000 : ℝ), (983868959203/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482419511/10000000000 : ℝ)|^5327 ≤ (18516193544201/50000000000000 : ℝ)^4303
        have hw : |(4482419511/10000000000 : ℝ)|=(4482419511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3931597537/10000000000 : ℝ)|^5327 ≤ (15741903099409/50000000000000 : ℝ)^4303
        have hw : |(3931597537/10000000000 : ℝ)|=(3931597537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3931597587/10000000000 : ℝ)|^5327 ≤ (983868959203/3125000000000 : ℝ)^4303
        have hw : |(3931597587/10000000000 : ℝ)|=(3931597587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_4 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6952863/40000000 : ℝ)*x 0 + (2588800081/5000000000 : ℝ)*x 1 + (1035520021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6952863/40000000 : ℝ)^5327 ≤ (5731106687559/50000000000000 : ℝ)^4303 := by
    have hnat : (6952863 : ℕ)^5327*50000000000000^4303 ≤ 5731106687559^4303*40000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6952863 40000000 5731106687559 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588800081/5000000000 : ℝ)^5327 ≤ (44268893609229/100000000000000 : ℝ)^4303 := by
    have hnat : (2588800081 : ℕ)^5327*100000000000000^4303 ≤ 44268893609229^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588800081 5000000000 44268893609229 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035520021/2000000000 : ℝ)^5327 ≤ (44268893005897/100000000000000 : ℝ)^4303 := by
    have hnat : (1035520021 : ℕ)^5327*100000000000000^4303 ≤ 44268893005897^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035520021 2000000000 44268893005897 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6952863/40000000 : ℝ), (2588800081/5000000000 : ℝ), (1035520021/2000000000 : ℝ)] ![(5731106687559/50000000000000 : ℝ), (44268893609229/100000000000000 : ℝ), (44268893005897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6952863/40000000 : ℝ)|^5327 ≤ (5731106687559/50000000000000 : ℝ)^4303
        have hw : |(-6952863/40000000 : ℝ)|=(6952863/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588800081/5000000000 : ℝ)|^5327 ≤ (44268893609229/100000000000000 : ℝ)^4303
        have hw : |(2588800081/5000000000 : ℝ)|=(2588800081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035520021/2000000000 : ℝ)|^5327 ≤ (44268893005897/100000000000000 : ℝ)^4303
        have hw : |(1035520021/2000000000 : ℝ)|=(1035520021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_5 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693286899/5000000000 : ℝ)*x 0 + (-365115213/2500000000 : ℝ)*x 1 + (1294400029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693286899/5000000000 : ℝ)^5327 ≤ (46491347592239/100000000000000 : ℝ)^4303 := by
    have hnat : (2693286899 : ℕ)^5327*100000000000000^4303 ≤ 46491347592239^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693286899 5000000000 46491347592239 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365115213/2500000000 : ℝ)^5327 ≤ (1847951853941/20000000000000 : ℝ)^4303 := by
    have hnat : (365115213 : ℕ)^5327*20000000000000^4303 ≤ 1847951853941^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365115213 2500000000 1847951853941 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294400029/2500000000 : ℝ)^5327 ≤ (44268893122329/100000000000000 : ℝ)^4303 := by
    have hnat : (1294400029 : ℕ)^5327*100000000000000^4303 ≤ 44268893122329^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294400029 2500000000 44268893122329 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693286899/5000000000 : ℝ), (-365115213/2500000000 : ℝ), (1294400029/2500000000 : ℝ)] ![(46491347592239/100000000000000 : ℝ), (1847951853941/20000000000000 : ℝ), (44268893122329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693286899/5000000000 : ℝ)|^5327 ≤ (46491347592239/100000000000000 : ℝ)^4303
        have hw : |(2693286899/5000000000 : ℝ)|=(2693286899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-365115213/2500000000 : ℝ)|^5327 ≤ (1847951853941/20000000000000 : ℝ)^4303
        have hw : |(-365115213/2500000000 : ℝ)|=(365115213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294400029/2500000000 : ℝ)|^5327 ≤ (44268893122329/100000000000000 : ℝ)^4303
        have hw : |(1294400029/2500000000 : ℝ)|=(1294400029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_6 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269328693/500000000 : ℝ)*x 0 + (2588800061/5000000000 : ℝ)*x 1 + (-1460460759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269328693/500000000 : ℝ)^5327 ≤ (2905709265919/6250000000000 : ℝ)^4303 := by
    have hnat : (269328693 : ℕ)^5327*6250000000000^4303 ≤ 2905709265919^4303*500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269328693 500000000 2905709265919 6250000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588800061/5000000000 : ℝ)^5327 ≤ (22134446592919/50000000000000 : ℝ)^4303 := by
    have hnat : (2588800061 : ℕ)^5327*50000000000000^4303 ≤ 22134446592919^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588800061 5000000000 22134446592919 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460460759/10000000000 : ℝ)^5327 ≤ (9239758541313/100000000000000 : ℝ)^4303 := by
    have hnat : (1460460759 : ℕ)^5327*100000000000000^4303 ≤ 9239758541313^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460460759 10000000000 9239758541313 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269328693/500000000 : ℝ), (2588800061/5000000000 : ℝ), (-1460460759/10000000000 : ℝ)] ![(2905709265919/6250000000000 : ℝ), (22134446592919/50000000000000 : ℝ), (9239758541313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269328693/500000000 : ℝ)|^5327 ≤ (2905709265919/6250000000000 : ℝ)^4303
        have hw : |(269328693/500000000 : ℝ)|=(269328693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588800061/5000000000 : ℝ)|^5327 ≤ (22134446592919/50000000000000 : ℝ)^4303
        have hw : |(2588800061/5000000000 : ℝ)|=(2588800061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1460460759/10000000000 : ℝ)|^5327 ≤ (9239758541313/100000000000000 : ℝ)^4303
        have hw : |(-1460460759/10000000000 : ℝ)|=(1460460759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_7 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (925882121/2500000000 : ℝ)*x 0 + (172808817/400000000 : ℝ)*x 1 + (2160110273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925882121/2500000000 : ℝ)^5327 ≤ (29238672575423/100000000000000 : ℝ)^4303 := by
    have hnat : (925882121 : ℕ)^5327*100000000000000^4303 ≤ 29238672575423^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925882121 2500000000 29238672575423 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172808817/400000000 : ℝ)^5327 ≤ (35380663088707/100000000000000 : ℝ)^4303 := by
    have hnat : (172808817 : ℕ)^5327*100000000000000^4303 ≤ 35380663088707^4303*400000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172808817 400000000 35380663088707 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160110273/5000000000 : ℝ)^5327 ≤ (35380664315459/100000000000000 : ℝ)^4303 := by
    have hnat : (2160110273 : ℕ)^5327*100000000000000^4303 ≤ 35380664315459^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160110273 5000000000 35380664315459 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(925882121/2500000000 : ℝ), (172808817/400000000 : ℝ), (2160110273/5000000000 : ℝ)] ![(29238672575423/100000000000000 : ℝ), (35380663088707/100000000000000 : ℝ), (35380664315459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(925882121/2500000000 : ℝ)|^5327 ≤ (29238672575423/100000000000000 : ℝ)^4303
        have hw : |(925882121/2500000000 : ℝ)|=(925882121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172808817/400000000 : ℝ)|^5327 ≤ (35380663088707/100000000000000 : ℝ)^4303
        have hw : |(172808817/400000000 : ℝ)|=(172808817/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160110273/5000000000 : ℝ)|^5327 ≤ (35380664315459/100000000000000 : ℝ)^4303
        have hw : |(2160110273/5000000000 : ℝ)|=(2160110273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_8 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-798839789/5000000000 : ℝ)*x 0 + (5001756141/10000000000 : ℝ)*x 1 + (5458264833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798839789/5000000000 : ℝ)^5327 ≤ (5163109492911/50000000000000 : ℝ)^4303 := by
    have hnat : (798839789 : ℕ)^5327*50000000000000^4303 ≤ 5163109492911^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798839789 5000000000 5163109492911 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001756141/10000000000 : ℝ)^5327 ≤ (42415212148011/100000000000000 : ℝ)^4303 := by
    have hnat : (5001756141 : ℕ)^5327*100000000000000^4303 ≤ 42415212148011^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001756141 10000000000 42415212148011 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458264833/10000000000 : ℝ)^5327 ≤ (47258568848913/100000000000000 : ℝ)^4303 := by
    have hnat : (5458264833 : ℕ)^5327*100000000000000^4303 ≤ 47258568848913^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458264833 10000000000 47258568848913 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798839789/5000000000 : ℝ), (5001756141/10000000000 : ℝ), (5458264833/10000000000 : ℝ)] ![(5163109492911/50000000000000 : ℝ), (42415212148011/100000000000000 : ℝ), (47258568848913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798839789/5000000000 : ℝ)|^5327 ≤ (5163109492911/50000000000000 : ℝ)^4303
        have hw : |(-798839789/5000000000 : ℝ)|=(798839789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001756141/10000000000 : ℝ)|^5327 ≤ (42415212148011/100000000000000 : ℝ)^4303
        have hw : |(5001756141/10000000000 : ℝ)|=(5001756141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458264833/10000000000 : ℝ)|^5327 ≤ (47258568848913/100000000000000 : ℝ)^4303
        have hw : |(5458264833/10000000000 : ℝ)|=(5458264833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_9 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259819489/500000000 : ℝ)*x 0 + (-667902259/5000000000 : ℝ)*x 1 + (5458264751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259819489/500000000 : ℝ)^5327 ≤ (44467863232681/100000000000000 : ℝ)^4303 := by
    have hnat : (259819489 : ℕ)^5327*100000000000000^4303 ≤ 44467863232681^4303*500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259819489 500000000 44467863232681 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667902259/5000000000 : ℝ)^5327 ≤ (8273568785819/100000000000000 : ℝ)^4303 := by
    have hnat : (667902259 : ℕ)^5327*100000000000000^4303 ≤ 8273568785819^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667902259 5000000000 8273568785819 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458264751/10000000000 : ℝ)^5327 ≤ (47258567969989/100000000000000 : ℝ)^4303 := by
    have hnat : (5458264751 : ℕ)^5327*100000000000000^4303 ≤ 47258567969989^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458264751 10000000000 47258567969989 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259819489/500000000 : ℝ), (-667902259/5000000000 : ℝ), (5458264751/10000000000 : ℝ)] ![(44467863232681/100000000000000 : ℝ), (8273568785819/100000000000000 : ℝ), (47258567969989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259819489/500000000 : ℝ)|^5327 ≤ (44467863232681/100000000000000 : ℝ)^4303
        have hw : |(259819489/500000000 : ℝ)|=(259819489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-667902259/5000000000 : ℝ)|^5327 ≤ (8273568785819/100000000000000 : ℝ)^4303
        have hw : |(-667902259/5000000000 : ℝ)|=(667902259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458264751/10000000000 : ℝ)|^5327 ≤ (47258567969989/100000000000000 : ℝ)^4303
        have hw : |(5458264751/10000000000 : ℝ)|=(5458264751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_10 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598194757/5000000000 : ℝ)*x 0 + (682283129/1250000000 : ℝ)*x 1 + (-1335804493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598194757/5000000000 : ℝ)^5327 ≤ (44467860414703/100000000000000 : ℝ)^4303 := by
    have hnat : (2598194757 : ℕ)^5327*100000000000000^4303 ≤ 44467860414703^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598194757 5000000000 44467860414703 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682283129/1250000000 : ℝ)^5327 ≤ (47258570981911/100000000000000 : ℝ)^4303 := by
    have hnat : (682283129 : ℕ)^5327*100000000000000^4303 ≤ 47258570981911^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682283129 1250000000 47258570981911 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1335804493/10000000000 : ℝ)^5327 ≤ (8273568594129/100000000000000 : ℝ)^4303 := by
    have hnat : (1335804493 : ℕ)^5327*100000000000000^4303 ≤ 8273568594129^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335804493 10000000000 8273568594129 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598194757/5000000000 : ℝ), (682283129/1250000000 : ℝ), (-1335804493/10000000000 : ℝ)] ![(44467860414703/100000000000000 : ℝ), (47258570981911/100000000000000 : ℝ), (8273568594129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598194757/5000000000 : ℝ)|^5327 ≤ (44467860414703/100000000000000 : ℝ)^4303
        have hw : |(2598194757/5000000000 : ℝ)|=(2598194757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682283129/1250000000 : ℝ)|^5327 ≤ (47258570981911/100000000000000 : ℝ)^4303
        have hw : |(682283129/1250000000 : ℝ)|=(682283129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1335804493/10000000000 : ℝ)|^5327 ≤ (8273568594129/100000000000000 : ℝ)^4303
        have hw : |(-1335804493/10000000000 : ℝ)|=(1335804493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_11 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4616895239/10000000000 : ℝ)*x 0 + (241364687/625000000 : ℝ)*x 1 + (965458711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4616895239/10000000000 : ℝ)^5327 ≤ (38412645421199/100000000000000 : ℝ)^4303 := by
    have hnat : (4616895239 : ℕ)^5327*100000000000000^4303 ≤ 38412645421199^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616895239 10000000000 38412645421199 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241364687/625000000 : ℝ)^5327 ≤ (15396839003379/50000000000000 : ℝ)^4303 := by
    have hnat : (241364687 : ℕ)^5327*50000000000000^4303 ≤ 15396839003379^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241364687 625000000 15396839003379 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965458711/2500000000 : ℝ)^5327 ≤ (3079367654579/10000000000000 : ℝ)^4303 := by
    have hnat : (965458711 : ℕ)^5327*10000000000000^4303 ≤ 3079367654579^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965458711 2500000000 3079367654579 10000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4616895239/10000000000 : ℝ), (241364687/625000000 : ℝ), (965458711/2500000000 : ℝ)] ![(38412645421199/100000000000000 : ℝ), (15396839003379/50000000000000 : ℝ), (3079367654579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4616895239/10000000000 : ℝ)|^5327 ≤ (38412645421199/100000000000000 : ℝ)^4303
        have hw : |(4616895239/10000000000 : ℝ)|=(4616895239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241364687/625000000 : ℝ)|^5327 ≤ (15396839003379/50000000000000 : ℝ)^4303
        have hw : |(241364687/625000000 : ℝ)|=(241364687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965458711/2500000000 : ℝ)|^5327 ≤ (3079367654579/10000000000000 : ℝ)^4303
        have hw : |(965458711/2500000000 : ℝ)|=(965458711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_12 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121999353/1000000000 : ℝ)*x 0 + (5583224547/10000000000 : ℝ)*x 1 + (5152509673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121999353/1000000000 : ℝ)^5327 ≤ (7394942888813/100000000000000 : ℝ)^4303 := by
    have hnat : (121999353 : ℕ)^5327*100000000000000^4303 ≤ 7394942888813^4303*1000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121999353 1000000000 7394942888813 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5583224547/10000000000 : ℝ)^5327 ≤ (48601587275003/100000000000000 : ℝ)^4303 := by
    have hnat : (5583224547 : ℕ)^5327*100000000000000^4303 ≤ 48601587275003^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583224547 10000000000 48601587275003 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152509673/10000000000 : ℝ)^5327 ≤ (4400346982489/10000000000000 : ℝ)^4303 := by
    have hnat : (5152509673 : ℕ)^5327*10000000000000^4303 ≤ 4400346982489^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152509673 10000000000 4400346982489 10000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121999353/1000000000 : ℝ), (5583224547/10000000000 : ℝ), (5152509673/10000000000 : ℝ)] ![(7394942888813/100000000000000 : ℝ), (48601587275003/100000000000000 : ℝ), (4400346982489/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121999353/1000000000 : ℝ)|^5327 ≤ (7394942888813/100000000000000 : ℝ)^4303
        have hw : |(-121999353/1000000000 : ℝ)|=(121999353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5583224547/10000000000 : ℝ)|^5327 ≤ (48601587275003/100000000000000 : ℝ)^4303
        have hw : |(5583224547/10000000000 : ℝ)|=(5583224547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152509673/10000000000 : ℝ)|^5327 ≤ (4400346982489/10000000000000 : ℝ)^4303
        have hw : |(5152509673/10000000000 : ℝ)|=(5152509673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_13 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216144343/400000000 : ℝ)*x 0 + (-735546149/5000000000 : ℝ)*x 1 + (2576254861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216144343/400000000 : ℝ)^5327 ≤ (23336715544009/50000000000000 : ℝ)^4303 := by
    have hnat : (216144343 : ℕ)^5327*50000000000000^4303 ≤ 23336715544009^4303*400000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216144343 400000000 23336715544009 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735546149/5000000000 : ℝ)^5327 ≤ (9323098548931/100000000000000 : ℝ)^4303 := by
    have hnat : (735546149 : ℕ)^5327*100000000000000^4303 ≤ 9323098548931^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735546149 5000000000 9323098548931 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576254861/5000000000 : ℝ)^5327 ≤ (1375108448217/3125000000000 : ℝ)^4303 := by
    have hnat : (2576254861 : ℕ)^5327*3125000000000^4303 ≤ 1375108448217^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576254861 5000000000 1375108448217 3125000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216144343/400000000 : ℝ), (-735546149/5000000000 : ℝ), (2576254861/5000000000 : ℝ)] ![(23336715544009/50000000000000 : ℝ), (9323098548931/100000000000000 : ℝ), (1375108448217/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216144343/400000000 : ℝ)|^5327 ≤ (23336715544009/50000000000000 : ℝ)^4303
        have hw : |(216144343/400000000 : ℝ)|=(216144343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735546149/5000000000 : ℝ)|^5327 ≤ (9323098548931/100000000000000 : ℝ)^4303
        have hw : |(-735546149/5000000000 : ℝ)|=(735546149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576254861/5000000000 : ℝ)|^5327 ≤ (1375108448217/3125000000000 : ℝ)^4303
        have hw : |(2576254861/5000000000 : ℝ)|=(2576254861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_14 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540360863/1000000000 : ℝ)*x 0 + (322031871/625000000 : ℝ)*x 1 + (-294218387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540360863/1000000000 : ℝ)^5327 ≤ (46673431676129/100000000000000 : ℝ)^4303 := by
    have hnat : (540360863 : ℕ)^5327*100000000000000^4303 ≤ 46673431676129^4303*1000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540360863 1000000000 46673431676129 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322031871/625000000 : ℝ)^5327 ≤ (11000868151367/25000000000000 : ℝ)^4303 := by
    have hnat : (322031871 : ℕ)^5327*25000000000000^4303 ≤ 11000868151367^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322031871 625000000 11000868151367 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294218387/2000000000 : ℝ)^5327 ≤ (4661547850471/50000000000000 : ℝ)^4303 := by
    have hnat : (294218387 : ℕ)^5327*50000000000000^4303 ≤ 4661547850471^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294218387 2000000000 4661547850471 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540360863/1000000000 : ℝ), (322031871/625000000 : ℝ), (-294218387/2000000000 : ℝ)] ![(46673431676129/100000000000000 : ℝ), (11000868151367/25000000000000 : ℝ), (4661547850471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540360863/1000000000 : ℝ)|^5327 ≤ (46673431676129/100000000000000 : ℝ)^4303
        have hw : |(540360863/1000000000 : ℝ)|=(540360863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322031871/625000000 : ℝ)|^5327 ≤ (11000868151367/25000000000000 : ℝ)^4303
        have hw : |(322031871/625000000 : ℝ)|=(322031871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294218387/2000000000 : ℝ)|^5327 ≤ (4661547850471/50000000000000 : ℝ)^4303
        have hw : |(-294218387/2000000000 : ℝ)|=(294218387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_box_15 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (361844833/1000000000 : ℝ)*x 0 + (272566937/625000000 : ℝ)*x 1 + (4361070951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361844833/1000000000 : ℝ)^5327 ≤ (710235548379/2500000000000 : ℝ)^4303 := by
    have hnat : (361844833 : ℕ)^5327*2500000000000^4303 ≤ 710235548379^4303*1000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361844833 1000000000 710235548379 2500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272566937/625000000 : ℝ)^5327 ≤ (4474411154233/12500000000000 : ℝ)^4303 := by
    have hnat : (272566937 : ℕ)^5327*12500000000000^4303 ≤ 4474411154233^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272566937 625000000 4474411154233 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4361070951/10000000000 : ℝ)^5327 ≤ (4474411102157/12500000000000 : ℝ)^4303 := by
    have hnat : (4361070951 : ℕ)^5327*12500000000000^4303 ≤ 4474411102157^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361070951 10000000000 4474411102157 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(361844833/1000000000 : ℝ), (272566937/625000000 : ℝ), (4361070951/10000000000 : ℝ)] ![(710235548379/2500000000000 : ℝ), (4474411154233/12500000000000 : ℝ), (4474411102157/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(361844833/1000000000 : ℝ)|^5327 ≤ (710235548379/2500000000000 : ℝ)^4303
        have hw : |(361844833/1000000000 : ℝ)|=(361844833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272566937/625000000 : ℝ)|^5327 ≤ (4474411154233/12500000000000 : ℝ)^4303
        have hw : |(272566937/625000000 : ℝ)|=(272566937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4361070951/10000000000 : ℝ)|^5327 ≤ (4474411102157/12500000000000 : ℝ)^4303
        have hw : |(4361070951/10000000000 : ℝ)|=(4361070951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1713_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2671/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58473/100000 : ℝ) ∧ (81579/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45233/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5017/50000 : ℝ) ^ (5319/1024 : ℝ) ≤ (650610422062967/100000000000000000000 : ℝ) := by
    have hpowers : (5017/50000 : ℝ)^5319 ≤ (650610422062967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5017 : ℕ)^5319*100000000000000000000^1024 ≤ 650610422062967^1024*50000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5017 50000 650610422062967 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5017/50000 : ℝ)) (X := (650610422062967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17071/100000 : ℝ) ^ (5319/1024 : ℝ) ≤ (10282415220662169/100000000000000000000 : ℝ) := by
    have hpowers : (17071/100000 : ℝ)^5319 ≤ (10282415220662169/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17071 : ℕ)^5319*100000000000000000000^1024 ≤ 10282415220662169^1024*100000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17071 100000 10282415220662169 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17071/100000 : ℝ)) (X := (10282415220662169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000650610422062967/50000000000000000000 : ℝ) ≤ (2500006262658133/2500000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50000650610422062967/50000000000000000000 : ℝ)^1024 ≤ (2500006262658133/2500000000000000 : ℝ)^5319 := by
      have hnat : (50000650610422062967 : ℕ)^1024*2500000000000000^5319 ≤ 2500006262658133^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000650610422062967 50000000000000000000 2500006262658133 2500000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500006262658133/2500000000000000 : ℝ)) (X := (50000650610422062967/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250683314102670321/6250000000000000000 : ℝ) ≤ (5000105235233241/5000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (6250683314102670321/6250000000000000000 : ℝ)^1024 ≤ (5000105235233241/5000000000000000 : ℝ)^5319 := by
      have hnat : (6250683314102670321 : ℕ)^1024*5000000000000000^5319 ≤ 5000105235233241^5319*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250683314102670321 6250000000000000000 5000105235233241 5000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105235233241/5000000000000000 : ℝ)) (X := (6250683314102670321/6250000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010282415220662169/50000000000000000000 : ℝ) ≤ (625024743143777/625000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50010282415220662169/50000000000000000000 : ℝ)^1024 ≤ (625024743143777/625000000000000 : ℝ)^5319 := by
      have hnat : (50010282415220662169 : ℕ)^1024*625000000000000^5319 ≤ 625024743143777^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010282415220662169 50000000000000000000 625024743143777 625000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625024743143777/625000000000000 : ℝ)) (X := (50010282415220662169/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(650610422062967/100000000000000000000 : ℝ) ≤ ((17591613819018354771/17592500000000000000 : ℝ)+2*(3708396679/14074000000000 : ℝ)*(5017/50000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (17591613819018354771/17592500000000000000 : ℝ)+2*(3708396679/14074000000000 : ℝ)*(5017/50000 : ℝ)=(2500006262658133/2500000000000000 : ℝ) by norm_num, show 1+2*(650610422062967/100000000000000000000 : ℝ)=(50000650610422062967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10282415220662169/100000000000000000000 : ℝ)+(650610422062967/100000000000000000000 : ℝ) ≤ ((17591613819018354771/17592500000000000000 : ℝ)+(3708396679/14074000000000 : ℝ)*((17071/100000 : ℝ)+(5017/50000 : ℝ)))^(5319/1024 : ℝ) := by
    rw [show (17591613819018354771/17592500000000000000 : ℝ)+(3708396679/14074000000000 : ℝ)*((17071/100000 : ℝ)+(5017/50000 : ℝ))=(5000105235233241/5000000000000000 : ℝ) by norm_num, show 1+(10282415220662169/100000000000000000000 : ℝ)+(650610422062967/100000000000000000000 : ℝ)=(6250683314102670321/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10282415220662169/100000000000000000000 : ℝ) ≤ ((17591613819018354771/17592500000000000000 : ℝ)+2*(3708396679/14074000000000 : ℝ)*(17071/100000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (17591613819018354771/17592500000000000000 : ℝ)+2*(3708396679/14074000000000 : ℝ)*(17071/100000 : ℝ)=(625024743143777/625000000000000 : ℝ) by norm_num, show 1+2*(10282415220662169/100000000000000000000 : ℝ)=(50010282415220662169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17591613819018354771/17592500000000000000 : ℝ)*(X 1 0+X 2 0)+(3708396679/14074000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (17071/100000 : ℝ)) (c := (17591613819018354771/17592500000000000000 : ℝ)) (alpha := (3708396679/14074000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17591613819018354771/17592500000000000000 : ℝ)*(X 0 1+X 2 1)+(3708396679/14074000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (17071/100000 : ℝ)) (c := (17591613819018354771/17592500000000000000 : ℝ)) (alpha := (3708396679/14074000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17591613819018354771/17592500000000000000 : ℝ)*(X 0 2+X 1 2)+(3708396679/14074000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (17071/100000 : ℝ)) (c := (17591613819018354771/17592500000000000000 : ℝ)) (alpha := (3708396679/14074000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1084996361/10000000000 : ℝ)*X 0 0+(5415644839/10000000000 : ℝ)*X 0 1+(5415644617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612626361/5000000000 : ℝ)*X 1 0+(-677694449/5000000000 : ℝ)*X 1 1+(2707822417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612626479/5000000000 : ℝ)*X 2 0+(1083128919/2000000000 : ℝ)*X 2 1+(-677694453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482419511/10000000000 : ℝ)*X 0 0+(3931597537/10000000000 : ℝ)*X 0 1+(3931597587/10000000000 : ℝ)*X 0 2+(4482419511/10000000000 : ℝ)*X 1 0+(3931597537/10000000000 : ℝ)*X 1 1+(3931597587/10000000000 : ℝ)*X 1 2+(4482419511/10000000000 : ℝ)*X 2 0+(3931597537/10000000000 : ℝ)*X 2 1+(3931597587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6952863/40000000 : ℝ)*X 0 0+(2588800081/5000000000 : ℝ)*X 0 1+(1035520021/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2693286899/5000000000 : ℝ)*X 1 0+(-365115213/2500000000 : ℝ)*X 1 1+(1294400029/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((269328693/500000000 : ℝ)*X 2 0+(2588800061/5000000000 : ℝ)*X 2 1+(-1460460759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((925882121/2500000000 : ℝ)*X 0 0+(172808817/400000000 : ℝ)*X 0 1+(2160110273/5000000000 : ℝ)*X 0 2+(925882121/2500000000 : ℝ)*X 1 0+(172808817/400000000 : ℝ)*X 1 1+(2160110273/5000000000 : ℝ)*X 1 2+(925882121/2500000000 : ℝ)*X 2 0+(172808817/400000000 : ℝ)*X 2 1+(2160110273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-798839789/5000000000 : ℝ)*X 0 0+(5001756141/10000000000 : ℝ)*X 0 1+(5458264833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((259819489/500000000 : ℝ)*X 1 0+(-667902259/5000000000 : ℝ)*X 1 1+(5458264751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598194757/5000000000 : ℝ)*X 2 0+(682283129/1250000000 : ℝ)*X 2 1+(-1335804493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4616895239/10000000000 : ℝ)*X 0 0+(241364687/625000000 : ℝ)*X 0 1+(965458711/2500000000 : ℝ)*X 0 2+(4616895239/10000000000 : ℝ)*X 1 0+(241364687/625000000 : ℝ)*X 1 1+(965458711/2500000000 : ℝ)*X 1 2+(4616895239/10000000000 : ℝ)*X 2 0+(241364687/625000000 : ℝ)*X 2 1+(965458711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-121999353/1000000000 : ℝ)*X 0 0+(5583224547/10000000000 : ℝ)*X 0 1+(5152509673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((216144343/400000000 : ℝ)*X 1 0+(-735546149/5000000000 : ℝ)*X 1 1+(2576254861/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540360863/1000000000 : ℝ)*X 2 0+(322031871/625000000 : ℝ)*X 2 1+(-294218387/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((361844833/1000000000 : ℝ)*X 0 0+(272566937/625000000 : ℝ)*X 0 1+(4361070951/10000000000 : ℝ)*X 0 2+(361844833/1000000000 : ℝ)*X 1 0+(272566937/625000000 : ℝ)*X 1 1+(4361070951/10000000000 : ℝ)*X 1 2+(361844833/1000000000 : ℝ)*X 2 0+(272566937/625000000 : ℝ)*X 2 1+(4361070951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2671/4000 : ℝ) ≤ (-58734637516547183443349443056747/87962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (203499/1000000000000 : ℝ)*(upper0) + (728027/3125000000000 : ℝ)*(lower2) + (143261/25000000000000 : ℝ)*(lower3) + (136423941392881/10000000000000 : ℝ)*(major0) + (136423941392881/10000000000000 : ℝ)*(major1) + (136423941392881/10000000000000 : ℝ)*(major2) + (42535673/100000000000000 : ℝ)*(sp1) + (109974393/100000000000000 : ℝ)*(sp3) + (2054532420504743/100000000000000 : ℝ)*(sp4) + (1027266257492771/50000000000000 : ℝ)*(sp5) + (513631690494833/25000000000000 : ℝ)*(sp6) + (696203613828559/100000000000000 : ℝ)*(sp7) + (137016473/100000000000000 : ℝ)*(sp8) + (1448885471/25000000000000 : ℝ)*(sp14) + (87025465475369/12500000000000 : ℝ)*(f.failure) + (32102071211269/1562500000000 : ℝ)*(f.sum) + (3064300051459/1407400000000000000000000000 : ℝ)*base66 + (658093534298839749/175925000000000000000000000000000 : ℝ)*base68 + (655927590383789749/175925000000000000000000000000000 : ℝ)*base70 + (562743258784610251/175925000000000000000000000000000 : ℝ)*base71 + (106747871393/3518500000000000000000000000 : ℝ)*base74 + (379691139795960251/175925000000000000000000000000000 : ℝ)*base75 + (758267013882039749/175925000000000000000000000000000 : ℝ)*base78 + (906914618327664749/175925000000000000000000000000000 : ℝ)*base80 + (20193826078951/7037000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2220557/1250000000000000000000 : ℝ)*base89 + (2220557/1250000000000000000000 : ℝ)*base91 + (2220557/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58473/100000 : ℝ) ≤ (3318472603409265287067302690517/5675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4378209/25000000000000 : ℝ)*(upper0) + (9701/1250000000000 : ℝ)*(upper3) + (14306701/50000000000000 : ℝ)*(upper4) + (293984083711821/20000000000000 : ℝ)*(major0) + (293984083711821/20000000000000 : ℝ)*(major1) + (293984083711821/20000000000000 : ℝ)*(major2) + (434042553511041/20000000000000 : ℝ)*(sp0) + (542553017988959/25000000000000 : ℝ)*(sp1) + (271276684139283/12500000000000 : ℝ)*(sp2) + (750134945113219/100000000000000 : ℝ)*(sp3) + (877954701/50000000000000 : ℝ)*(sp5) + (177375487/50000000000000 : ℝ)*(sp6) + (37677227/12500000000000 : ℝ)*(sp7) + (1060310033/100000000000000 : ℝ)*(sp8) + (150027049306207/20000000000000 : ℝ)*(f.failure) + (1085106913932619/50000000000000 : ℝ)*(f.sum) + (17126723539/7093750000000000000000000 : ℝ)*base66 + (56533508496253161/11350000000000000000000000000000 : ℝ)*base67 + (19951686560053161/11350000000000000000000000000000 : ℝ)*base69 + (30234837460246839/11350000000000000000000000000000 : ℝ)*base72 + (159793862633/227000000000000000000000000 : ℝ)*base73 + (24710845049353161/11350000000000000000000000000000 : ℝ)*base75 + (10646748378353161/11350000000000000000000000000000 : ℝ)*base77 + (129419469154746839/11350000000000000000000000000000 : ℝ)*base80 + (482087560603/227000000000000000000000000 : ℝ)*base82 + (293029/2000000000000000000000 : ℝ)*base90 + (293029/2000000000000000000000 : ℝ)*base92 + (293029/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81579/100000 : ℝ) ≤ (35880348583432235226546070441197/43981250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1990899/12500000000000 : ℝ)*(upper0) + (41212901/100000000000000 : ℝ)*(upper1) + (3106177/6250000000000 : ℝ)*(upper2) + (10098183/50000000000000 : ℝ)*(upper4) + (74436744494769/5000000000000 : ℝ)*(major0) + (74436744494769/5000000000000 : ℝ)*(major1) + (74436744494769/5000000000000 : ℝ)*(major2) + (2122950033/25000000000000 : ℝ)*(sp1) + (9228925477/50000000000000 : ℝ)*(sp2) + (4611019/1000000000000 : ℝ)*(sp4) + (273817366350769/12500000000000 : ℝ)*(sp8) + (2190530900107921/100000000000000 : ℝ)*(sp9) + (2190520934057099/100000000000000 : ℝ)*(sp10) + (379868358705339/50000000000000 : ℝ)*(sp11) + (379868358705339/50000000000000 : ℝ)*(f.failure) + (2190539391908053/100000000000000 : ℝ)*(f.sum) + (28151519410159/3518500000000000000000000000 : ℝ)*base65 + (200412333476757101/87962500000000000000000000000000 : ℝ)*base68 + (309410880173492899/87962500000000000000000000000000 : ℝ)*base69 + (32169707126332101/87962500000000000000000000000000 : ℝ)*base72 + (18215803973303/3518500000000000000000000000 : ℝ)*base73 + (381900361961394601/87962500000000000000000000000000 : ℝ)*base76 + (457071108899192899/87962500000000000000000000000000 : ℝ)*base77 + (88143029713532101/87962500000000000000000000000000 : ℝ)*base80 + (441018245463/7037000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9788967/5000000000000000000000 : ℝ)*base89 + (9788967/5000000000000000000000 : ℝ)*base91 + (9788967/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-45233/50000 : ℝ) ≤ (-99467008573562178634009224263379/109953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29307427/100000000000000 : ℝ)*(lower1) + (75190721/100000000000000 : ℝ)*(lower2) + (12795387/100000000000000 : ℝ)*(upper5) + (192287541017867/12500000000000 : ℝ)*(major0) + (192287541017867/12500000000000 : ℝ)*(major1) + (192287541017867/12500000000000 : ℝ)*(major2) + (2638656623/100000000000000 : ℝ)*(sp0) + (36643414417/100000000000000 : ℝ)*(sp5) + (693835273/10000000000000 : ℝ)*(sp7) + (149679059/100000000000000 : ℝ)*(sp8) + (2321721099654479/100000000000000 : ℝ)*(sp12) + (2267272699781/97656250000 : ℝ)*(sp13) + (1160861943995081/50000000000000 : ℝ)*(sp14) + (157004839513021/20000000000000 : ℝ)*(sp15) + (157006227183567/20000000000000 : ℝ)*(f.failure) + (1160861943995081/50000000000000 : ℝ)*(f.sum) + (354278849757/281480000000000000000000000 : ℝ)*base65 + (1687410081929400293/219906250000000000000000000000000 : ℝ)*base68 + (921227610560068457/219906250000000000000000000000000 : ℝ)*base69 + (244149111447806543/219906250000000000000000000000000 : ℝ)*base72 + (13165641047439/3518500000000000000000000000 : ℝ)*base74 + (1277959609575849707/219906250000000000000000000000000 : ℝ)*base75 + (762082755675244043/219906250000000000000000000000000 : ℝ)*base78 + (726086304251619043/219906250000000000000000000000000 : ℝ)*base80 + (813865619547/1407400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8647051/2000000000000000000000 : ℝ)*base89 + (8647051/2000000000000000000000 : ℝ)*base91 + (8647051/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1713_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2671/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (81579/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45233/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1713_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1713_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2671/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (81579/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45233/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1713_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1713_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2671/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (81579/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45233/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1713_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

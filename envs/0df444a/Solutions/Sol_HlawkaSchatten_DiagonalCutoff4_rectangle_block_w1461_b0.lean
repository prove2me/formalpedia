-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1461_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:30.317262+00:00
-- url     : https://prove2.me/submissions/057a04a7-a65e-488a-bba9-0e152040e25e

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
theorem support_rectangle_w1461_s0_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740838559/10000000000 : ℝ)*x 0 + (5947086427/10000000000 : ℝ)*x 1 + (2419249343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740838559/10000000000 : ℝ)^4421 ≤ (642348770097/6250000000000 : ℝ)^3397 := by
    have hnat : (1740838559 : ℕ)^4421*6250000000000^3397 ≤ 642348770097^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740838559 10000000000 642348770097 6250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5947086427/10000000000 : ℝ)^4421 ≤ (12711885693933/25000000000000 : ℝ)^3397 := by
    have hnat : (5947086427 : ℕ)^4421*25000000000000^3397 ≤ 12711885693933^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947086427 10000000000 12711885693933 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419249343/5000000000 : ℝ)^4421 ≤ (19437438447953/50000000000000 : ℝ)^3397 := by
    have hnat : (2419249343 : ℕ)^4421*50000000000000^3397 ≤ 19437438447953^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419249343 5000000000 19437438447953 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740838559/10000000000 : ℝ), (5947086427/10000000000 : ℝ), (2419249343/5000000000 : ℝ)] ![(642348770097/6250000000000 : ℝ), (12711885693933/25000000000000 : ℝ), (19437438447953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740838559/10000000000 : ℝ)|^4421 ≤ (642348770097/6250000000000 : ℝ)^3397
        have hw : |(-1740838559/10000000000 : ℝ)|=(1740838559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5947086427/10000000000 : ℝ)|^4421 ≤ (12711885693933/25000000000000 : ℝ)^3397
        have hw : |(5947086427/10000000000 : ℝ)|=(5947086427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419249343/5000000000 : ℝ)|^4421 ≤ (19437438447953/50000000000000 : ℝ)^3397
        have hw : |(2419249343/5000000000 : ℝ)|=(2419249343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744273097/5000000000 : ℝ)*x 0 + (-2365701423/10000000000 : ℝ)*x 1 + (241924933/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744273097/5000000000 : ℝ)^4421 ≤ (22902806594799/50000000000000 : ℝ)^3397 := by
    have hnat : (2744273097 : ℕ)^4421*50000000000000^3397 ≤ 22902806594799^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744273097 5000000000 22902806594799 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2365701423/10000000000 : ℝ)^4421 ≤ (7659755087807/50000000000000 : ℝ)^3397 := by
    have hnat : (2365701423 : ℕ)^4421*50000000000000^3397 ≤ 7659755087807^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365701423 10000000000 7659755087807 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241924933/500000000 : ℝ)^4421 ≤ (19437438312019/50000000000000 : ℝ)^3397 := by
    have hnat : (241924933 : ℕ)^4421*50000000000000^3397 ≤ 19437438312019^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241924933 500000000 19437438312019 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744273097/5000000000 : ℝ), (-2365701423/10000000000 : ℝ), (241924933/500000000 : ℝ)] ![(22902806594799/50000000000000 : ℝ), (7659755087807/50000000000000 : ℝ), (19437438312019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744273097/5000000000 : ℝ)|^4421 ≤ (22902806594799/50000000000000 : ℝ)^3397
        have hw : |(2744273097/5000000000 : ℝ)|=(2744273097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2365701423/10000000000 : ℝ)|^4421 ≤ (7659755087807/50000000000000 : ℝ)^3397
        have hw : |(-2365701423/10000000000 : ℝ)|=(2365701423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241924933/500000000 : ℝ)|^4421 ≤ (19437438312019/50000000000000 : ℝ)^3397
        have hw : |(241924933/500000000 : ℝ)|=(241924933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744273231/5000000000 : ℝ)*x 0 + (241924933/500000000 : ℝ)*x 1 + (-2365701077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744273231/5000000000 : ℝ)^4421 ≤ (45805616100457/100000000000000 : ℝ)^3397 := by
    have hnat : (2744273231 : ℕ)^4421*100000000000000^3397 ≤ 45805616100457^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744273231 5000000000 45805616100457 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241924933/500000000 : ℝ)^4421 ≤ (19437438312019/50000000000000 : ℝ)^3397 := by
    have hnat : (241924933 : ℕ)^4421*50000000000000^3397 ≤ 19437438312019^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241924933 500000000 19437438312019 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365701077/10000000000 : ℝ)^4421 ≤ (1914938407453/12500000000000 : ℝ)^3397 := by
    have hnat : (2365701077 : ℕ)^4421*12500000000000^3397 ≤ 1914938407453^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365701077 10000000000 1914938407453 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744273231/5000000000 : ℝ), (241924933/500000000 : ℝ), (-2365701077/10000000000 : ℝ)] ![(45805616100457/100000000000000 : ℝ), (19437438312019/50000000000000 : ℝ), (1914938407453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744273231/5000000000 : ℝ)|^4421 ≤ (45805616100457/100000000000000 : ℝ)^3397
        have hw : |(2744273231/5000000000 : ℝ)|=(2744273231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241924933/500000000 : ℝ)|^4421 ≤ (19437438312019/50000000000000 : ℝ)^3397
        have hw : |(241924933/500000000 : ℝ)|=(241924933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2365701077/10000000000 : ℝ)|^4421 ≤ (1914938407453/12500000000000 : ℝ)^3397
        have hw : |(-2365701077/10000000000 : ℝ)|=(2365701077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166457779/400000000 : ℝ)*x 0 + (3102703927/10000000000 : ℝ)*x 1 + (172784297/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166457779/400000000 : ℝ)^4421 ≤ (3993724730519/12500000000000 : ℝ)^3397 := by
    have hnat : (166457779 : ℕ)^4421*12500000000000^3397 ≤ 3993724730519^3397*400000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166457779 400000000 3993724730519 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102703927/10000000000 : ℝ)^4421 ≤ (136272842389/625000000000 : ℝ)^3397 := by
    have hnat : (3102703927 : ℕ)^4421*625000000000^3397 ≤ 136272842389^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102703927 10000000000 136272842389 625000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172784297/312500000 : ℝ)^4421 ≤ (11561636840721/25000000000000 : ℝ)^3397 := by
    have hnat : (172784297 : ℕ)^4421*25000000000000^3397 ≤ 11561636840721^3397*312500000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172784297 312500000 11561636840721 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166457779/400000000 : ℝ), (3102703927/10000000000 : ℝ), (172784297/312500000 : ℝ)] ![(3993724730519/12500000000000 : ℝ), (136272842389/625000000000 : ℝ), (11561636840721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166457779/400000000 : ℝ)|^4421 ≤ (3993724730519/12500000000000 : ℝ)^3397
        have hw : |(166457779/400000000 : ℝ)|=(166457779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102703927/10000000000 : ℝ)|^4421 ≤ (136272842389/625000000000 : ℝ)^3397
        have hw : |(3102703927/10000000000 : ℝ)|=(3102703927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172784297/312500000 : ℝ)|^4421 ≤ (11561636840721/25000000000000 : ℝ)^3397
        have hw : |(172784297/312500000 : ℝ)|=(172784297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8723521/50000000 : ℝ)*x 0 + (4866790549/10000000000 : ℝ)*x 1 + (739723129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8723521/50000000 : ℝ)^4421 ≤ (10307291790343/100000000000000 : ℝ)^3397 := by
    have hnat : (8723521 : ℕ)^4421*100000000000000^3397 ≤ 10307291790343^3397*50000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8723521 50000000 10307291790343 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866790549/10000000000 : ℝ)^4421 ≤ (19585484549339/50000000000000 : ℝ)^3397 := by
    have hnat : (4866790549 : ℕ)^4421*50000000000000^3397 ≤ 19585484549339^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866790549 10000000000 19585484549339 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739723129/1250000000 : ℝ)^4421 ≤ (25260869548083/50000000000000 : ℝ)^3397 := by
    have hnat : (739723129 : ℕ)^4421*50000000000000^3397 ≤ 25260869548083^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739723129 1250000000 25260869548083 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8723521/50000000 : ℝ), (4866790549/10000000000 : ℝ), (739723129/1250000000 : ℝ)] ![(10307291790343/100000000000000 : ℝ), (19585484549339/50000000000000 : ℝ), (25260869548083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8723521/50000000 : ℝ)|^4421 ≤ (10307291790343/100000000000000 : ℝ)^3397
        have hw : |(-8723521/50000000 : ℝ)|=(8723521/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866790549/10000000000 : ℝ)|^4421 ≤ (19585484549339/50000000000000 : ℝ)^3397
        have hw : |(4866790549/10000000000 : ℝ)|=(4866790549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739723129/1250000000 : ℝ)|^4421 ≤ (25260869548083/50000000000000 : ℝ)^3397
        have hw : |(739723129/1250000000 : ℝ)|=(739723129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_5 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185834671/10000000000 : ℝ)*x 0 + (-643207347/5000000000 : ℝ)*x 1 + (369861569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185834671/10000000000 : ℝ)^4421 ≤ (10636357257471/25000000000000 : ℝ)^3397 := by
    have hnat : (5185834671 : ℕ)^4421*25000000000000^3397 ≤ 10636357257471^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185834671 10000000000 10636357257471 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643207347/5000000000 : ℝ)^4421 ≤ (6932831055113/100000000000000 : ℝ)^3397 := by
    have hnat : (643207347 : ℕ)^4421*100000000000000^3397 ≤ 6932831055113^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643207347 5000000000 6932831055113 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369861569/625000000 : ℝ)^4421 ≤ (50521739896141/100000000000000 : ℝ)^3397 := by
    have hnat : (369861569 : ℕ)^4421*100000000000000^3397 ≤ 50521739896141^3397*625000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369861569 625000000 50521739896141 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185834671/10000000000 : ℝ), (-643207347/5000000000 : ℝ), (369861569/625000000 : ℝ)] ![(10636357257471/25000000000000 : ℝ), (6932831055113/100000000000000 : ℝ), (50521739896141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185834671/10000000000 : ℝ)|^4421 ≤ (10636357257471/25000000000000 : ℝ)^3397
        have hw : |(5185834671/10000000000 : ℝ)|=(5185834671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-643207347/5000000000 : ℝ)|^4421 ≤ (6932831055113/100000000000000 : ℝ)^3397
        have hw : |(-643207347/5000000000 : ℝ)|=(643207347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369861569/625000000 : ℝ)|^4421 ≤ (50521739896141/100000000000000 : ℝ)^3397
        have hw : |(369861569/625000000 : ℝ)|=(369861569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_6 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296458677/2500000000 : ℝ)*x 0 + (2958892471/5000000000 : ℝ)*x 1 + (-80400931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296458677/2500000000 : ℝ)^4421 ≤ (21272714712471/50000000000000 : ℝ)^3397 := by
    have hnat : (1296458677 : ℕ)^4421*50000000000000^3397 ≤ 21272714712471^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296458677 2500000000 21272714712471 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2958892471/5000000000 : ℝ)^4421 ≤ (50521738096197/100000000000000 : ℝ)^3397 := by
    have hnat : (2958892471 : ℕ)^4421*100000000000000^3397 ≤ 50521738096197^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958892471 5000000000 50521738096197 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80400931/625000000 : ℝ)^4421 ≤ (1386566494381/20000000000000 : ℝ)^3397 := by
    have hnat : (80400931 : ℕ)^4421*20000000000000^3397 ≤ 1386566494381^3397*625000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80400931 625000000 1386566494381 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296458677/2500000000 : ℝ), (2958892471/5000000000 : ℝ), (-80400931/625000000 : ℝ)] ![(21272714712471/50000000000000 : ℝ), (50521738096197/100000000000000 : ℝ), (1386566494381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296458677/2500000000 : ℝ)|^4421 ≤ (21272714712471/50000000000000 : ℝ)^3397
        have hw : |(1296458677/2500000000 : ℝ)|=(1296458677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2958892471/5000000000 : ℝ)|^4421 ≤ (50521738096197/100000000000000 : ℝ)^3397
        have hw : |(2958892471/5000000000 : ℝ)|=(2958892471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80400931/625000000 : ℝ)|^4421 ≤ (1386566494381/20000000000000 : ℝ)^3397
        have hw : |(-80400931/625000000 : ℝ)|=(80400931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s0_7 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169906349/10000000000 : ℝ)*x 0 + (5467173641/10000000000 : ℝ)*x 1 + (1583418571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169906349/10000000000 : ℝ)^4421 ≤ (32034374118491/100000000000000 : ℝ)^3397 := by
    have hnat : (4169906349 : ℕ)^4421*100000000000000^3397 ≤ 32034374118491^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169906349 10000000000 32034374118491 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467173641/10000000000 : ℝ)^4421 ≤ (45573613422501/100000000000000 : ℝ)^3397 := by
    have hnat : (5467173641 : ℕ)^4421*100000000000000^3397 ≤ 45573613422501^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467173641 10000000000 45573613422501 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583418571/5000000000 : ℝ)^4421 ≤ (22392012444791/100000000000000 : ℝ)^3397 := by
    have hnat : (1583418571 : ℕ)^4421*100000000000000^3397 ≤ 22392012444791^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583418571 5000000000 22392012444791 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169906349/10000000000 : ℝ), (5467173641/10000000000 : ℝ), (1583418571/5000000000 : ℝ)] ![(32034374118491/100000000000000 : ℝ), (45573613422501/100000000000000 : ℝ), (22392012444791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169906349/10000000000 : ℝ)|^4421 ≤ (32034374118491/100000000000000 : ℝ)^3397
        have hw : |(4169906349/10000000000 : ℝ)|=(4169906349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467173641/10000000000 : ℝ)|^4421 ≤ (45573613422501/100000000000000 : ℝ)^3397
        have hw : |(5467173641/10000000000 : ℝ)|=(5467173641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583418571/5000000000 : ℝ)|^4421 ≤ (22392012444791/100000000000000 : ℝ)^3397
        have hw : |(1583418571/5000000000 : ℝ)|=(1583418571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26039/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1105/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1105 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1105*1^256 ≤ 0^256*1^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1105/256 : ℝ) ≤ (383141552877419731/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1105 ≤ (383141552877419731/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1105*20000000000000000000^256 ≤ 383141552877419731^256*5^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 383141552877419731 20000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (383141552877419731/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1105 := by
      have hnat : (1 : ℕ)^256*1^1105 ≤ 1^1105*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20383141552877419731/20000000000000000000 : ℝ) ≤ (5022029510669629/5000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (20383141552877419731/20000000000000000000 : ℝ)^256 ≤ (5022029510669629/5000000000000000 : ℝ)^1105 := by
      have hnat : (20383141552877419731 : ℕ)^256*5000000000000000^1105 ≤ 5022029510669629^1105*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20383141552877419731 20000000000000000000 5022029510669629 5000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022029510669629/5000000000000000 : ℝ)) (X := (20383141552877419731/20000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10383141552877419731/10000000000000000000 : ℝ) ≤ (2522029510669629/2500000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (10383141552877419731/10000000000000000000 : ℝ)^256 ≤ (2522029510669629/2500000000000000 : ℝ)^1105 := by
      have hnat : (10383141552877419731 : ℕ)^256*2500000000000000^1105 ≤ 2522029510669629^1105*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10383141552877419731 10000000000000000000 2522029510669629 2500000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522029510669629/2500000000000000 : ℝ)) (X := (10383141552877419731/10000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22029510669629/2000000000000000 : ℝ)*(0 : ℝ))^(1105/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(22029510669629/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(383141552877419731/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22029510669629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (1 : ℝ)+(22029510669629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5022029510669629/5000000000000000 : ℝ) by norm_num, show 1+(383141552877419731/20000000000000000000 : ℝ)+(0 : ℝ)=(20383141552877419731/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(383141552877419731/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22029510669629/2000000000000000 : ℝ)*(2/5 : ℝ))^(1105/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(22029510669629/2000000000000000 : ℝ)*(2/5 : ℝ)=(2522029510669629/2500000000000000 : ℝ) by norm_num, show 1+2*(383141552877419731/20000000000000000000 : ℝ)=(10383141552877419731/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22029510669629/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22029510669629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22029510669629/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22029510669629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22029510669629/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22029510669629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1740838559/10000000000 : ℝ)*X 0 0+(5947086427/10000000000 : ℝ)*X 0 1+(2419249343/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2744273097/5000000000 : ℝ)*X 1 0+(-2365701423/10000000000 : ℝ)*X 1 1+(241924933/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744273231/5000000000 : ℝ)*X 2 0+(241924933/500000000 : ℝ)*X 2 1+(-2365701077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((166457779/400000000 : ℝ)*X 0 0+(3102703927/10000000000 : ℝ)*X 0 1+(172784297/312500000 : ℝ)*X 0 2+(166457779/400000000 : ℝ)*X 1 0+(3102703927/10000000000 : ℝ)*X 1 1+(172784297/312500000 : ℝ)*X 1 2+(166457779/400000000 : ℝ)*X 2 0+(3102703927/10000000000 : ℝ)*X 2 1+(172784297/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8723521/50000000 : ℝ)*X 0 0+(4866790549/10000000000 : ℝ)*X 0 1+(739723129/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185834671/10000000000 : ℝ)*X 1 0+(-643207347/5000000000 : ℝ)*X 1 1+(369861569/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296458677/2500000000 : ℝ)*X 2 0+(2958892471/5000000000 : ℝ)*X 2 1+(-80400931/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169906349/10000000000 : ℝ)*X 0 0+(5467173641/10000000000 : ℝ)*X 0 1+(1583418571/5000000000 : ℝ)*X 0 2+(4169906349/10000000000 : ℝ)*X 1 0+(5467173641/10000000000 : ℝ)*X 1 1+(1583418571/5000000000 : ℝ)*X 1 2+(4169906349/10000000000 : ℝ)*X 2 0+(5467173641/10000000000 : ℝ)*X 2 1+(1583418571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (559939985347670004346089/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658871/10000000000000 : ℝ)*(base1) + (250614129/20000000000000 : ℝ)*(base19) + (259423421/20000000000000 : ℝ)*(base23) + (26245217/25000000000000 : ℝ)*(upper3) + (21225721/10000000000000 : ℝ)*(upper5) + (657098089357749/100000000000000 : ℝ)*(major0) + (657098089357749/100000000000000 : ℝ)*(major1) + (657098089357749/100000000000000 : ℝ)*(major2) + (451026243793689/50000000000000 : ℝ)*(sp0) + (90205614173643/10000000000000 : ℝ)*(sp1) + (90205609768997/10000000000000 : ℝ)*(sp2) + (412136518247737/100000000000000 : ℝ)*(sp3) + (615476051/12500000000000 : ℝ)*(sp4) + (2062425311/100000000000000 : ℝ)*(sp7) + (206069298630879/50000000000000 : ℝ)*(f.failure) + (36082295792283/4000000000000 : ℝ)*(f.sum) + (94356541094879/100000000000000000000000000000 : ℝ)*base66 + (1118477459494879/200000000000000000000000000000 : ℝ)*base68 + (165825264694879/200000000000000000000000000000 : ℝ)*base70 + (223298476694879/200000000000000000000000000000 : ℝ)*base72 + (182073535894879/100000000000000000000000000000 : ℝ)*base74 + (79195151894879/200000000000000000000000000000 : ℝ)*base76 + (981046220694879/200000000000000000000000000000 : ℝ)*base78 + (457725380105121/200000000000000000000000000000 : ℝ)*base79 + (228156338105121/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10003647/5000000000000000000000 : ℝ)*base89 + (10003647/5000000000000000000000 : ℝ)*base91 + (10003647/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28649672747820838251519/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1310912737/100000000000000 : ℝ)*(base19) + (33081949/2500000000000 : ℝ)*(base23) + (33175113/25000000000000 : ℝ)*(base32) + (199030337/100000000000000 : ℝ)*(upper3) + (14750383/12500000000000 : ℝ)*(upper5) + (34654954787379/5000000000000 : ℝ)*(major0) + (34654954787379/5000000000000 : ℝ)*(major1) + (34654954787379/5000000000000 : ℝ)*(major2) + (794420853/25000000000000 : ℝ)*(sp1) + (204575949/6250000000000 : ℝ)*(sp2) + (237869801571261/25000000000000 : ℝ)*(sp4) + (14866792463889/1562500000000 : ℝ)*(sp5) + (9514746097919/1000000000000 : ℝ)*(sp6) + (434718661511839/100000000000000 : ℝ)*(sp7) + (43471879421229/10000000000000 : ℝ)*(f.failure) + (237869801571261/25000000000000 : ℝ)*(f.sum) + (7330297242609/5000000000000000000000000000 : ℝ)*base66 + (53021241737609/10000000000000000000000000000 : ℝ)*base68 + (23007752352391/10000000000000000000000000000 : ℝ)*base69 + (22954521737609/10000000000000000000000000000 : ℝ)*base72 + (24942905682609/5000000000000000000000000000 : ℝ)*base74 + (89117964607609/10000000000000000000000000000 : ℝ)*base76 + (9425492377609/10000000000000000000000000000 : ℝ)*base78 + (50120982577609/10000000000000000000000000000 : ℝ)*base80 + (6492464962391/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4858803/1000000000000000000000 : ℝ)*base90 + (4858803/1000000000000000000000 : ℝ)*base92 + (4858803/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1461_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1461_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1461_s1_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908678929/10000000000 : ℝ)*x 0 + (559267113/1000000000 : ℝ)*x 1 + (158914343/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908678929/10000000000 : ℝ)^4421 ≤ (724094508601/6250000000000 : ℝ)^3397 := by
    have hnat : (1908678929 : ℕ)^4421*6250000000000^3397 ≤ 724094508601^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908678929 10000000000 724094508601 6250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559267113/1000000000 : ℝ)^4421 ≤ (23469888398079/50000000000000 : ℝ)^3397 := by
    have hnat : (559267113 : ℕ)^4421*50000000000000^3397 ≤ 23469888398079^3397*1000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559267113 1000000000 23469888398079 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158914343/312500000 : ℝ)^4421 ≤ (41474711056753/100000000000000 : ℝ)^3397 := by
    have hnat : (158914343 : ℕ)^4421*100000000000000^3397 ≤ 41474711056753^3397*312500000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158914343 312500000 41474711056753 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908678929/10000000000 : ℝ), (559267113/1000000000 : ℝ), (158914343/312500000 : ℝ)] ![(724094508601/6250000000000 : ℝ), (23469888398079/50000000000000 : ℝ), (41474711056753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908678929/10000000000 : ℝ)|^4421 ≤ (724094508601/6250000000000 : ℝ)^3397
        have hw : |(-1908678929/10000000000 : ℝ)|=(1908678929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559267113/1000000000 : ℝ)|^4421 ≤ (23469888398079/50000000000000 : ℝ)^3397
        have hw : |(559267113/1000000000 : ℝ)|=(559267113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158914343/312500000 : ℝ)|^4421 ≤ (41474711056753/100000000000000 : ℝ)^3397
        have hw : |(158914343/312500000 : ℝ)|=(158914343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078725109/2000000000 : ℝ)*x 0 + (-2176909039/10000000000 : ℝ)*x 1 + (2542630539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078725109/2000000000 : ℝ)^4421 ≤ (44777339032457/100000000000000 : ℝ)^3397 := by
    have hnat : (1078725109 : ℕ)^4421*100000000000000^3397 ≤ 44777339032457^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078725109 2000000000 44777339032457 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176909039/10000000000 : ℝ)^4421 ≤ (687396378913/5000000000000 : ℝ)^3397 := by
    have hnat : (2176909039 : ℕ)^4421*5000000000000^3397 ≤ 687396378913^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176909039 10000000000 687396378913 5000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542630539/5000000000 : ℝ)^4421 ≤ (41474733368213/100000000000000 : ℝ)^3397 := by
    have hnat : (2542630539 : ℕ)^4421*100000000000000^3397 ≤ 41474733368213^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542630539 5000000000 41474733368213 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078725109/2000000000 : ℝ), (-2176909039/10000000000 : ℝ), (2542630539/5000000000 : ℝ)] ![(44777339032457/100000000000000 : ℝ), (687396378913/5000000000000 : ℝ), (41474733368213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078725109/2000000000 : ℝ)|^4421 ≤ (44777339032457/100000000000000 : ℝ)^3397
        have hw : |(1078725109/2000000000 : ℝ)|=(1078725109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176909039/10000000000 : ℝ)|^4421 ≤ (687396378913/5000000000000 : ℝ)^3397
        have hw : |(-2176909039/10000000000 : ℝ)|=(2176909039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542630539/5000000000 : ℝ)|^4421 ≤ (41474733368213/100000000000000 : ℝ)^3397
        have hw : |(2542630539/5000000000 : ℝ)|=(2542630539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696813657/5000000000 : ℝ)*x 0 + (1271314783/2500000000 : ℝ)*x 1 + (-2176909227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696813657/5000000000 : ℝ)^4421 ≤ (44777358145521/100000000000000 : ℝ)^3397 := by
    have hnat : (2696813657 : ℕ)^4421*100000000000000^3397 ≤ 44777358145521^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696813657 5000000000 44777358145521 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271314783/2500000000 : ℝ)^4421 ≤ (20737356356299/50000000000000 : ℝ)^3397 := by
    have hnat : (1271314783 : ℕ)^4421*50000000000000^3397 ≤ 20737356356299^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271314783 2500000000 20737356356299 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176909227/10000000000 : ℝ)^4421 ≤ (13747929123443/100000000000000 : ℝ)^3397 := by
    have hnat : (2176909227 : ℕ)^4421*100000000000000^3397 ≤ 13747929123443^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176909227 10000000000 13747929123443 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696813657/5000000000 : ℝ), (1271314783/2500000000 : ℝ), (-2176909227/10000000000 : ℝ)] ![(44777358145521/100000000000000 : ℝ), (20737356356299/50000000000000 : ℝ), (13747929123443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696813657/5000000000 : ℝ)|^4421 ≤ (44777358145521/100000000000000 : ℝ)^3397
        have hw : |(2696813657/5000000000 : ℝ)|=(2696813657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271314783/2500000000 : ℝ)|^4421 ≤ (20737356356299/50000000000000 : ℝ)^3397
        have hw : |(1271314783/2500000000 : ℝ)|=(1271314783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176909227/10000000000 : ℝ)|^4421 ≤ (13747929123443/100000000000000 : ℝ)^3397
        have hw : |(-2176909227/10000000000 : ℝ)|=(2176909227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270806851/10000000000 : ℝ)*x 0 + (1873655533/5000000000 : ℝ)*x 1 + (607236461/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270806851/10000000000 : ℝ)^4421 ≤ (16523420057607/50000000000000 : ℝ)^3397 := by
    have hnat : (4270806851 : ℕ)^4421*50000000000000^3397 ≤ 16523420057607^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270806851 10000000000 16523420057607 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873655533/5000000000 : ℝ)^4421 ≤ (27875379048883/100000000000000 : ℝ)^3397 := by
    have hnat : (1873655533 : ℕ)^4421*100000000000000^3397 ≤ 27875379048883^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873655533 5000000000 27875379048883 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (607236461/1250000000 : ℝ)^4421 ≤ (39077780818677/100000000000000 : ℝ)^3397 := by
    have hnat : (607236461 : ℕ)^4421*100000000000000^3397 ≤ 39077780818677^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607236461 1250000000 39077780818677 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270806851/10000000000 : ℝ), (1873655533/5000000000 : ℝ), (607236461/1250000000 : ℝ)] ![(16523420057607/50000000000000 : ℝ), (27875379048883/100000000000000 : ℝ), (39077780818677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270806851/10000000000 : ℝ)|^4421 ≤ (16523420057607/50000000000000 : ℝ)^3397
        have hw : |(4270806851/10000000000 : ℝ)|=(4270806851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1873655533/5000000000 : ℝ)|^4421 ≤ (27875379048883/100000000000000 : ℝ)^3397
        have hw : |(1873655533/5000000000 : ℝ)|=(1873655533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(607236461/1250000000 : ℝ)|^4421 ≤ (39077780818677/100000000000000 : ℝ)^3397
        have hw : |(607236461/1250000000 : ℝ)|=(607236461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-954517803/5000000000 : ℝ)*x 0 + (636382669/1250000000 : ℝ)*x 1 + (1396693221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954517803/5000000000 : ℝ)^4421 ≤ (1448541229629/12500000000000 : ℝ)^3397 := by
    have hnat : (954517803 : ℕ)^4421*12500000000000^3397 ≤ 1448541229629^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954517803 5000000000 1448541229629 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636382669/1250000000 : ℝ)^4421 ≤ (10384077589723/25000000000000 : ℝ)^3397 := by
    have hnat : (636382669 : ℕ)^4421*25000000000000^3397 ≤ 10384077589723^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636382669 1250000000 10384077589723 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396693221/2500000000 : ℝ)^4421 ≤ (46875359790733/100000000000000 : ℝ)^3397 := by
    have hnat : (1396693221 : ℕ)^4421*100000000000000^3397 ≤ 46875359790733^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396693221 2500000000 46875359790733 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954517803/5000000000 : ℝ), (636382669/1250000000 : ℝ), (1396693221/2500000000 : ℝ)] ![(1448541229629/12500000000000 : ℝ), (10384077589723/25000000000000 : ℝ), (46875359790733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954517803/5000000000 : ℝ)|^4421 ≤ (1448541229629/12500000000000 : ℝ)^3397
        have hw : |(-954517803/5000000000 : ℝ)|=(954517803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636382669/1250000000 : ℝ)|^4421 ≤ (10384077589723/25000000000000 : ℝ)^3397
        have hw : |(636382669/1250000000 : ℝ)|=(636382669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1396693221/2500000000 : ℝ)|^4421 ≤ (46875359790733/100000000000000 : ℝ)^3397
        have hw : |(1396693221/2500000000 : ℝ)|=(1396693221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_5 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260745663/10000000000 : ℝ)*x 0 + (-1675396439/10000000000 : ℝ)*x 1 + (5586772921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260745663/10000000000 : ℝ)^4421 ≤ (43347007653607/100000000000000 : ℝ)^3397 := by
    have hnat : (5260745663 : ℕ)^4421*100000000000000^3397 ≤ 43347007653607^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260745663 10000000000 43347007653607 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1675396439/10000000000 : ℝ)^4421 ≤ (9777632129023/100000000000000 : ℝ)^3397 := by
    have hnat : (1675396439 : ℕ)^4421*100000000000000^3397 ≤ 9777632129023^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675396439 10000000000 9777632129023 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586772921/10000000000 : ℝ)^4421 ≤ (1171884004869/2500000000000 : ℝ)^3397 := by
    have hnat : (5586772921 : ℕ)^4421*2500000000000^3397 ≤ 1171884004869^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586772921 10000000000 1171884004869 2500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260745663/10000000000 : ℝ), (-1675396439/10000000000 : ℝ), (5586772921/10000000000 : ℝ)] ![(43347007653607/100000000000000 : ℝ), (9777632129023/100000000000000 : ℝ), (1171884004869/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260745663/10000000000 : ℝ)|^4421 ≤ (43347007653607/100000000000000 : ℝ)^3397
        have hw : |(5260745663/10000000000 : ℝ)|=(5260745663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1675396439/10000000000 : ℝ)|^4421 ≤ (9777632129023/100000000000000 : ℝ)^3397
        have hw : |(-1675396439/10000000000 : ℝ)|=(1675396439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586772921/10000000000 : ℝ)|^4421 ≤ (1171884004869/2500000000000 : ℝ)^3397
        have hw : |(5586772921/10000000000 : ℝ)|=(5586772921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_6 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260745541/10000000000 : ℝ)*x 0 + (698346611/1250000000 : ℝ)*x 1 + (-1675396659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260745541/10000000000 : ℝ)^4421 ≤ (43347006345339/100000000000000 : ℝ)^3397 := by
    have hnat : (5260745541 : ℕ)^4421*100000000000000^3397 ≤ 43347006345339^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260745541 10000000000 43347006345339 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698346611/1250000000 : ℝ)^4421 ≤ (46875359834411/100000000000000 : ℝ)^3397 := by
    have hnat : (698346611 : ℕ)^4421*100000000000000^3397 ≤ 46875359834411^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698346611 1250000000 46875359834411 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1675396659/10000000000 : ℝ)^4421 ≤ (4888816899987/50000000000000 : ℝ)^3397 := by
    have hnat : (1675396659 : ℕ)^4421*50000000000000^3397 ≤ 4888816899987^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675396659 10000000000 4888816899987 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260745541/10000000000 : ℝ), (698346611/1250000000 : ℝ), (-1675396659/10000000000 : ℝ)] ![(43347006345339/100000000000000 : ℝ), (46875359834411/100000000000000 : ℝ), (4888816899987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260745541/10000000000 : ℝ)|^4421 ≤ (43347006345339/100000000000000 : ℝ)^3397
        have hw : |(5260745541/10000000000 : ℝ)|=(5260745541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698346611/1250000000 : ℝ)|^4421 ≤ (46875359834411/100000000000000 : ℝ)^3397
        have hw : |(698346611/1250000000 : ℝ)|=(698346611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1675396659/10000000000 : ℝ)|^4421 ≤ (4888816899987/50000000000000 : ℝ)^3397
        have hw : |(-1675396659/10000000000 : ℝ)|=(1675396659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s1_7 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067897077/2500000000 : ℝ)*x 0 + (2422596859/5000000000 : ℝ)*x 1 + (940054369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067897077/2500000000 : ℝ)^4421 ≤ (16527354942597/50000000000000 : ℝ)^3397 := by
    have hnat : (1067897077 : ℕ)^4421*50000000000000^3397 ≤ 16527354942597^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067897077 2500000000 16527354942597 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422596859/5000000000 : ℝ)^4421 ≤ (19472448806917/50000000000000 : ℝ)^3397 := by
    have hnat : (2422596859 : ℕ)^4421*50000000000000^3397 ≤ 19472448806917^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422596859 5000000000 19472448806917 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940054369/2500000000 : ℝ)^4421 ≤ (28000392478401/100000000000000 : ℝ)^3397 := by
    have hnat : (940054369 : ℕ)^4421*100000000000000^3397 ≤ 28000392478401^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940054369 2500000000 28000392478401 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067897077/2500000000 : ℝ), (2422596859/5000000000 : ℝ), (940054369/2500000000 : ℝ)] ![(16527354942597/50000000000000 : ℝ), (19472448806917/50000000000000 : ℝ), (28000392478401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067897077/2500000000 : ℝ)|^4421 ≤ (16527354942597/50000000000000 : ℝ)^3397
        have hw : |(1067897077/2500000000 : ℝ)|=(1067897077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422596859/5000000000 : ℝ)|^4421 ≤ (19472448806917/50000000000000 : ℝ)^3397
        have hw : |(2422596859/5000000000 : ℝ)|=(2422596859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940054369/2500000000 : ℝ)|^4421 ≤ (28000392478401/100000000000000 : ℝ)^3397
        have hw : |(940054369/2500000000 : ℝ)|=(940054369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7909/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9319/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/100000 : ℝ) ^ (1105/256 : ℝ) ≤ (1606184239651/20000000000000000000 : ℝ) := by
    have hpowers : (2271/100000 : ℝ)^1105 ≤ (1606184239651/20000000000000000000 : ℝ)^256 := by
      have hnat : (2271 : ℕ)^1105*20000000000000000000^256 ≤ 1606184239651^256*100000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 100000 1606184239651 20000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/100000 : ℝ)) (X := (1606184239651/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26039/100000 : ℝ) ^ (1105/256 : ℝ) ≤ (300328870715019317/100000000000000000000 : ℝ) := by
    have hpowers : (26039/100000 : ℝ)^1105 ≤ (300328870715019317/100000000000000000000 : ℝ)^256 := by
      have hnat : (26039 : ℕ)^1105*100000000000000000000^256 ≤ 300328870715019317^256*100000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26039 100000 300328870715019317 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26039/100000 : ℝ)) (X := (300328870715019317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000001606184239651/10000000000000000000 : ℝ) ≤ (10000000372111439/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (10000001606184239651/10000000000000000000 : ℝ)^256 ≤ (10000000372111439/10000000000000000 : ℝ)^1105 := by
      have hnat : (10000001606184239651 : ℕ)^256*10000000000000000^1105 ≤ 10000000372111439^1105*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000001606184239651 10000000000000000000 10000000372111439 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000372111439/10000000000000000 : ℝ)) (X := (10000001606184239651/10000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25075084225409054393/25000000000000000000 : ℝ) ≤ (1250868752188889/1250000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (25075084225409054393/25000000000000000000 : ℝ)^256 ≤ (1250868752188889/1250000000000000 : ℝ)^1105 := by
      have hnat : (25075084225409054393 : ℕ)^256*1250000000000000^1105 ≤ 1250868752188889^1105*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25075084225409054393 25000000000000000000 1250868752188889 1250000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250868752188889/1250000000000000 : ℝ)) (X := (25075084225409054393/25000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50300328870715019317/50000000000000000000 : ℝ) ≤ (2002779932582157/2000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50300328870715019317/50000000000000000000 : ℝ)^256 ≤ (2002779932582157/2000000000000000 : ℝ)^1105 := by
      have hnat : (50300328870715019317 : ℕ)^256*2000000000000000^1105 ≤ 2002779932582157^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50300328870715019317 50000000000000000000 2002779932582157 2000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002779932582157/2000000000000000 : ℝ)) (X := (50300328870715019317/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1606184239651/20000000000000000000 : ℝ) ≤ ((118824221777469683693/118840000000000000000 : ℝ)+2*(6949645399673/2376800000000000 : ℝ)*(2271/100000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (118824221777469683693/118840000000000000000 : ℝ)+2*(6949645399673/2376800000000000 : ℝ)*(2271/100000 : ℝ)=(10000000372111439/10000000000000000 : ℝ) by norm_num, show 1+2*(1606184239651/20000000000000000000 : ℝ)=(10000001606184239651/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(300328870715019317/100000000000000000000 : ℝ)+(1606184239651/20000000000000000000 : ℝ) ≤ ((118824221777469683693/118840000000000000000 : ℝ)+(6949645399673/2376800000000000 : ℝ)*((26039/100000 : ℝ)+(2271/100000 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (118824221777469683693/118840000000000000000 : ℝ)+(6949645399673/2376800000000000 : ℝ)*((26039/100000 : ℝ)+(2271/100000 : ℝ))=(1250868752188889/1250000000000000 : ℝ) by norm_num, show 1+(300328870715019317/100000000000000000000 : ℝ)+(1606184239651/20000000000000000000 : ℝ)=(25075084225409054393/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(300328870715019317/100000000000000000000 : ℝ) ≤ ((118824221777469683693/118840000000000000000 : ℝ)+2*(6949645399673/2376800000000000 : ℝ)*(26039/100000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (118824221777469683693/118840000000000000000 : ℝ)+2*(6949645399673/2376800000000000 : ℝ)*(26039/100000 : ℝ)=(2002779932582157/2000000000000000 : ℝ) by norm_num, show 1+2*(300328870715019317/100000000000000000000 : ℝ)=(50300328870715019317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (118824221777469683693/118840000000000000000 : ℝ)*(X 1 0+X 2 0)+(6949645399673/2376800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2271/100000 : ℝ)) (hi := (26039/100000 : ℝ)) (c := (118824221777469683693/118840000000000000000 : ℝ)) (alpha := (6949645399673/2376800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (118824221777469683693/118840000000000000000 : ℝ)*(X 0 1+X 2 1)+(6949645399673/2376800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2271/100000 : ℝ)) (hi := (26039/100000 : ℝ)) (c := (118824221777469683693/118840000000000000000 : ℝ)) (alpha := (6949645399673/2376800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (118824221777469683693/118840000000000000000 : ℝ)*(X 0 2+X 1 2)+(6949645399673/2376800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (2271/100000 : ℝ)) (hi := (26039/100000 : ℝ)) (c := (118824221777469683693/118840000000000000000 : ℝ)) (alpha := (6949645399673/2376800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908678929/10000000000 : ℝ)*X 0 0+(559267113/1000000000 : ℝ)*X 0 1+(158914343/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1078725109/2000000000 : ℝ)*X 1 0+(-2176909039/10000000000 : ℝ)*X 1 1+(2542630539/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696813657/5000000000 : ℝ)*X 2 0+(1271314783/2500000000 : ℝ)*X 2 1+(-2176909227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270806851/10000000000 : ℝ)*X 0 0+(1873655533/5000000000 : ℝ)*X 0 1+(607236461/1250000000 : ℝ)*X 0 2+(4270806851/10000000000 : ℝ)*X 1 0+(1873655533/5000000000 : ℝ)*X 1 1+(607236461/1250000000 : ℝ)*X 1 2+(4270806851/10000000000 : ℝ)*X 2 0+(1873655533/5000000000 : ℝ)*X 2 1+(607236461/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-954517803/5000000000 : ℝ)*X 0 0+(636382669/1250000000 : ℝ)*X 0 1+(1396693221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260745663/10000000000 : ℝ)*X 1 0+(-1675396439/10000000000 : ℝ)*X 1 1+(5586772921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260745541/10000000000 : ℝ)*X 2 0+(698346611/1250000000 : ℝ)*X 2 1+(-1675396659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1067897077/2500000000 : ℝ)*X 0 0+(2422596859/5000000000 : ℝ)*X 0 1+(940054369/2500000000 : ℝ)*X 0 2+(1067897077/2500000000 : ℝ)*X 1 0+(2422596859/5000000000 : ℝ)*X 1 1+(940054369/2500000000 : ℝ)*X 1 2+(1067897077/2500000000 : ℝ)*X 2 0+(2422596859/5000000000 : ℝ)*X 2 1+(940054369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44937838747808010863973/5942000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1202319687/100000000000000 : ℝ)*(base19) + (1776182847/100000000000000 : ℝ)*(base23) + (3175363/3125000000000 : ℝ)*(upper3) + (9779281/25000000000000 : ℝ)*(upper4) + (96983549/100000000000000 : ℝ)*(upper5) + (71781506045817/5000000000000 : ℝ)*(major0) + (71781506045817/5000000000000 : ℝ)*(major1) + (71781506045817/5000000000000 : ℝ)*(major2) + (1970800176282013/100000000000000 : ℝ)*(sp0) + (246352123834139/12500000000000 : ℝ)*(sp1) + (61588013025311/3125000000000 : ℝ)*(sp2) + (225108839604239/25000000000000 : ℝ)*(sp3) + (9008355393/50000000000000 : ℝ)*(sp4) + (6438331377/100000000000000 : ℝ)*(sp7) + (900441796748333/100000000000000 : ℝ)*(f.failure) + (1970818192992799/100000000000000 : ℝ)*(f.sum) + (70688350023/5942000000000000000000000000 : ℝ)*base65 + (1170063252916987819/594200000000000000000000000000000 : ℝ)*base68 + (231904379661412181/594200000000000000000000000000000 : ℝ)*base69 + (2134104943777412181/594200000000000000000000000000000 : ℝ)*base71 + (2878817327853/5942000000000000000000000000 : ℝ)*base73 + (4797409901239387819/594200000000000000000000000000000 : ℝ)*base76 + (811188231727812181/594200000000000000000000000000000 : ℝ)*base77 + (6581415499165387819/594200000000000000000000000000000 : ℝ)*base80 + (17409897148249/5942000000000000000000000000 : ℝ)*base81 + (7383731/10000000000000000000000 : ℝ)*base90 + (7383731/10000000000000000000000 : ℝ)*base92 + (7383731/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5069221523307549903549104433/1485500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218694479/25000000000000 : ℝ)*(base19) + (206663353/25000000000000 : ℝ)*(base23) + (2013379/2000000000000 : ℝ)*(upper3) + (5337341/100000000000000 : ℝ)*(lower4) + (53568341/100000000000000 : ℝ)*(upper5) + (734745216905727/50000000000000 : ℝ)*(major0) + (734745216905727/50000000000000 : ℝ)*(major1) + (734745216905727/50000000000000 : ℝ)*(major2) + (2919715937/50000000000000 : ℝ)*(sp1) + (5384557149/100000000000000 : ℝ)*(sp2) + (504325356220701/25000000000000 : ℝ)*(sp4) + (1008647355336507/50000000000000 : ℝ)*(sp5) + (2017295213672243/100000000000000 : ℝ)*(sp6) + (460839664495581/50000000000000 : ℝ)*(sp7) + (460839664495581/50000000000000 : ℝ)*(f.failure) + (504325356220701/25000000000000 : ℝ)*(f.sum) + (187915182182969/59420000000000000000000000000 : ℝ)*base66 + (840311558954240189/5942000000000000000000000000000000 : ℝ)*base68 + (6838894396562240189/5942000000000000000000000000000000 : ℝ)*base70 + (36914681896282240189/5942000000000000000000000000000000 : ℝ)*base72 + (79819488755991/59420000000000000000000000000 : ℝ)*base73 + (1953082928577759811/5942000000000000000000000000000000 : ℝ)*base75 + (7993937773336240189/5942000000000000000000000000000000 : ℝ)*base78 + (20240296519202240189/5942000000000000000000000000000000 : ℝ)*base80 + (7895309144569/59420000000000000000000000000 : ℝ)*base82 + (36867/5000000000000000000000 : ℝ)*base90 + (36867/5000000000000000000000 : ℝ)*base92 + (36867/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1461_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9319/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1461_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1461_s2_0 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939496627/10000000000 : ℝ)*x 0 + (1090251951/2000000000 : ℝ)*x 1 + (260339937/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939496627/10000000000 : ℝ)^4421 ≤ (2957387776501/25000000000000 : ℝ)^3397 := by
    have hnat : (1939496627 : ℕ)^4421*25000000000000^3397 ≤ 2957387776501^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939496627 10000000000 2957387776501 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090251951/2000000000 : ℝ)^4421 ≤ (22700522545079/50000000000000 : ℝ)^3397 := by
    have hnat : (1090251951 : ℕ)^4421*50000000000000^3397 ≤ 22700522545079^3397*2000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090251951 2000000000 22700522545079 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260339937/500000000 : ℝ)^4421 ≤ (42769403787671/100000000000000 : ℝ)^3397 := by
    have hnat : (260339937 : ℕ)^4421*100000000000000^3397 ≤ 42769403787671^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260339937 500000000 42769403787671 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939496627/10000000000 : ℝ), (1090251951/2000000000 : ℝ), (260339937/500000000 : ℝ)] ![(2957387776501/25000000000000 : ℝ), (22700522545079/50000000000000 : ℝ), (42769403787671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939496627/10000000000 : ℝ)|^4421 ≤ (2957387776501/25000000000000 : ℝ)^3397
        have hw : |(-1939496627/10000000000 : ℝ)|=(1939496627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090251951/2000000000 : ℝ)|^4421 ≤ (22700522545079/50000000000000 : ℝ)^3397
        have hw : |(1090251951/2000000000 : ℝ)|=(1090251951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260339937/500000000 : ℝ)|^4421 ≤ (42769403787671/100000000000000 : ℝ)^3397
        have hw : |(260339937/500000000 : ℝ)|=(260339937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_1 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214326047/400000000 : ℝ)*x 0 + (-516275961/2500000000 : ℝ)*x 1 + (1301698811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214326047/400000000 : ℝ)^4421 ≤ (22197219345307/50000000000000 : ℝ)^3397 := by
    have hnat : (214326047 : ℕ)^4421*50000000000000^3397 ≤ 22197219345307^3397*400000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214326047 400000000 22197219345307 50000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516275961/2500000000 : ℝ)^4421 ≤ (12836194883819/100000000000000 : ℝ)^3397 := by
    have hnat : (516275961 : ℕ)^4421*100000000000000^3397 ≤ 12836194883819^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516275961 2500000000 12836194883819 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301698811/2500000000 : ℝ)^4421 ≤ (42769366414603/100000000000000 : ℝ)^3397 := by
    have hnat : (1301698811 : ℕ)^4421*100000000000000^3397 ≤ 42769366414603^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301698811 2500000000 42769366414603 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214326047/400000000 : ℝ), (-516275961/2500000000 : ℝ), (1301698811/2500000000 : ℝ)] ![(22197219345307/50000000000000 : ℝ), (12836194883819/100000000000000 : ℝ), (42769366414603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214326047/400000000 : ℝ)|^4421 ≤ (22197219345307/50000000000000 : ℝ)^3397
        have hw : |(214326047/400000000 : ℝ)|=(214326047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516275961/2500000000 : ℝ)|^4421 ≤ (12836194883819/100000000000000 : ℝ)^3397
        have hw : |(-516275961/2500000000 : ℝ)|=(516275961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301698811/2500000000 : ℝ)|^4421 ≤ (42769366414603/100000000000000 : ℝ)^3397
        have hw : |(1301698811/2500000000 : ℝ)|=(1301698811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_2 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334884319/625000000 : ℝ)*x 0 + (5206796971/10000000000 : ℝ)*x 1 + (-1032552161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334884319/625000000 : ℝ)^4421 ≤ (11098604089769/25000000000000 : ℝ)^3397 := by
    have hnat : (334884319 : ℕ)^4421*25000000000000^3397 ≤ 11098604089769^3397*625000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334884319 625000000 11098604089769 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206796971/10000000000 : ℝ)^4421 ≤ (42769384876641/100000000000000 : ℝ)^3397 := by
    have hnat : (5206796971 : ℕ)^4421*100000000000000^3397 ≤ 42769384876641^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206796971 10000000000 42769384876641 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032552161/5000000000 : ℝ)^4421 ≤ (12836198750579/100000000000000 : ℝ)^3397 := by
    have hnat : (1032552161 : ℕ)^4421*100000000000000^3397 ≤ 12836198750579^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032552161 5000000000 12836198750579 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334884319/625000000 : ℝ), (5206796971/10000000000 : ℝ), (-1032552161/5000000000 : ℝ)] ![(11098604089769/25000000000000 : ℝ), (42769384876641/100000000000000 : ℝ), (12836198750579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334884319/625000000 : ℝ)|^4421 ≤ (11098604089769/25000000000000 : ℝ)^3397
        have hw : |(334884319/625000000 : ℝ)|=(334884319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206796971/10000000000 : ℝ)|^4421 ≤ (42769384876641/100000000000000 : ℝ)^3397
        have hw : |(5206796971/10000000000 : ℝ)|=(5206796971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032552161/5000000000 : ℝ)|^4421 ≤ (12836198750579/100000000000000 : ℝ)^3397
        have hw : |(-1032552161/5000000000 : ℝ)|=(1032552161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_3 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073158419/2500000000 : ℝ)*x 0 + (4032480987/10000000000 : ℝ)*x 1 + (1141886671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073158419/2500000000 : ℝ)^4421 ≤ (33266813202757/100000000000000 : ℝ)^3397 := by
    have hnat : (1073158419 : ℕ)^4421*100000000000000^3397 ≤ 33266813202757^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073158419 2500000000 33266813202757 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032480987/10000000000 : ℝ)^4421 ≤ (6133453550857/20000000000000 : ℝ)^3397 := by
    have hnat : (4032480987 : ℕ)^4421*20000000000000^3397 ≤ 6133453550857^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032480987 10000000000 6133453550857 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141886671/2500000000 : ℝ)^4421 ≤ (9016479757819/25000000000000 : ℝ)^3397 := by
    have hnat : (1141886671 : ℕ)^4421*25000000000000^3397 ≤ 9016479757819^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141886671 2500000000 9016479757819 25000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073158419/2500000000 : ℝ), (4032480987/10000000000 : ℝ), (1141886671/2500000000 : ℝ)] ![(33266813202757/100000000000000 : ℝ), (6133453550857/20000000000000 : ℝ), (9016479757819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073158419/2500000000 : ℝ)|^4421 ≤ (33266813202757/100000000000000 : ℝ)^3397
        have hw : |(1073158419/2500000000 : ℝ)|=(1073158419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032480987/10000000000 : ℝ)|^4421 ≤ (6133453550857/20000000000000 : ℝ)^3397
        have hw : |(4032480987/10000000000 : ℝ)|=(4032480987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141886671/2500000000 : ℝ)|^4421 ≤ (9016479757819/25000000000000 : ℝ)^3397
        have hw : |(1141886671/2500000000 : ℝ)|=(1141886671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_4 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-242442079/1250000000 : ℝ)*x 0 + (651019109/1250000000 : ℝ)*x 1 + (2724947411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242442079/1250000000 : ℝ)^4421 ≤ (11829868661643/100000000000000 : ℝ)^3397 := by
    have hnat : (242442079 : ℕ)^4421*100000000000000^3397 ≤ 11829868661643^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242442079 1250000000 11829868661643 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651019109/1250000000 : ℝ)^4421 ≤ (42783880348397/100000000000000 : ℝ)^3397 := by
    have hnat : (651019109 : ℕ)^4421*100000000000000^3397 ≤ 42783880348397^3397*1250000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651019109 1250000000 42783880348397 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724947411/5000000000 : ℝ)^4421 ≤ (45386250978779/100000000000000 : ℝ)^3397 := by
    have hnat : (2724947411 : ℕ)^4421*100000000000000^3397 ≤ 45386250978779^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724947411 5000000000 45386250978779 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242442079/1250000000 : ℝ), (651019109/1250000000 : ℝ), (2724947411/5000000000 : ℝ)] ![(11829868661643/100000000000000 : ℝ), (42783880348397/100000000000000 : ℝ), (45386250978779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242442079/1250000000 : ℝ)|^4421 ≤ (11829868661643/100000000000000 : ℝ)^3397
        have hw : |(-242442079/1250000000 : ℝ)|=(242442079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651019109/1250000000 : ℝ)|^4421 ≤ (42783880348397/100000000000000 : ℝ)^3397
        have hw : |(651019109/1250000000 : ℝ)|=(651019109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724947411/5000000000 : ℝ)|^4421 ≤ (45386250978779/100000000000000 : ℝ)^3397
        have hw : |(2724947411/5000000000 : ℝ)|=(2724947411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_5 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294395497/10000000000 : ℝ)*x 0 + (-1822002661/10000000000 : ℝ)*x 1 + (5449895927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294395497/10000000000 : ℝ)^4421 ≤ (8741639840381/20000000000000 : ℝ)^3397 := by
    have hnat : (5294395497 : ℕ)^4421*20000000000000^3397 ≤ 8741639840381^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294395497 10000000000 8741639840381 20000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822002661/10000000000 : ℝ)^4421 ≤ (10905537826881/100000000000000 : ℝ)^3397 := by
    have hnat : (1822002661 : ℕ)^4421*100000000000000^3397 ≤ 10905537826881^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822002661 10000000000 10905537826881 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449895927/10000000000 : ℝ)^4421 ≤ (45386262955101/100000000000000 : ℝ)^3397 := by
    have hnat : (5449895927 : ℕ)^4421*100000000000000^3397 ≤ 45386262955101^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449895927 10000000000 45386262955101 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294395497/10000000000 : ℝ), (-1822002661/10000000000 : ℝ), (5449895927/10000000000 : ℝ)] ![(8741639840381/20000000000000 : ℝ), (10905537826881/100000000000000 : ℝ), (45386262955101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294395497/10000000000 : ℝ)|^4421 ≤ (8741639840381/20000000000000 : ℝ)^3397
        have hw : |(5294395497/10000000000 : ℝ)|=(5294395497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1822002661/10000000000 : ℝ)|^4421 ≤ (10905537826881/100000000000000 : ℝ)^3397
        have hw : |(-1822002661/10000000000 : ℝ)|=(1822002661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449895927/10000000000 : ℝ)|^4421 ≤ (45386262955101/100000000000000 : ℝ)^3397
        have hw : |(5449895927/10000000000 : ℝ)|=(5449895927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_6 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330899671/625000000 : ℝ)*x 0 + (1362473739/2500000000 : ℝ)*x 1 + (-1822005061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330899671/625000000 : ℝ)^4421 ≤ (43708191025617/100000000000000 : ℝ)^3397 := by
    have hnat : (330899671 : ℕ)^4421*100000000000000^3397 ≤ 43708191025617^3397*625000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330899671 625000000 43708191025617 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362473739/2500000000 : ℝ)^4421 ≤ (45386252431111/100000000000000 : ℝ)^3397 := by
    have hnat : (1362473739 : ℕ)^4421*100000000000000^3397 ≤ 45386252431111^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362473739 2500000000 45386252431111 100000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1822005061/10000000000 : ℝ)^4421 ≤ (1363194565283/12500000000000 : ℝ)^3397 := by
    have hnat : (1822005061 : ℕ)^4421*12500000000000^3397 ≤ 1363194565283^3397*10000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822005061 10000000000 1363194565283 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330899671/625000000 : ℝ), (1362473739/2500000000 : ℝ), (-1822005061/10000000000 : ℝ)] ![(43708191025617/100000000000000 : ℝ), (45386252431111/100000000000000 : ℝ), (1363194565283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330899671/625000000 : ℝ)|^4421 ≤ (43708191025617/100000000000000 : ℝ)^3397
        have hw : |(330899671/625000000 : ℝ)|=(330899671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362473739/2500000000 : ℝ)|^4421 ≤ (45386252431111/100000000000000 : ℝ)^3397
        have hw : |(1362473739/2500000000 : ℝ)|=(1362473739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1822005061/10000000000 : ℝ)|^4421 ≤ (1363194565283/12500000000000 : ℝ)^3397
        have hw : |(-1822005061/10000000000 : ℝ)|=(1822005061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1461_s2_7 (p : ℝ) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214635997/500000000 : ℝ)*x 0 + (1141145639/2500000000 : ℝ)*x 1 + (2017735009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214635997/500000000 : ℝ)^4421 ≤ (1330707330033/4000000000000 : ℝ)^3397 := by
    have hnat : (214635997 : ℕ)^4421*4000000000000^3397 ≤ 1330707330033^3397*500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214635997 500000000 1330707330033 4000000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141145639/2500000000 : ℝ)^4421 ≤ (4504432698509/12500000000000 : ℝ)^3397 := by
    have hnat : (1141145639 : ℕ)^4421*12500000000000^3397 ≤ 4504432698509^3397*2500000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141145639 2500000000 4504432698509 12500000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017735009/5000000000 : ℝ)^4421 ≤ (1918553446501/6250000000000 : ℝ)^3397 := by
    have hnat : (2017735009 : ℕ)^4421*6250000000000^3397 ≤ 1918553446501^3397*5000000000^4421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017735009 5000000000 1918553446501 6250000000000 4421 3397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4421/1024 : ℝ)) 4421 3397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214635997/500000000 : ℝ), (1141145639/2500000000 : ℝ), (2017735009/5000000000 : ℝ)] ![(1330707330033/4000000000000 : ℝ), (4504432698509/12500000000000 : ℝ), (1918553446501/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214635997/500000000 : ℝ)|^4421 ≤ (1330707330033/4000000000000 : ℝ)^3397
        have hw : |(214635997/500000000 : ℝ)|=(214635997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141145639/2500000000 : ℝ)|^4421 ≤ (4504432698509/12500000000000 : ℝ)^3397
        have hw : |(1141145639/2500000000 : ℝ)|=(1141145639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017735009/5000000000 : ℝ)|^4421 ≤ (1918553446501/6250000000000 : ℝ)^3397
        have hw : |(2017735009/5000000000 : ℝ)|=(2017735009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1461_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2633/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7853/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9319/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9319/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9319/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9319/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9319/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9319/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7909/100000 : ℝ) ^ (1105/256 : ℝ) ≤ (1753254983105889/100000000000000000000 : ℝ) := by
    have hpowers : (7909/100000 : ℝ)^1105 ≤ (1753254983105889/100000000000000000000 : ℝ)^256 := by
      have hnat : (7909 : ℕ)^1105*100000000000000000000^256 ≤ 1753254983105889^256*100000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7909 100000 1753254983105889 100000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7909/100000 : ℝ)) (X := (1753254983105889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9319/50000 : ℝ) ^ (1105/256 : ℝ) ≤ (35458226900749901/50000000000000000000 : ℝ) := by
    have hpowers : (9319/50000 : ℝ)^1105 ≤ (35458226900749901/50000000000000000000 : ℝ)^256 := by
      have hnat : (9319 : ℕ)^1105*50000000000000000000^256 ≤ 35458226900749901^256*50000^1105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9319 50000 35458226900749901 50000000000000000000 1105 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9319/50000 : ℝ)) (X := (35458226900749901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001753254983105889/50000000000000000000 : ℝ) ≤ (10000081235697683/10000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (50001753254983105889/50000000000000000000 : ℝ)^256 ≤ (10000081235697683/10000000000000000 : ℝ)^1105 := by
      have hnat : (50001753254983105889 : ℕ)^256*10000000000000000^1105 ≤ 10000081235697683^1105*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001753254983105889 50000000000000000000 10000081235697683 10000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081235697683/10000000000000000 : ℝ)) (X := (50001753254983105889/50000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072669708784605691/100000000000000000000 : ℝ) ≤ (2500420774980711/2500000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (100072669708784605691/100000000000000000000 : ℝ)^256 ≤ (2500420774980711/2500000000000000 : ℝ)^1105 := by
      have hnat : (100072669708784605691 : ℕ)^256*2500000000000000^1105 ≤ 2500420774980711^1105*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072669708784605691 100000000000000000000 2500420774980711 2500000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500420774980711/2500000000000000 : ℝ)) (X := (100072669708784605691/100000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25035458226900749901/25000000000000000000 : ℝ) ≤ (2000656992829601/2000000000000000 : ℝ) ^ (1105/256 : ℝ) := by
    have hpowers : (25035458226900749901/25000000000000000000 : ℝ)^256 ≤ (2000656992829601/2000000000000000 : ℝ)^1105 := by
      have hnat : (25035458226900749901 : ℕ)^256*2000000000000000^1105 ≤ 2000656992829601^1105*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035458226900749901 25000000000000000000 2000656992829601 2000000000000000 256 1105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000656992829601/2000000000000000 : ℝ)) (X := (25035458226900749901/25000000000000000000 : ℝ)) (by norm_num) 1105 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1753254983105889/100000000000000000000 : ℝ) ≤ ((107265533289486844209/107290000000000000000 : ℝ)+2*(1601864225161/1072900000000000 : ℝ)*(7909/100000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (107265533289486844209/107290000000000000000 : ℝ)+2*(1601864225161/1072900000000000 : ℝ)*(7909/100000 : ℝ)=(10000081235697683/10000000000000000 : ℝ) by norm_num, show 1+2*(1753254983105889/100000000000000000000 : ℝ)=(50001753254983105889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35458226900749901/50000000000000000000 : ℝ)+(1753254983105889/100000000000000000000 : ℝ) ≤ ((107265533289486844209/107290000000000000000 : ℝ)+(1601864225161/1072900000000000 : ℝ)*((9319/50000 : ℝ)+(7909/100000 : ℝ)))^(1105/256 : ℝ) := by
    rw [show (107265533289486844209/107290000000000000000 : ℝ)+(1601864225161/1072900000000000 : ℝ)*((9319/50000 : ℝ)+(7909/100000 : ℝ))=(2500420774980711/2500000000000000 : ℝ) by norm_num, show 1+(35458226900749901/50000000000000000000 : ℝ)+(1753254983105889/100000000000000000000 : ℝ)=(100072669708784605691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35458226900749901/50000000000000000000 : ℝ) ≤ ((107265533289486844209/107290000000000000000 : ℝ)+2*(1601864225161/1072900000000000 : ℝ)*(9319/50000 : ℝ))^(1105/256 : ℝ) := by
    rw [show (107265533289486844209/107290000000000000000 : ℝ)+2*(1601864225161/1072900000000000 : ℝ)*(9319/50000 : ℝ)=(2000656992829601/2000000000000000 : ℝ) by norm_num, show 1+2*(35458226900749901/50000000000000000000 : ℝ)=(25035458226900749901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107265533289486844209/107290000000000000000 : ℝ)*(X 1 0+X 2 0)+(1601864225161/1072900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (7909/100000 : ℝ)) (hi := (9319/50000 : ℝ)) (c := (107265533289486844209/107290000000000000000 : ℝ)) (alpha := (1601864225161/1072900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107265533289486844209/107290000000000000000 : ℝ)*(X 0 1+X 2 1)+(1601864225161/1072900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (7909/100000 : ℝ)) (hi := (9319/50000 : ℝ)) (c := (107265533289486844209/107290000000000000000 : ℝ)) (alpha := (1601864225161/1072900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107265533289486844209/107290000000000000000 : ℝ)*(X 0 2+X 1 2)+(1601864225161/1072900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1105/256 : ℝ)) (lo := (7909/100000 : ℝ)) (hi := (9319/50000 : ℝ)) (c := (107265533289486844209/107290000000000000000 : ℝ)) (alpha := (1601864225161/1072900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1939496627/10000000000 : ℝ)*X 0 0+(1090251951/2000000000 : ℝ)*X 0 1+(260339937/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214326047/400000000 : ℝ)*X 1 0+(-516275961/2500000000 : ℝ)*X 1 1+(1301698811/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334884319/625000000 : ℝ)*X 2 0+(5206796971/10000000000 : ℝ)*X 2 1+(-1032552161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073158419/2500000000 : ℝ)*X 0 0+(4032480987/10000000000 : ℝ)*X 0 1+(1141886671/2500000000 : ℝ)*X 0 2+(1073158419/2500000000 : ℝ)*X 1 0+(4032480987/10000000000 : ℝ)*X 1 1+(1141886671/2500000000 : ℝ)*X 1 2+(1073158419/2500000000 : ℝ)*X 2 0+(4032480987/10000000000 : ℝ)*X 2 1+(1141886671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-242442079/1250000000 : ℝ)*X 0 0+(651019109/1250000000 : ℝ)*X 0 1+(2724947411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294395497/10000000000 : ℝ)*X 1 0+(-1822002661/10000000000 : ℝ)*X 1 1+(5449895927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330899671/625000000 : ℝ)*X 2 0+(1362473739/2500000000 : ℝ)*X 2 1+(-1822005061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((214635997/500000000 : ℝ)*X 0 0+(1141145639/2500000000 : ℝ)*X 0 1+(2017735009/5000000000 : ℝ)*X 0 2+(214635997/500000000 : ℝ)*X 1 0+(1141145639/2500000000 : ℝ)*X 1 1+(2017735009/5000000000 : ℝ)*X 1 2+(214635997/500000000 : ℝ)*X 2 0+(1141145639/2500000000 : ℝ)*X 2 1+(2017735009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1461_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23156492314167422153523143709/2682250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (264594373/50000000000000 : ℝ)*(base19) + (3191169/20000000000000 : ℝ)*(upper2) + (293463679/50000000000000 : ℝ)*(lower4) + (48919301/10000000000000 : ℝ)*(upper5) + (1489899107035167/50000000000000 : ℝ)*(major0) + (1489899107035167/50000000000000 : ℝ)*(major1) + (1489899107035167/50000000000000 : ℝ)*(major2) + (4090636428018859/100000000000000 : ℝ)*(sp0) + (511323438237209/12500000000000 : ℝ)*(sp1) + (818116375225061/20000000000000 : ℝ)*(sp2) + (233618814304869/12500000000000 : ℝ)*(sp3) + (1209823311/2500000000000 : ℝ)*(sp5) + (27275946777/50000000000000 : ℝ)*(sp6) + (4598954189/50000000000000 : ℝ)*(sp7) + (186895971234733/10000000000000 : ℝ)*(f.failure) + (4090636428018859/100000000000000 : ℝ)*(f.sum) + (278684888686819/53645000000000000000000000000 : ℝ)*base65 + (57483950224434502097/5364500000000000000000000000000000 : ℝ)*base68 + (29833730914962002097/5364500000000000000000000000000000 : ℝ)*base70 + (26208618429497997903/5364500000000000000000000000000000 : ℝ)*base71 + (64885934954453/26822500000000000000000000000 : ℝ)*base74 + (49963173389511997903/5364500000000000000000000000000000 : ℝ)*base75 + (56885454412070002097/5364500000000000000000000000000000 : ℝ)*base78 + (30855887782227502097/5364500000000000000000000000000000 : ℝ)*base80 + (38608274022707/26822500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1108531/1000000000000000000000 : ℝ)*base90 + (1108531/1000000000000000000000 : ℝ)*base92 + (1108531/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4451188598179970904277256481/670562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864578587/100000000000000 : ℝ)*(base19) + (4878563/1000000000000 : ℝ)*(base23) + (16638671/12500000000000 : ℝ)*(upper3) + (159392107/50000000000000 : ℝ)*(lower4) + (376663040019399/12500000000000 : ℝ)*(major0) + (376663040019399/12500000000000 : ℝ)*(major1) + (376663040019399/12500000000000 : ℝ)*(major2) + (599861871/25000000000000 : ℝ)*(sp0) + (7977255453/25000000000000 : ℝ)*(sp1) + (10373019067/100000000000000 : ℝ)*(sp3) + (1034157734279049/25000000000000 : ℝ)*(sp4) + (4136600562963281/100000000000000 : ℝ)*(sp5) + (206831642435369/5000000000000 : ℝ)*(sp6) + (1889964709461227/100000000000000 : ℝ)*(sp7) + (377995016496059/20000000000000 : ℝ)*(f.failure) + (25853958353523/625000000000 : ℝ)*(f.sum) + (11549452341443/13411250000000000000000000000 : ℝ)*base65 + (1866114274897585391/1341125000000000000000000000000000 : ℝ)*base67 + (3476984422650460391/1341125000000000000000000000000000 : ℝ)*base69 + (4689471069007085391/1341125000000000000000000000000000 : ℝ)*base71 + (2920016327467/3352812500000000000000000000 : ℝ)*base73 + (12856529235269585391/1341125000000000000000000000000000 : ℝ)*base75 + (1866165668148710391/1341125000000000000000000000000000 : ℝ)*base77 + (15248323623886085391/1341125000000000000000000000000000 : ℝ)*base79 + (43520821192741/26822500000000000000000000000 : ℝ)*base81 + (6463387/2000000000000000000000 : ℝ)*base89 + (6463387/2000000000000000000000 : ℝ)*base91 + (6463387/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1461_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2633/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7853/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1461_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1461_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2633/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7853/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1461_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1461_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1461_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1105/256 : ℝ) ≤ p) (hpb : p ≤ (4421/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159436193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2633/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7853/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1461_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

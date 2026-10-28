-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:06:26.424274+00:00
-- url     : https://prove2.me/submissions/ea544cc1-18de-495c-b2f2-16a280bd110e

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
theorem support_rectangle_w1113_s6_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180795591/10000000000 : ℝ)*x 0 + (134849091/250000000 : ℝ)*x 1 + (2632436633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180795591/10000000000 : ℝ)^4153 ≤ (13248580870993/100000000000000 : ℝ)^3129 := by
    have hnat : (2180795591 : ℕ)^4153*100000000000000^3129 ≤ 13248580870993^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180795591 10000000000 13248580870993 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134849091/250000000 : ℝ)^4153 ≤ (5509116393773/12500000000000 : ℝ)^3129 := by
    have hnat : (134849091 : ℕ)^4153*12500000000000^3129 ≤ 5509116393773^3129*250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134849091 250000000 5509116393773 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632436633/5000000000 : ℝ)^4153 ≤ (21339243980283/50000000000000 : ℝ)^3129 := by
    have hnat : (2632436633 : ℕ)^4153*50000000000000^3129 ≤ 21339243980283^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632436633 5000000000 21339243980283 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180795591/10000000000 : ℝ), (134849091/250000000 : ℝ), (2632436633/5000000000 : ℝ)] ![(13248580870993/100000000000000 : ℝ), (5509116393773/12500000000000 : ℝ), (21339243980283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180795591/10000000000 : ℝ)|^4153 ≤ (13248580870993/100000000000000 : ℝ)^3129
        have hw : |(-2180795591/10000000000 : ℝ)|=(2180795591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134849091/250000000 : ℝ)|^4153 ≤ (5509116393773/12500000000000 : ℝ)^3129
        have hw : |(134849091/250000000 : ℝ)|=(134849091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632436633/5000000000 : ℝ)|^4153 ≤ (21339243980283/50000000000000 : ℝ)^3129
        have hw : |(2632436633/5000000000 : ℝ)|=(2632436633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336239989/2500000000 : ℝ)*x 0 + (-112314287/500000000 : ℝ)*x 1 + (2632436641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336239989/2500000000 : ℝ)^4153 ≤ (5442786145837/12500000000000 : ℝ)^3129 := by
    have hnat : (1336239989 : ℕ)^4153*12500000000000^3129 ≤ 5442786145837^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336239989 2500000000 5442786145837 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112314287/500000000 : ℝ)^4153 ≤ (3444805672079/25000000000000 : ℝ)^3129 := by
    have hnat : (112314287 : ℕ)^4153*25000000000000^3129 ≤ 3444805672079^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112314287 500000000 3444805672079 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632436641/5000000000 : ℝ)^4153 ≤ (5334811016589/12500000000000 : ℝ)^3129 := by
    have hnat : (2632436641 : ℕ)^4153*12500000000000^3129 ≤ 5334811016589^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632436641 5000000000 5334811016589 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336239989/2500000000 : ℝ), (-112314287/500000000 : ℝ), (2632436641/5000000000 : ℝ)] ![(5442786145837/12500000000000 : ℝ), (3444805672079/25000000000000 : ℝ), (5334811016589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336239989/2500000000 : ℝ)|^4153 ≤ (5442786145837/12500000000000 : ℝ)^3129
        have hw : |(1336239989/2500000000 : ℝ)|=(1336239989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112314287/500000000 : ℝ)|^4153 ≤ (3444805672079/25000000000000 : ℝ)^3129
        have hw : |(-112314287/500000000 : ℝ)|=(112314287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632436641/5000000000 : ℝ)|^4153 ≤ (5334811016589/12500000000000 : ℝ)^3129
        have hw : |(2632436641/5000000000 : ℝ)|=(2632436641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672479971/5000000000 : ℝ)*x 0 + (1316218327/2500000000 : ℝ)*x 1 + (-89851429/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672479971/5000000000 : ℝ)^4153 ≤ (43542289015323/100000000000000 : ℝ)^3129 := by
    have hnat : (2672479971 : ℕ)^4153*100000000000000^3129 ≤ 43542289015323^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672479971 5000000000 43542289015323 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316218327/2500000000 : ℝ)^4153 ≤ (853569768249/2000000000000 : ℝ)^3129 := by
    have hnat : (1316218327 : ℕ)^4153*2000000000000^3129 ≤ 853569768249^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316218327 2500000000 853569768249 2000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89851429/400000000 : ℝ)^4153 ≤ (1377922256619/10000000000000 : ℝ)^3129 := by
    have hnat : (89851429 : ℕ)^4153*10000000000000^3129 ≤ 1377922256619^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89851429 400000000 1377922256619 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672479971/5000000000 : ℝ), (1316218327/2500000000 : ℝ), (-89851429/400000000 : ℝ)] ![(43542289015323/100000000000000 : ℝ), (853569768249/2000000000000 : ℝ), (1377922256619/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672479971/5000000000 : ℝ)|^4153 ≤ (43542289015323/100000000000000 : ℝ)^3129
        have hw : |(2672479971/5000000000 : ℝ)|=(2672479971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316218327/2500000000 : ℝ)|^4153 ≤ (853569768249/2000000000000 : ℝ)^3129
        have hw : |(1316218327/2500000000 : ℝ)|=(1316218327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89851429/400000000 : ℝ)|^4153 ≤ (1377922256619/10000000000000 : ℝ)^3129
        have hw : |(-89851429/400000000 : ℝ)|=(89851429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546094297/1250000000 : ℝ)*x 0 + (848588543/2000000000 : ℝ)*x 1 + (4498304553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546094297/1250000000 : ℝ)^4153 ≤ (33316599469227/100000000000000 : ℝ)^3129 := by
    have hnat : (546094297 : ℕ)^4153*100000000000000^3129 ≤ 33316599469227^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546094297 1250000000 33316599469227 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848588543/2000000000 : ℝ)^4153 ≤ (16024597076581/50000000000000 : ℝ)^3129 := by
    have hnat : (848588543 : ℕ)^4153*50000000000000^3129 ≤ 16024597076581^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848588543 2000000000 16024597076581 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498304553/10000000000 : ℝ)^4153 ≤ (34634206367757/100000000000000 : ℝ)^3129 := by
    have hnat : (4498304553 : ℕ)^4153*100000000000000^3129 ≤ 34634206367757^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498304553 10000000000 34634206367757 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546094297/1250000000 : ℝ), (848588543/2000000000 : ℝ), (4498304553/10000000000 : ℝ)] ![(33316599469227/100000000000000 : ℝ), (16024597076581/50000000000000 : ℝ), (34634206367757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546094297/1250000000 : ℝ)|^4153 ≤ (33316599469227/100000000000000 : ℝ)^3129
        have hw : |(546094297/1250000000 : ℝ)|=(546094297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848588543/2000000000 : ℝ)|^4153 ≤ (16024597076581/50000000000000 : ℝ)^3129
        have hw : |(848588543/2000000000 : ℝ)|=(848588543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498304553/10000000000 : ℝ)|^4153 ≤ (34634206367757/100000000000000 : ℝ)^3129
        have hw : |(4498304553/10000000000 : ℝ)|=(4498304553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109040033/500000000 : ℝ)*x 0 + (21060797/40000000 : ℝ)*x 1 + (1078727291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109040033/500000000 : ℝ)^4153 ≤ (13248621743683/100000000000000 : ℝ)^3129 := by
    have hnat : (109040033 : ℕ)^4153*100000000000000^3129 ≤ 13248621743683^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109040033 500000000 13248621743683 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21060797/40000000 : ℝ)^4153 ≤ (21340997651443/50000000000000 : ℝ)^3129 := by
    have hnat : (21060797 : ℕ)^4153*50000000000000^3129 ≤ 21340997651443^3129*40000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21060797 40000000 21340997651443 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078727291/2000000000 : ℝ)^4153 ≤ (44069382939799/100000000000000 : ℝ)^3129 := by
    have hnat : (1078727291 : ℕ)^4153*100000000000000^3129 ≤ 44069382939799^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078727291 2000000000 44069382939799 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109040033/500000000 : ℝ), (21060797/40000000 : ℝ), (1078727291/2000000000 : ℝ)] ![(13248621743683/100000000000000 : ℝ), (21340997651443/50000000000000 : ℝ), (44069382939799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109040033/500000000 : ℝ)|^4153 ≤ (13248621743683/100000000000000 : ℝ)^3129
        have hw : |(-109040033/500000000 : ℝ)|=(109040033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21060797/40000000 : ℝ)|^4153 ≤ (21340997651443/50000000000000 : ℝ)^3129
        have hw : |(21060797/40000000 : ℝ)|=(21060797/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078727291/2000000000 : ℝ)|^4153 ≤ (44069382939799/100000000000000 : ℝ)^3129
        have hw : |(1078727291/2000000000 : ℝ)|=(1078727291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265616279/500000000 : ℝ)*x 0 + (-1058761279/5000000000 : ℝ)*x 1 + (337102277/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265616279/500000000 : ℝ)^4153 ≤ (21594892692809/50000000000000 : ℝ)^3129 := by
    have hnat : (265616279 : ℕ)^4153*50000000000000^3129 ≤ 21594892692809^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265616279 500000000 21594892692809 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058761279/5000000000 : ℝ)^4153 ≤ (796301994713/6250000000000 : ℝ)^3129 := by
    have hnat : (1058761279 : ℕ)^4153*6250000000000^3129 ≤ 796301994713^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058761279 5000000000 796301994713 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337102277/625000000 : ℝ)^4153 ≤ (22034691345187/50000000000000 : ℝ)^3129 := by
    have hnat : (337102277 : ℕ)^4153*50000000000000^3129 ≤ 22034691345187^3129*625000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337102277 625000000 22034691345187 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265616279/500000000 : ℝ), (-1058761279/5000000000 : ℝ), (337102277/625000000 : ℝ)] ![(21594892692809/50000000000000 : ℝ), (796301994713/6250000000000 : ℝ), (22034691345187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265616279/500000000 : ℝ)|^4153 ≤ (21594892692809/50000000000000 : ℝ)^3129
        have hw : |(265616279/500000000 : ℝ)|=(265616279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058761279/5000000000 : ℝ)|^4153 ≤ (796301994713/6250000000000 : ℝ)^3129
        have hw : |(-1058761279/5000000000 : ℝ)|=(1058761279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337102277/625000000 : ℝ)|^4153 ≤ (22034691345187/50000000000000 : ℝ)^3129
        have hw : |(337102277/625000000 : ℝ)|=(337102277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656162799/5000000000 : ℝ)*x 0 + (2696818201/5000000000 : ℝ)*x 1 + (-84700903/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656162799/5000000000 : ℝ)^4153 ≤ (10797446394963/25000000000000 : ℝ)^3129 := by
    have hnat : (2656162799 : ℕ)^4153*25000000000000^3129 ≤ 10797446394963^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656162799 5000000000 10797446394963 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696818201/5000000000 : ℝ)^4153 ≤ (44069382365037/100000000000000 : ℝ)^3129 := by
    have hnat : (2696818201 : ℕ)^4153*100000000000000^3129 ≤ 44069382365037^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696818201 5000000000 44069382365037 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84700903/400000000 : ℝ)^4153 ≤ (12740832051169/100000000000000 : ℝ)^3129 := by
    have hnat : (84700903 : ℕ)^4153*100000000000000^3129 ≤ 12740832051169^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84700903 400000000 12740832051169 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656162799/5000000000 : ℝ), (2696818201/5000000000 : ℝ), (-84700903/400000000 : ℝ)] ![(10797446394963/25000000000000 : ℝ), (44069382365037/100000000000000 : ℝ), (12740832051169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656162799/5000000000 : ℝ)|^4153 ≤ (10797446394963/25000000000000 : ℝ)^3129
        have hw : |(2656162799/5000000000 : ℝ)|=(2656162799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696818201/5000000000 : ℝ)|^4153 ≤ (44069382365037/100000000000000 : ℝ)^3129
        have hw : |(2696818201/5000000000 : ℝ)|=(2696818201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84700903/400000000 : ℝ)|^4153 ≤ (12740832051169/100000000000000 : ℝ)^3129
        have hw : |(-84700903/400000000 : ℝ)|=(84700903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s6_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436876433/1000000000 : ℝ)*x 0 + (2248829847/5000000000 : ℝ)*x 1 + (848717989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436876433/1000000000 : ℝ)^4153 ≤ (16658350111023/50000000000000 : ℝ)^3129 := by
    have hnat : (436876433 : ℕ)^4153*50000000000000^3129 ≤ 16658350111023^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436876433 1000000000 16658350111023 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248829847/5000000000 : ℝ)^4153 ≤ (17313808321081/50000000000000 : ℝ)^3129 := by
    have hnat : (2248829847 : ℕ)^4153*50000000000000^3129 ≤ 17313808321081^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248829847 5000000000 17313808321081 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848717989/2000000000 : ℝ)^4153 ≤ (8013920780889/25000000000000 : ℝ)^3129 := by
    have hnat : (848717989 : ℕ)^4153*25000000000000^3129 ≤ 8013920780889^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848717989 2000000000 8013920780889 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436876433/1000000000 : ℝ), (2248829847/5000000000 : ℝ), (848717989/2000000000 : ℝ)] ![(16658350111023/50000000000000 : ℝ), (17313808321081/50000000000000 : ℝ), (8013920780889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436876433/1000000000 : ℝ)|^4153 ≤ (16658350111023/50000000000000 : ℝ)^3129
        have hw : |(436876433/1000000000 : ℝ)|=(436876433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248829847/5000000000 : ℝ)|^4153 ≤ (17313808321081/50000000000000 : ℝ)^3129
        have hw : |(2248829847/5000000000 : ℝ)|=(2248829847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848717989/2000000000 : ℝ)|^4153 ≤ (8013920780889/25000000000000 : ℝ)^3129
        have hw : |(848717989/2000000000 : ℝ)|=(848717989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14041/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (8305/2048 : ℝ) ≤ (14311901344118869/100000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^8305 ≤ (14311901344118869/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8305*100000000000000000000^2048 ≤ 14311901344118869^2048*12500^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 14311901344118869 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (14311901344118869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (35241860078583517/100000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^8305 ≤ (35241860078583517/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14077 : ℕ)^8305*100000000000000000000^2048 ≤ 35241860078583517^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 35241860078583517 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (35241860078583517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014311901344118869/50000000000000000000 : ℝ) ≤ (2000141156479303/2000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50014311901344118869/50000000000000000000 : ℝ)^2048 ≤ (2000141156479303/2000000000000000 : ℝ)^8305 := by
      have hnat : (50014311901344118869 : ℕ)^2048*2000000000000000^8305 ≤ 2000141156479303^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014311901344118869 50000000000000000000 2000141156479303 2000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000141156479303/2000000000000000 : ℝ)) (X := (50014311901344118869/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024776880711351193/50000000000000000000 : ℝ) ≤ (625076359997387/625000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50024776880711351193/50000000000000000000 : ℝ)^2048 ≤ (625076359997387/625000000000000 : ℝ)^8305 := by
      have hnat : (50024776880711351193 : ℕ)^2048*625000000000000^8305 ≤ 625076359997387^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024776880711351193 50000000000000000000 625076359997387 625000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625076359997387/625000000000000 : ℝ)) (X := (50024776880711351193/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035241860078583517/50000000000000000000 : ℝ) ≤ (10001737737519869/10000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50035241860078583517/50000000000000000000 : ℝ)^2048 ≤ (10001737737519869/10000000000000000 : ℝ)^8305 := by
      have hnat : (50035241860078583517 : ℕ)^2048*10000000000000000^8305 ≤ 10001737737519869^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035241860078583517 50000000000000000000 10001737737519869 10000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001737737519869/10000000000000000 : ℝ)) (X := (50035241860078583517/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14311901344118869/100000000000000000000 : ℝ) ≤ ((9346782507157259429/9350000000000000000 : ℝ)+2*(171992520559/93500000000000 : ℝ)*(1409/12500 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (9346782507157259429/9350000000000000000 : ℝ)+2*(171992520559/93500000000000 : ℝ)*(1409/12500 : ℝ)=(2000141156479303/2000000000000000 : ℝ) by norm_num, show 1+2*(14311901344118869/100000000000000000000 : ℝ)=(50014311901344118869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35241860078583517/100000000000000000000 : ℝ)+(14311901344118869/100000000000000000000 : ℝ) ≤ ((9346782507157259429/9350000000000000000 : ℝ)+(171992520559/93500000000000 : ℝ)*((14077/100000 : ℝ)+(1409/12500 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (9346782507157259429/9350000000000000000 : ℝ)+(171992520559/93500000000000 : ℝ)*((14077/100000 : ℝ)+(1409/12500 : ℝ))=(625076359997387/625000000000000 : ℝ) by norm_num, show 1+(35241860078583517/100000000000000000000 : ℝ)+(14311901344118869/100000000000000000000 : ℝ)=(50024776880711351193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35241860078583517/100000000000000000000 : ℝ) ≤ ((9346782507157259429/9350000000000000000 : ℝ)+2*(171992520559/93500000000000 : ℝ)*(14077/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (9346782507157259429/9350000000000000000 : ℝ)+2*(171992520559/93500000000000 : ℝ)*(14077/100000 : ℝ)=(10001737737519869/10000000000000000 : ℝ) by norm_num, show 1+2*(35241860078583517/100000000000000000000 : ℝ)=(50035241860078583517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9346782507157259429/9350000000000000000 : ℝ)*(X 1 0+X 2 0)+(171992520559/93500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (9346782507157259429/9350000000000000000 : ℝ)) (alpha := (171992520559/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9346782507157259429/9350000000000000000 : ℝ)*(X 0 1+X 2 1)+(171992520559/93500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (9346782507157259429/9350000000000000000 : ℝ)) (alpha := (171992520559/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9346782507157259429/9350000000000000000 : ℝ)*(X 0 2+X 1 2)+(171992520559/93500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (9346782507157259429/9350000000000000000 : ℝ)) (alpha := (171992520559/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2180795591/10000000000 : ℝ)*X 0 0+(134849091/250000000 : ℝ)*X 0 1+(2632436633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336239989/2500000000 : ℝ)*X 1 0+(-112314287/500000000 : ℝ)*X 1 1+(2632436641/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672479971/5000000000 : ℝ)*X 2 0+(1316218327/2500000000 : ℝ)*X 2 1+(-89851429/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546094297/1250000000 : ℝ)*X 0 0+(848588543/2000000000 : ℝ)*X 0 1+(4498304553/10000000000 : ℝ)*X 0 2+(546094297/1250000000 : ℝ)*X 1 0+(848588543/2000000000 : ℝ)*X 1 1+(4498304553/10000000000 : ℝ)*X 1 2+(546094297/1250000000 : ℝ)*X 2 0+(848588543/2000000000 : ℝ)*X 2 1+(4498304553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109040033/500000000 : ℝ)*X 0 0+(21060797/40000000 : ℝ)*X 0 1+(1078727291/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265616279/500000000 : ℝ)*X 1 0+(-1058761279/5000000000 : ℝ)*X 1 1+(337102277/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656162799/5000000000 : ℝ)*X 2 0+(2696818201/5000000000 : ℝ)*X 2 1+(-84700903/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436876433/1000000000 : ℝ)*X 0 0+(2248829847/5000000000 : ℝ)*X 0 1+(848717989/2000000000 : ℝ)*X 0 2+(436876433/1000000000 : ℝ)*X 1 0+(2248829847/5000000000 : ℝ)*X 1 1+(848717989/2000000000 : ℝ)*X 1 2+(436876433/1000000000 : ℝ)*X 2 0+(2248829847/5000000000 : ℝ)*X 2 1+(848717989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236989984426853003289344499/116875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (434023023/100000000000000 : ℝ)*(base19) + (44601163/12500000000000 : ℝ)*(base23) + (1217011/4000000000000 : ℝ)*(lower2) + (14857489/25000000000000 : ℝ)*(upper3) + (9411989/25000000000000 : ℝ)*(upper5) + (2915639812267723/50000000000000 : ℝ)*(major0) + (2915639812267723/50000000000000 : ℝ)*(major1) + (2915639812267723/50000000000000 : ℝ)*(major2) + (3873261821985453/50000000000000 : ℝ)*(sp0) + (3873267758902817/50000000000000 : ℝ)*(sp1) + (3873267797509677/50000000000000 : ℝ)*(sp2) + (489502155286889/12500000000000 : ℝ)*(sp3) + (12307857751/100000000000000 : ℝ)*(sp4) + (2993678193/50000000000000 : ℝ)*(sp7) + (3916023229651497/100000000000000 : ℝ)*(f.failure) + (3873267975914329/50000000000000 : ℝ)*(f.sum) + (8346348830059/1168750000000000000000000000 : ℝ)*base66 + (1763397320534810167/467500000000000000000000000000000 : ℝ)*base67 + (6265639309257310167/467500000000000000000000000000000 : ℝ)*base69 + (5190006805899810167/467500000000000000000000000000000 : ℝ)*base71 + (25192842074693/2337500000000000000000000000 : ℝ)*base74 + (226327063915189833/467500000000000000000000000000000 : ℝ)*base76 + (8404758698229810167/467500000000000000000000000000000 : ℝ)*base77 + (471106498899810167/467500000000000000000000000000000 : ℝ)*base79 + (8201802938743/2337500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6863797/5000000000000000000000 : ℝ)*base90 + (6863797/5000000000000000000000 : ℝ)*base92 + (6863797/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1697317510170145618464570387/233750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (752866921/50000000000000 : ℝ)*(base19) + (321135609/20000000000000 : ℝ)*(base23) + (139240881/100000000000000 : ℝ)*(upper3) + (39694091/100000000000000 : ℝ)*(lower4) + (5478251/3125000000000 : ℝ)*(upper5) + (2930458275788301/50000000000000 : ℝ)*(major0) + (2930458275788301/50000000000000 : ℝ)*(major1) + (2930458275788301/50000000000000 : ℝ)*(major2) + (41661553293/100000000000000 : ℝ)*(sp1) + (20736555167/50000000000000 : ℝ)*(sp2) + (7785906813858799/100000000000000 : ℝ)*(sp4) + (486616477910729/6250000000000 : ℝ)*(sp5) + (389293186753521/5000000000000 : ℝ)*(sp6) + (1967963023626343/50000000000000 : ℝ)*(sp7) + (1967963023626343/50000000000000 : ℝ)*(f.failure) + (7785906813858799/100000000000000 : ℝ)*(f.sum) + (709682574259/2337500000000000000000000000 : ℝ)*base65 + (3120738337128959871/467500000000000000000000000000000 : ℝ)*base68 + (2676202395746459871/467500000000000000000000000000000 : ℝ)*base70 + (1677517208526040129/467500000000000000000000000000000 : ℝ)*base71 + (13241491490041/2337500000000000000000000000 : ℝ)*base74 + (7479841065053959871/467500000000000000000000000000000 : ℝ)*base76 + (3960323145773959871/467500000000000000000000000000000 : ℝ)*base78 + (1339074703136040129/467500000000000000000000000000000 : ℝ)*base79 + (3772346468991/2337500000000000000000000000 : ℝ)*base82 + (30729957/2500000000000000000000 : ℝ)*base89 + (30729957/2500000000000000000000 : ℝ)*base91 + (30729957/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1113_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s7_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180825737/10000000000 : ℝ)*x 0 + (5393593687/10000000000 : ℝ)*x 1 + (5265223563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180825737/10000000000 : ℝ)^4153 ≤ (13248823946637/100000000000000 : ℝ)^3129 := by
    have hnat : (2180825737 : ℕ)^4153*100000000000000^3129 ≤ 13248823946637^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180825737 10000000000 13248823946637 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393593687/10000000000 : ℝ)^4153 ≤ (22034459570273/50000000000000 : ℝ)^3129 := by
    have hnat : (5393593687 : ℕ)^4153*50000000000000^3129 ≤ 22034459570273^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393593687 10000000000 22034459570273 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265223563/10000000000 : ℝ)^4153 ≤ (21341128447651/50000000000000 : ℝ)^3129 := by
    have hnat : (5265223563 : ℕ)^4153*50000000000000^3129 ≤ 21341128447651^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265223563 10000000000 21341128447651 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180825737/10000000000 : ℝ), (5393593687/10000000000 : ℝ), (5265223563/10000000000 : ℝ)] ![(13248823946637/100000000000000 : ℝ), (22034459570273/50000000000000 : ℝ), (21341128447651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180825737/10000000000 : ℝ)|^4153 ≤ (13248823946637/100000000000000 : ℝ)^3129
        have hw : |(-2180825737/10000000000 : ℝ)|=(2180825737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393593687/10000000000 : ℝ)|^4153 ≤ (22034459570273/50000000000000 : ℝ)^3129
        have hw : |(5393593687/10000000000 : ℝ)|=(5393593687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265223563/10000000000 : ℝ)|^4153 ≤ (21341128447651/50000000000000 : ℝ)^3129
        have hw : |(5265223563/10000000000 : ℝ)|=(5265223563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068973553/2000000000 : ℝ)*x 0 + (-1122972627/5000000000 : ℝ)*x 1 + (5265223573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068973553/2000000000 : ℝ)^4153 ≤ (8708258472219/20000000000000 : ℝ)^3129 := by
    have hnat : (1068973553 : ℕ)^4153*20000000000000^3129 ≤ 8708258472219^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068973553 2000000000 8708258472219 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122972627/5000000000 : ℝ)^4153 ≤ (13776450615883/100000000000000 : ℝ)^3129 := by
    have hnat : (1122972627 : ℕ)^4153*100000000000000^3129 ≤ 13776450615883^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122972627 5000000000 13776450615883 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265223573/10000000000 : ℝ)^4153 ≤ (2667641062681/6250000000000 : ℝ)^3129 := by
    have hnat : (5265223573 : ℕ)^4153*6250000000000^3129 ≤ 2667641062681^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265223573 10000000000 2667641062681 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068973553/2000000000 : ℝ), (-1122972627/5000000000 : ℝ), (5265223573/10000000000 : ℝ)] ![(8708258472219/20000000000000 : ℝ), (13776450615883/100000000000000 : ℝ), (2667641062681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068973553/2000000000 : ℝ)|^4153 ≤ (8708258472219/20000000000000 : ℝ)^3129
        have hw : |(1068973553/2000000000 : ℝ)|=(1068973553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122972627/5000000000 : ℝ)|^4153 ≤ (13776450615883/100000000000000 : ℝ)^3129
        have hw : |(-1122972627/5000000000 : ℝ)|=(1122972627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265223573/10000000000 : ℝ)|^4153 ≤ (2667641062681/6250000000000 : ℝ)^3129
        have hw : |(5265223573/10000000000 : ℝ)|=(5265223573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344867769/10000000000 : ℝ)*x 0 + (210608943/400000000 : ℝ)*x 1 + (-1122972623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344867769/10000000000 : ℝ)^4153 ≤ (5442661550543/12500000000000 : ℝ)^3129 := by
    have hnat : (5344867769 : ℕ)^4153*12500000000000^3129 ≤ 5442661550543^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344867769 10000000000 5442661550543 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210608943/400000000 : ℝ)^4153 ≤ (21341128512207/50000000000000 : ℝ)^3129 := by
    have hnat : (210608943 : ℕ)^4153*50000000000000^3129 ≤ 21341128512207^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210608943 400000000 21341128512207 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122972623/5000000000 : ℝ)^4153 ≤ (430514079711/3125000000000 : ℝ)^3129 := by
    have hnat : (1122972623 : ℕ)^4153*3125000000000^3129 ≤ 430514079711^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122972623 5000000000 430514079711 3125000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344867769/10000000000 : ℝ), (210608943/400000000 : ℝ), (-1122972623/5000000000 : ℝ)] ![(5442661550543/12500000000000 : ℝ), (21341128512207/50000000000000 : ℝ), (430514079711/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344867769/10000000000 : ℝ)|^4153 ≤ (5442661550543/12500000000000 : ℝ)^3129
        have hw : |(5344867769/10000000000 : ℝ)|=(5344867769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210608943/400000000 : ℝ)|^4153 ≤ (21341128512207/50000000000000 : ℝ)^3129
        have hw : |(210608943/400000000 : ℝ)|=(210608943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122972623/5000000000 : ℝ)|^4153 ≤ (430514079711/3125000000000 : ℝ)^3129
        have hw : |(-1122972623/5000000000 : ℝ)|=(1122972623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174750909/400000000 : ℝ)*x 0 + (1060913177/2500000000 : ℝ)*x 1 + (2248794899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174750909/400000000 : ℝ)^4153 ≤ (33316785194971/100000000000000 : ℝ)^3129 := by
    have hnat : (174750909 : ℕ)^4153*100000000000000^3129 ≤ 33316785194971^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174750909 400000000 33316785194971 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060913177/2500000000 : ℝ)^4153 ≤ (32056312387341/100000000000000 : ℝ)^3129 := by
    have hnat : (1060913177 : ℕ)^4153*100000000000000^3129 ≤ 32056312387341^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060913177 2500000000 32056312387341 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248794899/5000000000 : ℝ)^4153 ≤ (17313451201553/50000000000000 : ℝ)^3129 := by
    have hnat : (2248794899 : ℕ)^4153*50000000000000^3129 ≤ 17313451201553^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248794899 5000000000 17313451201553 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174750909/400000000 : ℝ), (1060913177/2500000000 : ℝ), (2248794899/5000000000 : ℝ)] ![(33316785194971/100000000000000 : ℝ), (32056312387341/100000000000000 : ℝ), (17313451201553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174750909/400000000 : ℝ)|^4153 ≤ (33316785194971/100000000000000 : ℝ)^3129
        have hw : |(174750909/400000000 : ℝ)|=(174750909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060913177/2500000000 : ℝ)|^4153 ≤ (32056312387341/100000000000000 : ℝ)^3129
        have hw : |(1060913177/2500000000 : ℝ)|=(1060913177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248794899/5000000000 : ℝ)|^4153 ≤ (17313451201553/50000000000000 : ℝ)^3129
        have hw : |(2248794899/5000000000 : ℝ)|=(2248794899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136301919/625000000 : ℝ)*x 0 + (658193237/1250000000 : ℝ)*x 1 + (1078654037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136301919/625000000 : ℝ)^4153 ≤ (2649772799411/20000000000000 : ℝ)^3129 := by
    have hnat : (136301919 : ℕ)^4153*20000000000000^3129 ≤ 2649772799411^3129*625000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136301919 625000000 2649772799411 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658193237/1250000000 : ℝ)^4153 ≤ (5335715628841/12500000000000 : ℝ)^3129 := by
    have hnat : (658193237 : ℕ)^4153*12500000000000^3129 ≤ 5335715628841^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658193237 1250000000 5335715628841 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078654037/2000000000 : ℝ)^4153 ≤ (11016352737351/25000000000000 : ℝ)^3129 := by
    have hnat : (1078654037 : ℕ)^4153*25000000000000^3129 ≤ 11016352737351^3129*2000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078654037 2000000000 11016352737351 25000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136301919/625000000 : ℝ), (658193237/1250000000 : ℝ), (1078654037/2000000000 : ℝ)] ![(2649772799411/20000000000000 : ℝ), (5335715628841/12500000000000 : ℝ), (11016352737351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136301919/625000000 : ℝ)|^4153 ≤ (2649772799411/20000000000000 : ℝ)^3129
        have hw : |(-136301919/625000000 : ℝ)|=(136301919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658193237/1250000000 : ℝ)|^4153 ≤ (5335715628841/12500000000000 : ℝ)^3129
        have hw : |(658193237/1250000000 : ℝ)|=(658193237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078654037/2000000000 : ℝ)|^4153 ≤ (11016352737351/25000000000000 : ℝ)^3129
        have hw : |(1078654037/2000000000 : ℝ)|=(1078654037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312415309/10000000000 : ℝ)*x 0 + (-1058949317/5000000000 : ℝ)*x 1 + (337079387/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312415309/10000000000 : ℝ)^4153 ≤ (863815072679/2000000000000 : ℝ)^3129 := by
    have hnat : (5312415309 : ℕ)^4153*2000000000000^3129 ≤ 863815072679^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312415309 10000000000 863815072679 2000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058949317/5000000000 : ℝ)^4153 ≤ (12743835323511/100000000000000 : ℝ)^3129 := by
    have hnat : (1058949317 : ℕ)^4153*100000000000000^3129 ≤ 12743835323511^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058949317 5000000000 12743835323511 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337079387/625000000 : ℝ)^4153 ≤ (8813082205063/20000000000000 : ℝ)^3129 := by
    have hnat : (337079387 : ℕ)^4153*20000000000000^3129 ≤ 8813082205063^3129*625000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337079387 625000000 8813082205063 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312415309/10000000000 : ℝ), (-1058949317/5000000000 : ℝ), (337079387/625000000 : ℝ)] ![(863815072679/2000000000000 : ℝ), (12743835323511/100000000000000 : ℝ), (8813082205063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312415309/10000000000 : ℝ)|^4153 ≤ (863815072679/2000000000000 : ℝ)^3129
        have hw : |(5312415309/10000000000 : ℝ)|=(5312415309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058949317/5000000000 : ℝ)|^4153 ≤ (12743835323511/100000000000000 : ℝ)^3129
        have hw : |(-1058949317/5000000000 : ℝ)|=(1058949317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337079387/625000000 : ℝ)|^4153 ≤ (8813082205063/20000000000000 : ℝ)^3129
        have hw : |(337079387/625000000 : ℝ)|=(337079387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312415331/10000000000 : ℝ)*x 0 + (168539693/312500000 : ℝ)*x 1 + (-1058949313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312415331/10000000000 : ℝ)^4153 ≤ (43190753871349/100000000000000 : ℝ)^3129 := by
    have hnat : (5312415331 : ℕ)^4153*100000000000000^3129 ≤ 43190753871349^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312415331 10000000000 43190753871349 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168539693/312500000 : ℝ)^4153 ≤ (22032705425903/50000000000000 : ℝ)^3129 := by
    have hnat : (168539693 : ℕ)^4153*50000000000000^3129 ≤ 22032705425903^3129*312500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168539693 312500000 22032705425903 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058949313/5000000000 : ℝ)^4153 ≤ (12743835259619/100000000000000 : ℝ)^3129 := by
    have hnat : (1058949313 : ℕ)^4153*100000000000000^3129 ≤ 12743835259619^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058949313 5000000000 12743835259619 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312415331/10000000000 : ℝ), (168539693/312500000 : ℝ), (-1058949313/5000000000 : ℝ)] ![(43190753871349/100000000000000 : ℝ), (22032705425903/50000000000000 : ℝ), (12743835259619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312415331/10000000000 : ℝ)|^4153 ≤ (43190753871349/100000000000000 : ℝ)^3129
        have hw : |(5312415331/10000000000 : ℝ)|=(5312415331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168539693/312500000 : ℝ)|^4153 ≤ (22032705425903/50000000000000 : ℝ)^3129
        have hw : |(168539693/312500000 : ℝ)|=(168539693/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058949313/5000000000 : ℝ)|^4153 ≤ (12743835259619/100000000000000 : ℝ)^3129
        have hw : |(-1058949313/5000000000 : ℝ)|=(1058949313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s7_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (87375651/200000000 : ℝ)*x 0 + (1124238047/2500000000 : ℝ)*x 1 + (4244292611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87375651/200000000 : ℝ)^4153 ≤ (33316884642209/100000000000000 : ℝ)^3129 := by
    have hnat : (87375651 : ℕ)^4153*100000000000000^3129 ≤ 33316884642209^3129*200000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87375651 200000000 33316884642209 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124238047/2500000000 : ℝ)^4153 ≤ (2163774193199/6250000000000 : ℝ)^3129 := by
    have hnat : (1124238047 : ℕ)^4153*6250000000000^3129 ≤ 2163774193199^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124238047 2500000000 2163774193199 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244292611/10000000000 : ℝ)^4153 ≤ (16031364124243/50000000000000 : ℝ)^3129 := by
    have hnat : (4244292611 : ℕ)^4153*50000000000000^3129 ≤ 16031364124243^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244292611 10000000000 16031364124243 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87375651/200000000 : ℝ), (1124238047/2500000000 : ℝ), (4244292611/10000000000 : ℝ)] ![(33316884642209/100000000000000 : ℝ), (2163774193199/6250000000000 : ℝ), (16031364124243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87375651/200000000 : ℝ)|^4153 ≤ (33316884642209/100000000000000 : ℝ)^3129
        have hw : |(87375651/200000000 : ℝ)|=(87375651/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124238047/2500000000 : ℝ)|^4153 ≤ (2163774193199/6250000000000 : ℝ)^3129
        have hw : |(1124238047/2500000000 : ℝ)|=(1124238047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244292611/10000000000 : ℝ)|^4153 ≤ (16031364124243/50000000000000 : ℝ)^3129
        have hw : |(4244292611/10000000000 : ℝ)|=(4244292611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (3623241484150359/25000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^8305 ≤ (3623241484150359/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11307 : ℕ)^8305*25000000000000000000^2048 ≤ 3623241484150359^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 3623241484150359 25000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (3623241484150359/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14041/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (34877807641163093/100000000000000000000 : ℝ) := by
    have hpowers : (14041/100000 : ℝ)^8305 ≤ (34877807641163093/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14041 : ℕ)^8305*100000000000000000000^2048 ≤ 34877807641163093^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14041 100000 34877807641163093 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14041/100000 : ℝ)) (X := (34877807641163093/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503623241484150359/12500000000000000000 : ℝ) ≤ (5000357355254027/5000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (12503623241484150359/12500000000000000000 : ℝ)^2048 ≤ (5000357355254027/5000000000000000 : ℝ)^8305 := by
      have hnat : (12503623241484150359 : ℕ)^2048*5000000000000000^8305 ≤ 5000357355254027^8305*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503623241484150359 12500000000000000000 5000357355254027 5000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357355254027/5000000000000000 : ℝ)) (X := (12503623241484150359/12500000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049370773577764529/100000000000000000000 : ℝ) ≤ (5000608624593707/5000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (100049370773577764529/100000000000000000000 : ℝ)^2048 ≤ (5000608624593707/5000000000000000 : ℝ)^8305 := by
      have hnat : (100049370773577764529 : ℕ)^2048*5000000000000000^8305 ≤ 5000608624593707^8305*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049370773577764529 100000000000000000000 5000608624593707 5000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000608624593707/5000000000000000 : ℝ)) (X := (100049370773577764529/100000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034877807641163093/50000000000000000000 : ℝ) ≤ (5000859893933387/5000000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50034877807641163093/50000000000000000000 : ℝ)^2048 ≤ (5000859893933387/5000000000000000 : ℝ)^8305 := by
      have hnat : (50034877807641163093 : ℕ)^2048*5000000000000000^8305 ≤ 5000859893933387^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034877807641163093 50000000000000000000 5000859893933387 5000000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000859893933387/5000000000000000 : ℝ)) (X := (50034877807641163093/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3623241484150359/25000000000000000000 : ℝ) ≤ ((6832647402208493149/6835000000000000000 : ℝ)+2*(1570433373/854375000000 : ℝ)*(11307/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (6832647402208493149/6835000000000000000 : ℝ)+2*(1570433373/854375000000 : ℝ)*(11307/100000 : ℝ)=(5000357355254027/5000000000000000 : ℝ) by norm_num, show 1+2*(3623241484150359/25000000000000000000 : ℝ)=(12503623241484150359/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34877807641163093/100000000000000000000 : ℝ)+(3623241484150359/25000000000000000000 : ℝ) ≤ ((6832647402208493149/6835000000000000000 : ℝ)+(1570433373/854375000000 : ℝ)*((14041/100000 : ℝ)+(11307/100000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (6832647402208493149/6835000000000000000 : ℝ)+(1570433373/854375000000 : ℝ)*((14041/100000 : ℝ)+(11307/100000 : ℝ))=(5000608624593707/5000000000000000 : ℝ) by norm_num, show 1+(34877807641163093/100000000000000000000 : ℝ)+(3623241484150359/25000000000000000000 : ℝ)=(100049370773577764529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34877807641163093/100000000000000000000 : ℝ) ≤ ((6832647402208493149/6835000000000000000 : ℝ)+2*(1570433373/854375000000 : ℝ)*(14041/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (6832647402208493149/6835000000000000000 : ℝ)+2*(1570433373/854375000000 : ℝ)*(14041/100000 : ℝ)=(5000859893933387/5000000000000000 : ℝ) by norm_num, show 1+2*(34877807641163093/100000000000000000000 : ℝ)=(50034877807641163093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6832647402208493149/6835000000000000000 : ℝ)*(X 1 0+X 2 0)+(1570433373/854375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6832647402208493149/6835000000000000000 : ℝ)) (alpha := (1570433373/854375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6832647402208493149/6835000000000000000 : ℝ)*(X 0 1+X 2 1)+(1570433373/854375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6832647402208493149/6835000000000000000 : ℝ)) (alpha := (1570433373/854375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6832647402208493149/6835000000000000000 : ℝ)*(X 0 2+X 1 2)+(1570433373/854375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6832647402208493149/6835000000000000000 : ℝ)) (alpha := (1570433373/854375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2180825737/10000000000 : ℝ)*X 0 0+(5393593687/10000000000 : ℝ)*X 0 1+(5265223563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068973553/2000000000 : ℝ)*X 1 0+(-1122972627/5000000000 : ℝ)*X 1 1+(5265223573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344867769/10000000000 : ℝ)*X 2 0+(210608943/400000000 : ℝ)*X 2 1+(-1122972623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174750909/400000000 : ℝ)*X 0 0+(1060913177/2500000000 : ℝ)*X 0 1+(2248794899/5000000000 : ℝ)*X 0 2+(174750909/400000000 : ℝ)*X 1 0+(1060913177/2500000000 : ℝ)*X 1 1+(2248794899/5000000000 : ℝ)*X 1 2+(174750909/400000000 : ℝ)*X 2 0+(1060913177/2500000000 : ℝ)*X 2 1+(2248794899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136301919/625000000 : ℝ)*X 0 0+(658193237/1250000000 : ℝ)*X 0 1+(1078654037/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312415309/10000000000 : ℝ)*X 1 0+(-1058949317/5000000000 : ℝ)*X 1 1+(337079387/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312415331/10000000000 : ℝ)*X 2 0+(168539693/312500000 : ℝ)*X 2 1+(-1058949313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87375651/200000000 : ℝ)*X 0 0+(1124238047/2500000000 : ℝ)*X 0 1+(4244292611/10000000000 : ℝ)*X 0 2+(87375651/200000000 : ℝ)*X 1 0+(1124238047/2500000000 : ℝ)*X 1 1+(4244292611/10000000000 : ℝ)*X 1 2+(87375651/200000000 : ℝ)*X 2 0+(1124238047/2500000000 : ℝ)*X 2 1+(4244292611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4276397885039081191269/683500000000000000000000000 : ℝ) := by norm_num
    linear_combination (25160277/2000000000000 : ℝ)*(base19) + (119036341/10000000000000 : ℝ)*(base23) + (19637141/50000000000000 : ℝ)*(lower2) + (75643079/50000000000000 : ℝ)*(upper3) + (55287969/50000000000000 : ℝ)*(upper5) + (5864032188114463/100000000000000 : ℝ)*(major0) + (5864032188114463/100000000000000 : ℝ)*(major1) + (5864032188114463/100000000000000 : ℝ)*(major2) + (7790010489075323/100000000000000 : ℝ)*(sp0) + (7790044542052907/100000000000000 : ℝ)*(sp1) + (7790044609703347/100000000000000 : ℝ)*(sp2) + (3938000124060729/100000000000000 : ℝ)*(sp3) + (17655495717/50000000000000 : ℝ)*(sp4) + (9121773761/50000000000000 : ℝ)*(sp7) + (984504591902063/25000000000000 : ℝ)*(f.failure) + (7790045800066757/100000000000000 : ℝ)*(f.sum) + (1745135423211/683500000000000000000000000 : ℝ)*base65 + (6515191032700186013/683500000000000000000000000000000 : ℝ)*base68 + (3876667242334813987/683500000000000000000000000000000 : ℝ)*base69 + (8152666032275313987/683500000000000000000000000000000 : ℝ)*base71 + (1065976432869/683500000000000000000000000 : ℝ)*base73 + (14731993156127186013/683500000000000000000000000000000 : ℝ)*base76 + (1746382439522686013/683500000000000000000000000000000 : ℝ)*base78 + (5247389603839813987/683500000000000000000000000000000 : ℝ)*base79 + (5955574515097/683500000000000000000000000 : ℝ)*base81 + (9406237/1250000000000000000000 : ℝ)*base89 + (9406237/1250000000000000000000 : ℝ)*base91 + (9406237/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (441879869404298689986537243/85437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (203287691/20000000000000 : ℝ)*(base19) + (1121114241/100000000000000 : ℝ)*(base23) + (111532703/100000000000000 : ℝ)*(upper3) + (6228797/20000000000000 : ℝ)*(lower4) + (11557603/10000000000000 : ℝ)*(upper5) + (1473407356553269/25000000000000 : ℝ)*(major0) + (1473407356553269/25000000000000 : ℝ)*(major1) + (1473407356553269/25000000000000 : ℝ)*(major2) + (28286071811/100000000000000 : ℝ)*(sp1) + (15258451653/50000000000000 : ℝ)*(sp2) + (782936414811367/10000000000000 : ℝ)*(sp4) + (1957333711400851/25000000000000 : ℝ)*(sp5) + (1957333127524031/25000000000000 : ℝ)*(sp6) + (1236842041223/31250000000 : ℝ)*(sp7) + (1236842041223/31250000000 : ℝ)*(f.failure) + (782936414811367/10000000000000 : ℝ)*(f.sum) + (110521348697/42718750000000000000000000 : ℝ)*base66 + (430578228093945919/170875000000000000000000000000000 : ℝ)*base68 + (1184851821695195919/170875000000000000000000000000000 : ℝ)*base70 + (21521286646429081/170875000000000000000000000000000 : ℝ)*base71 + (3355028970877/683500000000000000000000000 : ℝ)*base74 + (952280894078929081/170875000000000000000000000000000 : ℝ)*base75 + (919835429012195919/170875000000000000000000000000000 : ℝ)*base78 + (1455663923921195919/170875000000000000000000000000000 : ℝ)*base80 + (1807218531441/341750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10577/1562500000000000000 : ℝ)*base89 + (10577/1562500000000000000 : ℝ)*base91 + (10577/1562500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1113_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1113_s8_0 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180834499/10000000000 : ℝ)*x 0 + (1348378737/2500000000 : ℝ)*x 1 + (5265296359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180834499/10000000000 : ℝ)^4153 ≤ (1656111824663/12500000000000 : ℝ)^3129 := by
    have hnat : (2180834499 : ℕ)^4153*12500000000000^3129 ≤ 1656111824663^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180834499 10000000000 1656111824663 12500000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348378737/2500000000 : ℝ)^4153 ≤ (275425407847/625000000000 : ℝ)^3129 := by
    have hnat : (1348378737 : ℕ)^4153*625000000000^3129 ≤ 275425407847^3129*2500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348378737 2500000000 275425407847 625000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265296359/10000000000 : ℝ)^4153 ≤ (1707321605453/4000000000000 : ℝ)^3129 := by
    have hnat : (5265296359 : ℕ)^4153*4000000000000^3129 ≤ 1707321605453^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265296359 10000000000 1707321605453 4000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180834499/10000000000 : ℝ), (1348378737/2500000000 : ℝ), (5265296359/10000000000 : ℝ)] ![(1656111824663/12500000000000 : ℝ), (275425407847/625000000000 : ℝ), (1707321605453/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180834499/10000000000 : ℝ)|^4153 ≤ (1656111824663/12500000000000 : ℝ)^3129
        have hw : |(-2180834499/10000000000 : ℝ)|=(2180834499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348378737/2500000000 : ℝ)|^4153 ≤ (275425407847/625000000000 : ℝ)^3129
        have hw : |(1348378737/2500000000 : ℝ)|=(1348378737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265296359/10000000000 : ℝ)|^4153 ≤ (1707321605453/4000000000000 : ℝ)^3129
        have hw : |(5265296359/10000000000 : ℝ)|=(5265296359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_1 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167026491/312500000 : ℝ)*x 0 + (-2245876381/10000000000 : ℝ)*x 1 + (5265295839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167026491/312500000 : ℝ)^4153 ≤ (43541075540863/100000000000000 : ℝ)^3129 := by
    have hnat : (167026491 : ℕ)^4153*100000000000000^3129 ≤ 43541075540863^3129*312500000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167026491 312500000 43541075540863 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245876381/10000000000 : ℝ)^4153 ≤ (1377588990193/10000000000000 : ℝ)^3129 := by
    have hnat : (2245876381 : ℕ)^4153*10000000000000^3129 ≤ 1377588990193^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245876381 10000000000 1377588990193 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265295839/10000000000 : ℝ)^4153 ≤ (21341517270713/50000000000000 : ℝ)^3129 := by
    have hnat : (5265295839 : ℕ)^4153*50000000000000^3129 ≤ 21341517270713^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265295839 10000000000 21341517270713 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167026491/312500000 : ℝ), (-2245876381/10000000000 : ℝ), (5265295839/10000000000 : ℝ)] ![(43541075540863/100000000000000 : ℝ), (1377588990193/10000000000000 : ℝ), (21341517270713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167026491/312500000 : ℝ)|^4153 ≤ (43541075540863/100000000000000 : ℝ)^3129
        have hw : |(167026491/312500000 : ℝ)|=(167026491/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245876381/10000000000 : ℝ)|^4153 ≤ (1377588990193/10000000000000 : ℝ)^3129
        have hw : |(-2245876381/10000000000 : ℝ)|=(2245876381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265295839/10000000000 : ℝ)|^4153 ≤ (21341517270713/50000000000000 : ℝ)^3129
        have hw : |(5265295839/10000000000 : ℝ)|=(5265295839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_2 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267242399/500000000 : ℝ)*x 0 + (526529539/1000000000 : ℝ)*x 1 + (-1122938309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267242399/500000000 : ℝ)^4153 ≤ (43541078438573/100000000000000 : ℝ)^3129 := by
    have hnat : (267242399 : ℕ)^4153*100000000000000^3129 ≤ 43541078438573^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267242399 500000000 43541078438573 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526529539/1000000000 : ℝ)^4153 ≤ (21341514855223/50000000000000 : ℝ)^3129 := by
    have hnat : (526529539 : ℕ)^4153*50000000000000^3129 ≤ 21341514855223^3129*1000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526529539 1000000000 21341514855223 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122938309/5000000000 : ℝ)^4153 ≤ (6887945915701/50000000000000 : ℝ)^3129 := by
    have hnat : (1122938309 : ℕ)^4153*50000000000000^3129 ≤ 6887945915701^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122938309 5000000000 6887945915701 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267242399/500000000 : ℝ), (526529539/1000000000 : ℝ), (-1122938309/5000000000 : ℝ)] ![(43541078438573/100000000000000 : ℝ), (21341514855223/50000000000000 : ℝ), (6887945915701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267242399/500000000 : ℝ)|^4153 ≤ (43541078438573/100000000000000 : ℝ)^3129
        have hw : |(267242399/500000000 : ℝ)|=(267242399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526529539/1000000000 : ℝ)|^4153 ≤ (21341514855223/50000000000000 : ℝ)^3129
        have hw : |(526529539/1000000000 : ℝ)|=(526529539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122938309/5000000000 : ℝ)|^4153 ≤ (6887945915701/50000000000000 : ℝ)^3129
        have hw : |(-1122938309/5000000000 : ℝ)|=(1122938309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_3 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184388371/5000000000 : ℝ)*x 0 + (42438013/100000000 : ℝ)*x 1 + (179897601/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184388371/5000000000 : ℝ)^4153 ≤ (33316825854459/100000000000000 : ℝ)^3129 := by
    have hnat : (2184388371 : ℕ)^4153*100000000000000^3129 ≤ 33316825854459^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184388371 5000000000 33316825854459 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42438013/100000000 : ℝ)^4153 ≤ (16028901093741/50000000000000 : ℝ)^3129 := by
    have hnat : (42438013 : ℕ)^4153*50000000000000^3129 ≤ 16028901093741^3129*100000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42438013 100000000 16028901093741 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179897601/400000000 : ℝ)^4153 ≤ (541021436647/1562500000000 : ℝ)^3129 := by
    have hnat : (179897601 : ℕ)^4153*1562500000000^3129 ≤ 541021436647^3129*400000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179897601 400000000 541021436647 1562500000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184388371/5000000000 : ℝ), (42438013/100000000 : ℝ), (179897601/400000000 : ℝ)] ![(33316825854459/100000000000000 : ℝ), (16028901093741/50000000000000 : ℝ), (541021436647/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184388371/5000000000 : ℝ)|^4153 ≤ (33316825854459/100000000000000 : ℝ)^3129
        have hw : |(2184388371/5000000000 : ℝ)|=(2184388371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42438013/100000000 : ℝ)|^4153 ≤ (16028901093741/50000000000000 : ℝ)^3129
        have hw : |(42438013/100000000 : ℝ)|=(42438013/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179897601/400000000 : ℝ)|^4153 ≤ (541021436647/1562500000000 : ℝ)^3129
        have hw : |(179897601/400000000 : ℝ)|=(179897601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_4 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109041977/500000000 : ℝ)*x 0 + (105312353/200000000 : ℝ)*x 1 + (2696596211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109041977/500000000 : ℝ)^4153 ≤ (662446762223/5000000000000 : ℝ)^3129 := by
    have hnat : (109041977 : ℕ)^4153*5000000000000^3129 ≤ 662446762223^3129*500000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109041977 500000000 662446762223 5000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105312353/200000000 : ℝ)^4153 ≤ (21343248537951/50000000000000 : ℝ)^3129 := by
    have hnat : (105312353 : ℕ)^4153*50000000000000^3129 ≤ 21343248537951^3129*200000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105312353 200000000 21343248537951 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696596211/5000000000 : ℝ)^4153 ≤ (44064567665139/100000000000000 : ℝ)^3129 := by
    have hnat : (2696596211 : ℕ)^4153*100000000000000^3129 ≤ 44064567665139^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696596211 5000000000 44064567665139 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109041977/500000000 : ℝ), (105312353/200000000 : ℝ), (2696596211/5000000000 : ℝ)] ![(662446762223/5000000000000 : ℝ), (21343248537951/50000000000000 : ℝ), (44064567665139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109041977/500000000 : ℝ)|^4153 ≤ (662446762223/5000000000000 : ℝ)^3129
        have hw : |(-109041977/500000000 : ℝ)|=(109041977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105312353/200000000 : ℝ)|^4153 ≤ (21343248537951/50000000000000 : ℝ)^3129
        have hw : |(105312353/200000000 : ℝ)|=(105312353/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696596211/5000000000 : ℝ)|^4153 ≤ (44064567665139/100000000000000 : ℝ)^3129
        have hw : |(2696596211/5000000000 : ℝ)|=(2696596211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_5 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664054173/1250000000 : ℝ)*x 0 + (-42359599/200000000 : ℝ)*x 1 + (8426863/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664054173/1250000000 : ℝ)^4153 ≤ (43190948678437/100000000000000 : ℝ)^3129 := by
    have hnat : (664054173 : ℕ)^4153*100000000000000^3129 ≤ 43190948678437^3129*1250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664054173 1250000000 43190948678437 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42359599/200000000 : ℝ)^4153 ≤ (12744484750127/100000000000000 : ℝ)^3129 := by
    have hnat : (42359599 : ℕ)^4153*100000000000000^3129 ≤ 12744484750127^3129*200000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42359599 200000000 12744484750127 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8426863/15625000 : ℝ)^4153 ≤ (2754035409939/6250000000000 : ℝ)^3129 := by
    have hnat : (8426863 : ℕ)^4153*6250000000000^3129 ≤ 2754035409939^3129*15625000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8426863 15625000 2754035409939 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664054173/1250000000 : ℝ), (-42359599/200000000 : ℝ), (8426863/15625000 : ℝ)] ![(43190948678437/100000000000000 : ℝ), (12744484750127/100000000000000 : ℝ), (2754035409939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664054173/1250000000 : ℝ)|^4153 ≤ (43190948678437/100000000000000 : ℝ)^3129
        have hw : |(664054173/1250000000 : ℝ)|=(664054173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42359599/200000000 : ℝ)|^4153 ≤ (12744484750127/100000000000000 : ℝ)^3129
        have hw : |(-42359599/200000000 : ℝ)|=(42359599/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8426863/15625000 : ℝ)|^4153 ≤ (2754035409939/6250000000000 : ℝ)^3129
        have hw : |(8426863/15625000 : ℝ)|=(8426863/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_6 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332027071/625000000 : ℝ)*x 0 + (2696596281/5000000000 : ℝ)*x 1 + (-2117979957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332027071/625000000 : ℝ)^4153 ≤ (21595473001153/50000000000000 : ℝ)^3129 := by
    have hnat : (332027071 : ℕ)^4153*50000000000000^3129 ≤ 21595473001153^3129*625000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332027071 625000000 21595473001153 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696596281/5000000000 : ℝ)^4153 ≤ (8812913836667/20000000000000 : ℝ)^3129 := by
    have hnat : (2696596281 : ℕ)^4153*20000000000000^3129 ≤ 8812913836667^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696596281 5000000000 8812913836667 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117979957/10000000000 : ℝ)^4153 ≤ (12744484806033/100000000000000 : ℝ)^3129 := by
    have hnat : (2117979957 : ℕ)^4153*100000000000000^3129 ≤ 12744484806033^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117979957 10000000000 12744484806033 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332027071/625000000 : ℝ), (2696596281/5000000000 : ℝ), (-2117979957/10000000000 : ℝ)] ![(21595473001153/50000000000000 : ℝ), (8812913836667/20000000000000 : ℝ), (12744484806033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332027071/625000000 : ℝ)|^4153 ≤ (21595473001153/50000000000000 : ℝ)^3129
        have hw : |(332027071/625000000 : ℝ)|=(332027071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696596281/5000000000 : ℝ)|^4153 ≤ (8812913836667/20000000000000 : ℝ)^3129
        have hw : |(2696596281/5000000000 : ℝ)|=(2696596281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117979957/10000000000 : ℝ)|^4153 ≤ (12744484806033/100000000000000 : ℝ)^3129
        have hw : |(-2117979957/10000000000 : ℝ)|=(2117979957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_7 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4368786279/10000000000 : ℝ)*x 0 + (2248401953/5000000000 : ℝ)*x 1 + (106110999/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368786279/10000000000 : ℝ)^4153 ≤ (3331692238663/10000000000000 : ℝ)^3129 := by
    have hnat : (4368786279 : ℕ)^4153*10000000000000^3129 ≤ 3331692238663^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368786279 10000000000 3331692238663 10000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248401953/5000000000 : ℝ)^4153 ≤ (34618871939513/100000000000000 : ℝ)^3129 := by
    have hnat : (2248401953 : ℕ)^4153*100000000000000^3129 ≤ 34618871939513^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248401953 5000000000 34618871939513 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106110999/250000000 : ℝ)^4153 ≤ (32064205658997/100000000000000 : ℝ)^3129 := by
    have hnat : (106110999 : ℕ)^4153*100000000000000^3129 ≤ 32064205658997^3129*250000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106110999 250000000 32064205658997 100000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368786279/10000000000 : ℝ), (2248401953/5000000000 : ℝ), (106110999/250000000 : ℝ)] ![(3331692238663/10000000000000 : ℝ), (34618871939513/100000000000000 : ℝ), (32064205658997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368786279/10000000000 : ℝ)|^4153 ≤ (3331692238663/10000000000000 : ℝ)^3129
        have hw : |(4368786279/10000000000 : ℝ)|=(4368786279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248401953/5000000000 : ℝ)|^4153 ≤ (34618871939513/100000000000000 : ℝ)^3129
        have hw : |(2248401953/5000000000 : ℝ)|=(2248401953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106110999/250000000 : ℝ)|^4153 ≤ (32064205658997/100000000000000 : ℝ)^3129
        have hw : |(106110999/250000000 : ℝ)|=(106110999/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1113_s8_8 (p : ℝ) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43213889/5000000000 : ℝ)*x 0 + (6078757627/10000000000 : ℝ)*x 1 + (28837013/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43213889/5000000000 : ℝ)^4153 ≤ (11409858487/6250000000000 : ℝ)^3129 := by
    have hnat : (43213889 : ℕ)^4153*6250000000000^3129 ≤ 11409858487^3129*5000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43213889 5000000000 11409858487 6250000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6078757627/10000000000 : ℝ)^4153 ≤ (25824732591641/50000000000000 : ℝ)^3129 := by
    have hnat : (6078757627 : ℕ)^4153*50000000000000^3129 ≤ 25824732591641^3129*10000000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6078757627 10000000000 25824732591641 50000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28837013/50000000 : ℝ)^4153 ≤ (9633595412123/20000000000000 : ℝ)^3129 := by
    have hnat : (28837013 : ℕ)^4153*20000000000000^3129 ≤ 9633595412123^3129*50000000^4153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28837013 50000000 9633595412123 20000000000000 4153 3129 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4153/1024 : ℝ)) 4153 3129 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43213889/5000000000 : ℝ), (6078757627/10000000000 : ℝ), (28837013/50000000 : ℝ)] ![(11409858487/6250000000000 : ℝ), (25824732591641/50000000000000 : ℝ), (9633595412123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43213889/5000000000 : ℝ)|^4153 ≤ (11409858487/6250000000000 : ℝ)^3129
        have hw : |(-43213889/5000000000 : ℝ)|=(43213889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6078757627/10000000000 : ℝ)|^4153 ≤ (25824732591641/50000000000000 : ℝ)^3129
        have hw : |(6078757627/10000000000 : ℝ)|=(6078757627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28837013/50000000 : ℝ)|^4153 ≤ (9633595412123/20000000000000 : ℝ)^3129
        have hw : |(28837013/50000000 : ℝ)|=(28837013/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1113_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2829/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/50000 : ℝ) ^ (8305/2048 : ℝ) ≤ (14529384960304001/100000000000000000000 : ℝ) := by
    have hpowers : (5657/50000 : ℝ)^8305 ≤ (14529384960304001/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5657 : ℕ)^8305*100000000000000000000^2048 ≤ 14529384960304001^2048*50000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 50000 14529384960304001 100000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/50000 : ℝ)) (X := (14529384960304001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/100000 : ℝ) ^ (8305/2048 : ℝ) ≤ (8699323345489971/25000000000000000000 : ℝ) := by
    have hpowers : (14033/100000 : ℝ)^8305 ≤ (8699323345489971/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14033 : ℕ)^8305*25000000000000000000^2048 ≤ 8699323345489971^2048*100000^8305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 100000 8699323345489971 25000000000000000000 8305 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/100000 : ℝ)) (X := (8699323345489971/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014529384960304001/50000000000000000000 : ℝ) ≤ (500035825314513/500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (50014529384960304001/50000000000000000000 : ℝ)^2048 ≤ (500035825314513/500000000000000 : ℝ)^8305 := by
      have hnat : (50014529384960304001 : ℕ)^2048*500000000000000^8305 ≤ 500035825314513^8305*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014529384960304001 50000000000000000000 500035825314513 500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500035825314513/500000000000000 : ℝ)) (X := (50014529384960304001/50000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009865335668452777/20000000000000000000 : ℝ) ≤ (2500304040552479/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (20009865335668452777/20000000000000000000 : ℝ)^2048 ≤ (2500304040552479/2500000000000000 : ℝ)^8305 := by
      have hnat : (20009865335668452777 : ℕ)^2048*2500000000000000^8305 ≤ 2500304040552479^8305*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009865335668452777 20000000000000000000 2500304040552479 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500304040552479/2500000000000000 : ℝ)) (X := (20009865335668452777/20000000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508699323345489971/12500000000000000000 : ℝ) ≤ (2500428954532393/2500000000000000 : ℝ) ^ (8305/2048 : ℝ) := by
    have hpowers : (12508699323345489971/12500000000000000000 : ℝ)^2048 ≤ (2500428954532393/2500000000000000 : ℝ)^8305 := by
      have hnat : (12508699323345489971 : ℕ)^2048*2500000000000000^8305 ≤ 2500428954532393^8305*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508699323345489971 12500000000000000000 2500428954532393 2500000000000000 2048 8305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500428954532393/2500000000000000 : ℝ)) (X := (12508699323345489971/12500000000000000000 : ℝ)) (by norm_num) 8305 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14529384960304001/100000000000000000000 : ℝ) ≤ ((6795160491613310243/6797500000000000000 : ℝ)+2*(62456989957/33987500000000 : ℝ)*(5657/50000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (6795160491613310243/6797500000000000000 : ℝ)+2*(62456989957/33987500000000 : ℝ)*(5657/50000 : ℝ)=(500035825314513/500000000000000 : ℝ) by norm_num, show 1+2*(14529384960304001/100000000000000000000 : ℝ)=(50014529384960304001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8699323345489971/25000000000000000000 : ℝ)+(14529384960304001/100000000000000000000 : ℝ) ≤ ((6795160491613310243/6797500000000000000 : ℝ)+(62456989957/33987500000000 : ℝ)*((14033/100000 : ℝ)+(5657/50000 : ℝ)))^(8305/2048 : ℝ) := by
    rw [show (6795160491613310243/6797500000000000000 : ℝ)+(62456989957/33987500000000 : ℝ)*((14033/100000 : ℝ)+(5657/50000 : ℝ))=(2500304040552479/2500000000000000 : ℝ) by norm_num, show 1+(8699323345489971/25000000000000000000 : ℝ)+(14529384960304001/100000000000000000000 : ℝ)=(20009865335668452777/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8699323345489971/25000000000000000000 : ℝ) ≤ ((6795160491613310243/6797500000000000000 : ℝ)+2*(62456989957/33987500000000 : ℝ)*(14033/100000 : ℝ))^(8305/2048 : ℝ) := by
    rw [show (6795160491613310243/6797500000000000000 : ℝ)+2*(62456989957/33987500000000 : ℝ)*(14033/100000 : ℝ)=(2500428954532393/2500000000000000 : ℝ) by norm_num, show 1+2*(8699323345489971/25000000000000000000 : ℝ)=(12508699323345489971/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6795160491613310243/6797500000000000000 : ℝ)*(X 1 0+X 2 0)+(62456989957/33987500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (6795160491613310243/6797500000000000000 : ℝ)) (alpha := (62456989957/33987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6795160491613310243/6797500000000000000 : ℝ)*(X 0 1+X 2 1)+(62456989957/33987500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (6795160491613310243/6797500000000000000 : ℝ)) (alpha := (62456989957/33987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6795160491613310243/6797500000000000000 : ℝ)*(X 0 2+X 1 2)+(62456989957/33987500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8305/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (6795160491613310243/6797500000000000000 : ℝ)) (alpha := (62456989957/33987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2180834499/10000000000 : ℝ)*X 0 0+(1348378737/2500000000 : ℝ)*X 0 1+(5265296359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167026491/312500000 : ℝ)*X 1 0+(-2245876381/10000000000 : ℝ)*X 1 1+(5265295839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267242399/500000000 : ℝ)*X 2 0+(526529539/1000000000 : ℝ)*X 2 1+(-1122938309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184388371/5000000000 : ℝ)*X 0 0+(42438013/100000000 : ℝ)*X 0 1+(179897601/400000000 : ℝ)*X 0 2+(2184388371/5000000000 : ℝ)*X 1 0+(42438013/100000000 : ℝ)*X 1 1+(179897601/400000000 : ℝ)*X 1 2+(2184388371/5000000000 : ℝ)*X 2 0+(42438013/100000000 : ℝ)*X 2 1+(179897601/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109041977/500000000 : ℝ)*X 0 0+(105312353/200000000 : ℝ)*X 0 1+(2696596211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664054173/1250000000 : ℝ)*X 1 0+(-42359599/200000000 : ℝ)*X 1 1+(8426863/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332027071/625000000 : ℝ)*X 2 0+(2696596281/5000000000 : ℝ)*X 2 1+(-2117979957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368786279/10000000000 : ℝ)*X 0 0+(2248401953/5000000000 : ℝ)*X 0 1+(106110999/250000000 : ℝ)*X 0 2+(4368786279/10000000000 : ℝ)*X 1 0+(2248401953/5000000000 : ℝ)*X 1 1+(106110999/250000000 : ℝ)*X 1 2+(4368786279/10000000000 : ℝ)*X 2 0+(2248401953/5000000000 : ℝ)*X 2 1+(106110999/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-43213889/5000000000 : ℝ)*X 0 0+(6078757627/10000000000 : ℝ)*X 0 1+(28837013/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1113_s8_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368795269756156619265133047/169937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536088311/100000000000000 : ℝ)*(lower2) + (29560021/6250000000000 : ℝ)*(lower3) + (109634479/25000000000000 : ℝ)*(lower4) + (8995771/12500000000000 : ℝ)*(lower5) + (2935443226392343/50000000000000 : ℝ)*(major0) + (2935443226392343/50000000000000 : ℝ)*(major1) + (2935443226392343/50000000000000 : ℝ)*(major2) + (7799147674829847/100000000000000 : ℝ)*(sp0) + (7799141893582527/100000000000000 : ℝ)*(sp1) + (3899553753066649/50000000000000 : ℝ)*(sp2) + (985655345312937/25000000000000 : ℝ)*(sp3) + (4779197839/50000000000000 : ℝ)*(sp5) + (43945844907/100000000000000 : ℝ)*(sp6) + (3777148359/100000000000000 : ℝ)*(sp8) + (985655345312937/25000000000000 : ℝ)*(f.failure) + (1949787862994551/25000000000000 : ℝ)*(f.sum) + (1207532639343721/13595000000000000000000000000 : ℝ)*base65 + (2682477579230005651/339875000000000000000000000000000 : ℝ)*base68 + (515180372700494349/339875000000000000000000000000000 : ℝ)*base69 + (24427196825582130651/339875000000000000000000000000000 : ℝ)*base72 + (62014472281219/13595000000000000000000000000 : ℝ)*base74 + (1758936045194505651/339875000000000000000000000000000 : ℝ)*base76 + (7968996931204869349/339875000000000000000000000000000 : ℝ)*base77 + (1047692731816880651/339875000000000000000000000000000 : ℝ)*base80 + (29411399377501/13595000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22378763/1250000000000000000000 : ℝ)*base89 + (22378763/1250000000000000000000 : ℝ)*base91 + (22378763/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455046412758505653719063283/169937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21799999/20000000000000 : ℝ)*(lower2) + (29675521/20000000000000 : ℝ)*(lower3) + (289694969/100000000000000 : ℝ)*(lower4) + (42816883/50000000000000 : ℝ)*(lower5) + (2950268642392191/50000000000000 : ℝ)*(major0) + (2950268642392191/50000000000000 : ℝ)*(major1) + (2950268642392191/50000000000000 : ℝ)*(major2) + (2113359799/50000000000000 : ℝ)*(sp2) + (1800775043/50000000000000 : ℝ)*(sp3) + (7838539115013771/100000000000000 : ℝ)*(sp4) + (7838540943517971/100000000000000 : ℝ)*(sp5) + (7838536716798373/100000000000000 : ℝ)*(sp6) + (3962529935243087/100000000000000 : ℝ)*(sp7) + (9142521/500000000000 : ℝ)*(sp8) + (1981266768396587/50000000000000 : ℝ)*(f.failure) + (7838540943517971/100000000000000 : ℝ)*(f.sum) + (15610551291317/13595000000000000000000000000 : ℝ)*base65 + (9359914812587412413/339875000000000000000000000000000 : ℝ)*base67 + (4220083459044912413/339875000000000000000000000000000 : ℝ)*base69 + (20644021154129537413/339875000000000000000000000000000 : ℝ)*base71 + (6447628528563/3398750000000000000000000000 : ℝ)*base73 + (7073191554744662413/339875000000000000000000000000000 : ℝ)*base75 + (6230447203757537413/339875000000000000000000000000000 : ℝ)*base77 + (4069025187359412413/339875000000000000000000000000000 : ℝ)*base79 + (1862621136317/13595000000000000000000000000 : ℝ)*base81 + (9760113/2500000000000000000000 : ℝ)*base89 + (9760113/2500000000000000000000 : ℝ)*base91 + (9760113/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1113_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1113_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1113_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1113_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1113_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1113_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8305/2048 : ℝ) ≤ p) (hpb : p ≤ (4153/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74454099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1113_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

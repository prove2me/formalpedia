-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1729_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:19.254815+00:00
-- url     : https://prove2.me/submissions/72d5e13b-32f1-4c7d-afe4-7bfcc116e3f9

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
theorem support_rectangle_w1729_s0_0 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-641239407/5000000000 : ℝ)*x 0 + (1415357261/2500000000 : ℝ)*x 1 + (995854627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (641239407/5000000000 : ℝ)^5455 ≤ (3989251621527/50000000000000 : ℝ)^4431 := by
    have hnat : (641239407 : ℕ)^5455*50000000000000^4431 ≤ 3989251621527^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641239407 5000000000 3989251621527 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415357261/2500000000 : ℝ)^5455 ≤ (2481975647343/5000000000000 : ℝ)^4431 := by
    have hnat : (1415357261 : ℕ)^5455*5000000000000^4431 ≤ 2481975647343^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415357261 2500000000 2481975647343 5000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995854627/2000000000 : ℝ)^5455 ≤ (42381983797673/100000000000000 : ℝ)^4431 := by
    have hnat : (995854627 : ℕ)^5455*100000000000000^4431 ≤ 42381983797673^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995854627 2000000000 42381983797673 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-641239407/5000000000 : ℝ), (1415357261/2500000000 : ℝ), (995854627/2000000000 : ℝ)] ![(3989251621527/50000000000000 : ℝ), (2481975647343/5000000000000 : ℝ), (42381983797673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-641239407/5000000000 : ℝ)|^5455 ≤ (3989251621527/50000000000000 : ℝ)^4431
        have hw : |(-641239407/5000000000 : ℝ)|=(641239407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415357261/2500000000 : ℝ)|^5455 ≤ (2481975647343/5000000000000 : ℝ)^4431
        have hw : |(1415357261/2500000000 : ℝ)|=(1415357261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995854627/2000000000 : ℝ)|^5455 ≤ (42381983797673/100000000000000 : ℝ)^4431
        have hw : |(995854627/2000000000 : ℝ)|=(995854627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_1 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391321641/10000000000 : ℝ)*x 0 + (-824842797/5000000000 : ℝ)*x 1 + (4979272439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391321641/10000000000 : ℝ)^5455 ≤ (46740167123799/100000000000000 : ℝ)^4431 := by
    have hnat : (5391321641 : ℕ)^5455*100000000000000^4431 ≤ 46740167123799^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391321641 10000000000 46740167123799 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824842797/5000000000 : ℝ)^5455 ≤ (10877856346103/100000000000000 : ℝ)^4431 := by
    have hnat : (824842797 : ℕ)^5455*100000000000000^4431 ≤ 10877856346103^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824842797 5000000000 10877856346103 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4979272439/10000000000 : ℝ)^5455 ≤ (42381976504483/100000000000000 : ℝ)^4431 := by
    have hnat : (4979272439 : ℕ)^5455*100000000000000^4431 ≤ 42381976504483^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979272439 10000000000 42381976504483 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391321641/10000000000 : ℝ), (-824842797/5000000000 : ℝ), (4979272439/10000000000 : ℝ)] ![(46740167123799/100000000000000 : ℝ), (10877856346103/100000000000000 : ℝ), (42381976504483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391321641/10000000000 : ℝ)|^5455 ≤ (46740167123799/100000000000000 : ℝ)^4431
        have hw : |(5391321641/10000000000 : ℝ)|=(5391321641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-824842797/5000000000 : ℝ)|^5455 ≤ (10877856346103/100000000000000 : ℝ)^4431
        have hw : |(-824842797/5000000000 : ℝ)|=(824842797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4979272439/10000000000 : ℝ)|^5455 ≤ (42381976504483/100000000000000 : ℝ)^4431
        have hw : |(4979272439/10000000000 : ℝ)|=(4979272439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_2 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391320159/10000000000 : ℝ)*x 0 + (1244818347/2500000000 : ℝ)*x 1 + (-1649686319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391320159/10000000000 : ℝ)^5455 ≤ (46740151306359/100000000000000 : ℝ)^4431 := by
    have hnat : (5391320159 : ℕ)^5455*100000000000000^4431 ≤ 46740151306359^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391320159 10000000000 46740151306359 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1244818347/2500000000 : ℝ)^5455 ≤ (4238198644879/10000000000000 : ℝ)^4431 := by
    have hnat : (1244818347 : ℕ)^5455*10000000000000^4431 ≤ 4238198644879^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244818347 2500000000 4238198644879 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1649686319/10000000000 : ℝ)^5455 ≤ (1359732778933/12500000000000 : ℝ)^4431 := by
    have hnat : (1649686319 : ℕ)^5455*12500000000000^4431 ≤ 1359732778933^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649686319 10000000000 1359732778933 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391320159/10000000000 : ℝ), (1244818347/2500000000 : ℝ), (-1649686319/10000000000 : ℝ)] ![(46740151306359/100000000000000 : ℝ), (4238198644879/10000000000000 : ℝ), (1359732778933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391320159/10000000000 : ℝ)|^5455 ≤ (46740151306359/100000000000000 : ℝ)^4431
        have hw : |(5391320159/10000000000 : ℝ)|=(5391320159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1244818347/2500000000 : ℝ)|^5455 ≤ (4238198644879/10000000000000 : ℝ)^4431
        have hw : |(1244818347/2500000000 : ℝ)|=(1244818347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1649686319/10000000000 : ℝ)|^5455 ≤ (1359732778933/12500000000000 : ℝ)^4431
        have hw : |(-1649686319/10000000000 : ℝ)|=(1649686319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_3 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (160955709/400000000 : ℝ)*x 0 + (3071105989/10000000000 : ℝ)*x 1 + (1026953147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160955709/400000000 : ℝ)^5455 ≤ (32604725004869/100000000000000 : ℝ)^4431 := by
    have hnat : (160955709 : ℕ)^5455*100000000000000^4431 ≤ 32604725004869^4431*400000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160955709 400000000 32604725004869 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071105989/10000000000 : ℝ)^5455 ≤ (23378094442359/100000000000000 : ℝ)^4431 := by
    have hnat : (3071105989 : ℕ)^5455*100000000000000^4431 ≤ 23378094442359^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071105989 10000000000 23378094442359 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026953147/2000000000 : ℝ)^5455 ≤ (220085902667/500000000000 : ℝ)^4431 := by
    have hnat : (1026953147 : ℕ)^5455*500000000000^4431 ≤ 220085902667^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026953147 2000000000 220085902667 500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(160955709/400000000 : ℝ), (3071105989/10000000000 : ℝ), (1026953147/2000000000 : ℝ)] ![(32604725004869/100000000000000 : ℝ), (23378094442359/100000000000000 : ℝ), (220085902667/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(160955709/400000000 : ℝ)|^5455 ≤ (32604725004869/100000000000000 : ℝ)^4431
        have hw : |(160955709/400000000 : ℝ)|=(160955709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071105989/10000000000 : ℝ)|^5455 ≤ (23378094442359/100000000000000 : ℝ)^4431
        have hw : |(3071105989/10000000000 : ℝ)|=(3071105989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026953147/2000000000 : ℝ)|^5455 ≤ (220085902667/500000000000 : ℝ)^4431
        have hw : |(1026953147/2000000000 : ℝ)|=(1026953147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_4 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-320969907/2500000000 : ℝ)*x 0 + (4995684947/10000000000 : ℝ)*x 1 + (5644491073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (320969907/2500000000 : ℝ)^5455 ≤ (998654154693/12500000000000 : ℝ)^4431 := by
    have hnat : (320969907 : ℕ)^5455*12500000000000^4431 ≤ 998654154693^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320969907 2500000000 998654154693 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4995684947/10000000000 : ℝ)^5455 ≤ (2659626503883/6250000000000 : ℝ)^4431 := by
    have hnat : (4995684947 : ℕ)^5455*6250000000000^4431 ≤ 2659626503883^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995684947 10000000000 2659626503883 6250000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644491073/10000000000 : ℝ)^5455 ≤ (24728371338177/50000000000000 : ℝ)^4431 := by
    have hnat : (5644491073 : ℕ)^5455*50000000000000^4431 ≤ 24728371338177^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644491073 10000000000 24728371338177 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-320969907/2500000000 : ℝ), (4995684947/10000000000 : ℝ), (5644491073/10000000000 : ℝ)] ![(998654154693/12500000000000 : ℝ), (2659626503883/6250000000000 : ℝ), (24728371338177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-320969907/2500000000 : ℝ)|^5455 ≤ (998654154693/12500000000000 : ℝ)^4431
        have hw : |(-320969907/2500000000 : ℝ)|=(320969907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4995684947/10000000000 : ℝ)|^5455 ≤ (2659626503883/6250000000000 : ℝ)^4431
        have hw : |(4995684947/10000000000 : ℝ)|=(4995684947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644491073/10000000000 : ℝ)|^5455 ≤ (24728371338177/50000000000000 : ℝ)^4431
        have hw : |(5644491073/10000000000 : ℝ)|=(5644491073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_5 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301775481/2500000000 : ℝ)*x 0 + (-98446729/1000000000 : ℝ)*x 1 + (282224563/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301775481/2500000000 : ℝ)^5455 ≤ (22390907663827/50000000000000 : ℝ)^4431 := by
    have hnat : (1301775481 : ℕ)^5455*50000000000000^4431 ≤ 22390907663827^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301775481 2500000000 22390907663827 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98446729/1000000000 : ℝ)^5455 ≤ (720179995401/12500000000000 : ℝ)^4431 := by
    have hnat : (98446729 : ℕ)^5455*12500000000000^4431 ≤ 720179995401^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98446729 1000000000 720179995401 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282224563/500000000 : ℝ)^5455 ≤ (4945674469349/10000000000000 : ℝ)^4431 := by
    have hnat : (282224563 : ℕ)^5455*10000000000000^4431 ≤ 4945674469349^4431*500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282224563 500000000 4945674469349 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301775481/2500000000 : ℝ), (-98446729/1000000000 : ℝ), (282224563/500000000 : ℝ)] ![(22390907663827/50000000000000 : ℝ), (720179995401/12500000000000 : ℝ), (4945674469349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301775481/2500000000 : ℝ)|^5455 ≤ (22390907663827/50000000000000 : ℝ)^4431
        have hw : |(1301775481/2500000000 : ℝ)|=(1301775481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98446729/1000000000 : ℝ)|^5455 ≤ (720179995401/12500000000000 : ℝ)^4431
        have hw : |(-98446729/1000000000 : ℝ)|=(98446729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282224563/500000000 : ℝ)|^5455 ≤ (4945674469349/10000000000000 : ℝ)^4431
        have hw : |(282224563/500000000 : ℝ)|=(282224563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_6 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5207101501/10000000000 : ℝ)*x 0 + (5644491143/10000000000 : ℝ)*x 1 + (-123058511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5207101501/10000000000 : ℝ)^5455 ≤ (699715794517/1562500000000 : ℝ)^4431 := by
    have hnat : (5207101501 : ℕ)^5455*1562500000000^4431 ≤ 699715794517^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207101501 10000000000 699715794517 1562500000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5644491143/10000000000 : ℝ)^5455 ≤ (6182092928929/12500000000000 : ℝ)^4431 := by
    have hnat : (5644491143 : ℕ)^5455*12500000000000^4431 ≤ 6182092928929^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644491143 10000000000 6182092928929 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123058511/1250000000 : ℝ)^5455 ≤ (115228914253/2000000000000 : ℝ)^4431 := by
    have hnat : (123058511 : ℕ)^5455*2000000000000^4431 ≤ 115228914253^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123058511 1250000000 115228914253 2000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5207101501/10000000000 : ℝ), (5644491143/10000000000 : ℝ), (-123058511/1250000000 : ℝ)] ![(699715794517/1562500000000 : ℝ), (6182092928929/12500000000000 : ℝ), (115228914253/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5207101501/10000000000 : ℝ)|^5455 ≤ (699715794517/1562500000000 : ℝ)^4431
        have hw : |(5207101501/10000000000 : ℝ)|=(5207101501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5644491143/10000000000 : ℝ)|^5455 ≤ (6182092928929/12500000000000 : ℝ)^4431
        have hw : |(5644491143/10000000000 : ℝ)|=(5644491143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123058511/1250000000 : ℝ)|^5455 ≤ (115228914253/2000000000000 : ℝ)^4431
        have hw : |(-123058511/1250000000 : ℝ)|=(123058511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s0_7 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4028127629/10000000000 : ℝ)*x 0 + (635639857/1250000000 : ℝ)*x 1 + (3122345353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4028127629/10000000000 : ℝ)^5455 ≤ (16323487347053/50000000000000 : ℝ)^4431 := by
    have hnat : (4028127629 : ℕ)^5455*50000000000000^4431 ≤ 16323487347053^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028127629 10000000000 16323487347053 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635639857/1250000000 : ℝ)^5455 ≤ (679590958389/1562500000000 : ℝ)^4431 := by
    have hnat : (635639857 : ℕ)^5455*1562500000000^4431 ≤ 679590958389^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635639857 1250000000 679590958389 1562500000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3122345353/10000000000 : ℝ)^5455 ≤ (23859203959461/100000000000000 : ℝ)^4431 := by
    have hnat : (3122345353 : ℕ)^5455*100000000000000^4431 ≤ 23859203959461^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122345353 10000000000 23859203959461 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4028127629/10000000000 : ℝ), (635639857/1250000000 : ℝ), (3122345353/10000000000 : ℝ)] ![(16323487347053/50000000000000 : ℝ), (679590958389/1562500000000 : ℝ), (23859203959461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4028127629/10000000000 : ℝ)|^5455 ≤ (16323487347053/50000000000000 : ℝ)^4431
        have hw : |(4028127629/10000000000 : ℝ)|=(4028127629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635639857/1250000000 : ℝ)|^5455 ≤ (679590958389/1562500000000 : ℝ)^4431
        have hw : |(635639857/1250000000 : ℝ)|=(635639857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3122345353/10000000000 : ℝ)|^5455 ≤ (23859203959461/100000000000000 : ℝ)^4431
        have hw : |(3122345353/10000000000 : ℝ)|=(3122345353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1729_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6573/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21267/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5447/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5447 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5447*1^1024 ≤ 0^1024*1^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5447/1024 : ℝ) ≤ (764228819061139433/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5447 ≤ (764228819061139433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5447*100000000000000000000^1024 ≤ 764228819061139433^1024*5^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 764228819061139433 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (764228819061139433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5447 := by
      have hnat : (1 : ℕ)^1024*1^5447 ≤ 1^5447*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100764228819061139433/100000000000000000000 : ℝ) ≤ (5007161311772027/5000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (100764228819061139433/100000000000000000000 : ℝ)^1024 ≤ (5007161311772027/5000000000000000 : ℝ)^5447 := by
      have hnat : (100764228819061139433 : ℕ)^1024*5000000000000000^5447 ≤ 5007161311772027^5447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100764228819061139433 100000000000000000000 5007161311772027 5000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007161311772027/5000000000000000 : ℝ)) (X := (100764228819061139433/100000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50764228819061139433/50000000000000000000 : ℝ) ≤ (2507161311772027/2500000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50764228819061139433/50000000000000000000 : ℝ)^1024 ≤ (2507161311772027/2500000000000000 : ℝ)^5447 := by
      have hnat : (50764228819061139433 : ℕ)^1024*2500000000000000^5447 ≤ 2507161311772027^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50764228819061139433 50000000000000000000 2507161311772027 2500000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507161311772027/2500000000000000 : ℝ)) (X := (50764228819061139433/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7161311772027/2000000000000000 : ℝ)*(0 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7161311772027/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(764228819061139433/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7161311772027/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5447/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7161311772027/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5007161311772027/5000000000000000 : ℝ) by norm_num, show 1+(764228819061139433/100000000000000000000 : ℝ)+(0 : ℝ)=(100764228819061139433/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(764228819061139433/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7161311772027/2000000000000000 : ℝ)*(2/5 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7161311772027/2000000000000000 : ℝ)*(2/5 : ℝ)=(2507161311772027/2500000000000000 : ℝ) by norm_num, show 1+2*(764228819061139433/100000000000000000000 : ℝ)=(50764228819061139433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7161311772027/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7161311772027/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7161311772027/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7161311772027/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7161311772027/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7161311772027/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-641239407/5000000000 : ℝ)*X 0 0+(1415357261/2500000000 : ℝ)*X 0 1+(995854627/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5391321641/10000000000 : ℝ)*X 1 0+(-824842797/5000000000 : ℝ)*X 1 1+(4979272439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5391320159/10000000000 : ℝ)*X 2 0+(1244818347/2500000000 : ℝ)*X 2 1+(-1649686319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((160955709/400000000 : ℝ)*X 0 0+(3071105989/10000000000 : ℝ)*X 0 1+(1026953147/2000000000 : ℝ)*X 0 2+(160955709/400000000 : ℝ)*X 1 0+(3071105989/10000000000 : ℝ)*X 1 1+(1026953147/2000000000 : ℝ)*X 1 2+(160955709/400000000 : ℝ)*X 2 0+(3071105989/10000000000 : ℝ)*X 2 1+(1026953147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-320969907/2500000000 : ℝ)*X 0 0+(4995684947/10000000000 : ℝ)*X 0 1+(5644491073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301775481/2500000000 : ℝ)*X 1 0+(-98446729/1000000000 : ℝ)*X 1 1+(282224563/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5207101501/10000000000 : ℝ)*X 2 0+(5644491143/10000000000 : ℝ)*X 2 1+(-123058511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4028127629/10000000000 : ℝ)*X 0 0+(635639857/1250000000 : ℝ)*X 0 1+(3122345353/10000000000 : ℝ)*X 0 2+(4028127629/10000000000 : ℝ)*X 1 0+(635639857/1250000000 : ℝ)*X 1 1+(3122345353/10000000000 : ℝ)*X 1 2+(4028127629/10000000000 : ℝ)*X 2 0+(635639857/1250000000 : ℝ)*X 2 1+(3122345353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3153913423617432597/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40321333/20000000000000 : ℝ)*(base1) + (29191671/100000000000000 : ℝ)*(base16) + (420024249/50000000000000 : ℝ)*(base19) + (89864813/20000000000000 : ℝ)*(base23) + (8192601/4000000000000 : ℝ)*(upper3) + (975259865988553/100000000000000 : ℝ)*(major0) + (975259865988553/100000000000000 : ℝ)*(major1) + (975259865988553/100000000000000 : ℝ)*(major2) + (36648585012907/2500000000000 : ℝ)*(sp0) + (732971164834723/50000000000000 : ℝ)*(sp1) + (146594225356833/10000000000000 : ℝ)*(sp2) + (484575886914541/100000000000000 : ℝ)*(sp3) + (24800861/5000000000000 : ℝ)*(sp6) + (339415833/100000000000000 : ℝ)*(sp7) + (242288213968519/50000000000000 : ℝ)*(f.failure) + (293188639781923/20000000000000 : ℝ)*(f.sum) + (10154698593069/100000000000000000000000000000 : ℝ)*base66 + (340241355793069/200000000000000000000000000000 : ℝ)*base68 + (108240369193069/200000000000000000000000000000 : ℝ)*base70 + (591016485993069/200000000000000000000000000000 : ℝ)*base72 + (82895310306931/100000000000000000000000000000 : ℝ)*base73 + (628947432006931/200000000000000000000000000000 : ℝ)*base75 + (71122646793069/200000000000000000000000000000 : ℝ)*base78 + (362309008206931/200000000000000000000000000000 : ℝ)*base79 + (120925122206931/100000000000000000000000000000 : ℝ)*base81 + (16405859/2500000000000000000000 : ℝ)*base90 + (16405859/2500000000000000000000 : ℝ)*base92 + (16405859/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (517010321564527563/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (596133541/50000000000000 : ℝ)*(base19) + (1065950801/100000000000000 : ℝ)*(base23) + (24736533/100000000000000 : ℝ)*(upper2) + (211732539/100000000000000 : ℝ)*(upper3) + (152468077/100000000000000 : ℝ)*(upper5) + (20507746652253/2000000000000 : ℝ)*(major0) + (20507746652253/2000000000000 : ℝ)*(major1) + (20507746652253/2000000000000 : ℝ)*(major2) + (316045043/6250000000000 : ℝ)*(sp1) + (1841307349/50000000000000 : ℝ)*(sp2) + (1541291279011289/100000000000000 : ℝ)*(sp4) + (9633031437647/625000000000 : ℝ)*(sp5) + (154128653044579/10000000000000 : ℝ)*(sp6) + (509483213877231/100000000000000 : ℝ)*(sp7) + (509483213877231/100000000000000 : ℝ)*(f.failure) + (1541291279011289/100000000000000 : ℝ)*(f.sum) + (1756392312831/2000000000000000000000000000 : ℝ)*base65 + (48201755749169/4000000000000000000000000000 : ℝ)*base68 + (2699940633169/4000000000000000000000000000 : ℝ)*base70 + (20768325221169/4000000000000000000000000000 : ℝ)*base72 + (746105398831/2000000000000000000000000000 : ℝ)*base73 + (29448861173169/4000000000000000000000000000 : ℝ)*base76 + (12772990357169/4000000000000000000000000000 : ℝ)*base78 + (16223068193169/4000000000000000000000000000 : ℝ)*base80 + (4273399204831/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15534891/5000000000000000000000 : ℝ)*base90 + (15534891/5000000000000000000000 : ℝ)*base92 + (15534891/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1729_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6573/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21267/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1729_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1729_s1_0 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1343892279/10000000000 : ℝ)*x 0 + (1093619271/2000000000 : ℝ)*x 1 + (320747891/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343892279/10000000000 : ℝ)^5455 ≤ (422571590537/5000000000000 : ℝ)^4431 := by
    have hnat : (1343892279 : ℕ)^5455*5000000000000^4431 ≤ 422571590537^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343892279 10000000000 422571590537 5000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093619271/2000000000 : ℝ)^5455 ≤ (237804649733/500000000000 : ℝ)^4431 := by
    have hnat : (1093619271 : ℕ)^5455*500000000000^4431 ≤ 237804649733^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093619271 2000000000 237804649733 500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320747891/625000000 : ℝ)^5455 ≤ (1759505528963/4000000000000 : ℝ)^4431 := by
    have hnat : (320747891 : ℕ)^5455*4000000000000^4431 ≤ 1759505528963^4431*625000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320747891 625000000 1759505528963 4000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1343892279/10000000000 : ℝ), (1093619271/2000000000 : ℝ), (320747891/625000000 : ℝ)] ![(422571590537/5000000000000 : ℝ), (237804649733/500000000000 : ℝ), (1759505528963/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1343892279/10000000000 : ℝ)|^5455 ≤ (422571590537/5000000000000 : ℝ)^4431
        have hw : |(-1343892279/10000000000 : ℝ)|=(1343892279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093619271/2000000000 : ℝ)|^5455 ≤ (237804649733/500000000000 : ℝ)^4431
        have hw : |(1093619271/2000000000 : ℝ)|=(1093619271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320747891/625000000 : ℝ)|^5455 ≤ (1759505528963/4000000000000 : ℝ)^4431
        have hw : |(320747891/625000000 : ℝ)|=(320747891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_1 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133496041/250000000 : ℝ)*x 0 + (-379566189/2500000000 : ℝ)*x 1 + (2565982673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133496041/250000000 : ℝ)^5455 ≤ (4619132687831/10000000000000 : ℝ)^4431 := by
    have hnat : (133496041 : ℕ)^5455*10000000000000^4431 ≤ 4619132687831^4431*250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133496041 250000000 4619132687831 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379566189/2500000000 : ℝ)^5455 ≤ (9821044479003/100000000000000 : ℝ)^4431 := by
    have hnat : (379566189 : ℕ)^5455*100000000000000^4431 ≤ 9821044479003^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379566189 2500000000 9821044479003 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565982673/5000000000 : ℝ)^5455 ≤ (43987628621643/100000000000000 : ℝ)^4431 := by
    have hnat : (2565982673 : ℕ)^5455*100000000000000^4431 ≤ 43987628621643^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565982673 5000000000 43987628621643 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133496041/250000000 : ℝ), (-379566189/2500000000 : ℝ), (2565982673/5000000000 : ℝ)] ![(4619132687831/10000000000000 : ℝ), (9821044479003/100000000000000 : ℝ), (43987628621643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133496041/250000000 : ℝ)|^5455 ≤ (4619132687831/10000000000000 : ℝ)^4431
        have hw : |(133496041/250000000 : ℝ)|=(133496041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379566189/2500000000 : ℝ)|^5455 ≤ (9821044479003/100000000000000 : ℝ)^4431
        have hw : |(-379566189/2500000000 : ℝ)|=(379566189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565982673/5000000000 : ℝ)|^5455 ≤ (43987628621643/100000000000000 : ℝ)^4431
        have hw : |(2565982673/5000000000 : ℝ)|=(2565982673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_2 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339840247/10000000000 : ℝ)*x 0 + (2565983143/5000000000 : ℝ)*x 1 + (-12146123/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339840247/10000000000 : ℝ)^5455 ≤ (23095656021849/50000000000000 : ℝ)^4431 := by
    have hnat : (5339840247 : ℕ)^5455*50000000000000^4431 ≤ 23095656021849^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339840247 10000000000 23095656021849 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565983143/5000000000 : ℝ)^5455 ≤ (43987638540639/100000000000000 : ℝ)^4431 := by
    have hnat : (2565983143 : ℕ)^5455*100000000000000^4431 ≤ 43987638540639^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565983143 5000000000 43987638540639 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12146123/80000000 : ℝ)^5455 ≤ (9821049408401/100000000000000 : ℝ)^4431 := by
    have hnat : (12146123 : ℕ)^5455*100000000000000^4431 ≤ 9821049408401^4431*80000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12146123 80000000 9821049408401 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339840247/10000000000 : ℝ), (2565983143/5000000000 : ℝ), (-12146123/80000000 : ℝ)] ![(23095656021849/50000000000000 : ℝ), (43987638540639/100000000000000 : ℝ), (9821049408401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339840247/10000000000 : ℝ)|^5455 ≤ (23095656021849/50000000000000 : ℝ)^4431
        have hw : |(5339840247/10000000000 : ℝ)|=(5339840247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565983143/5000000000 : ℝ)|^5455 ≤ (43987638540639/100000000000000 : ℝ)^4431
        have hw : |(2565983143/5000000000 : ℝ)|=(2565983143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12146123/80000000 : ℝ)|^5455 ≤ (9821049408401/100000000000000 : ℝ)^4431
        have hw : |(-12146123/80000000 : ℝ)|=(12146123/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_3 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2039595269/5000000000 : ℝ)*x 0 + (717968537/2000000000 : ℝ)*x 1 + (2303350101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039595269/5000000000 : ℝ)^5455 ≤ (33157211640561/100000000000000 : ℝ)^4431 := by
    have hnat : (2039595269 : ℕ)^5455*100000000000000^4431 ≤ 33157211640561^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039595269 5000000000 33157211640561 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (717968537/2000000000 : ℝ)^5455 ≤ (14165234294019/50000000000000 : ℝ)^4431 := by
    have hnat : (717968537 : ℕ)^5455*50000000000000^4431 ≤ 14165234294019^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717968537 2000000000 14165234294019 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303350101/5000000000 : ℝ)^5455 ≤ (240701998461/625000000000 : ℝ)^4431 := by
    have hnat : (2303350101 : ℕ)^5455*625000000000^4431 ≤ 240701998461^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303350101 5000000000 240701998461 625000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2039595269/5000000000 : ℝ), (717968537/2000000000 : ℝ), (2303350101/5000000000 : ℝ)] ![(33157211640561/100000000000000 : ℝ), (14165234294019/50000000000000 : ℝ), (240701998461/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2039595269/5000000000 : ℝ)|^5455 ≤ (33157211640561/100000000000000 : ℝ)^4431
        have hw : |(2039595269/5000000000 : ℝ)|=(2039595269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(717968537/2000000000 : ℝ)|^5455 ≤ (14165234294019/50000000000000 : ℝ)^4431
        have hw : |(717968537/2000000000 : ℝ)|=(717968537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2303350101/5000000000 : ℝ)|^5455 ≤ (240701998461/625000000000 : ℝ)^4431
        have hw : |(2303350101/5000000000 : ℝ)|=(2303350101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_4 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268812071/2000000000 : ℝ)*x 0 + (5135964893/10000000000 : ℝ)*x 1 + (683004211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268812071/2000000000 : ℝ)^5455 ≤ (8452733090927/100000000000000 : ℝ)^4431 := by
    have hnat : (268812071 : ℕ)^5455*100000000000000^4431 ≤ 8452733090927^4431*2000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268812071 2000000000 8452733090927 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135964893/10000000000 : ℝ)^5455 ≤ (44029836132797/100000000000000 : ℝ)^4431 := by
    have hnat : (5135964893 : ℕ)^5455*100000000000000^4431 ≤ 44029836132797^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135964893 10000000000 44029836132797 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683004211/1250000000 : ℝ)^5455 ≤ (47517430761901/100000000000000 : ℝ)^4431 := by
    have hnat : (683004211 : ℕ)^5455*100000000000000^4431 ≤ 47517430761901^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683004211 1250000000 47517430761901 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268812071/2000000000 : ℝ), (5135964893/10000000000 : ℝ), (683004211/1250000000 : ℝ)] ![(8452733090927/100000000000000 : ℝ), (44029836132797/100000000000000 : ℝ), (47517430761901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268812071/2000000000 : ℝ)|^5455 ≤ (8452733090927/100000000000000 : ℝ)^4431
        have hw : |(-268812071/2000000000 : ℝ)|=(268812071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135964893/10000000000 : ℝ)|^5455 ≤ (44029836132797/100000000000000 : ℝ)^4431
        have hw : |(5135964893/10000000000 : ℝ)|=(5135964893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683004211/1250000000 : ℝ)|^5455 ≤ (47517430761901/100000000000000 : ℝ)^4431
        have hw : |(683004211/1250000000 : ℝ)|=(683004211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_5 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5249860193/10000000000 : ℝ)*x 0 + (-1186197773/10000000000 : ℝ)*x 1 + (5464032981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5249860193/10000000000 : ℝ)^5455 ≤ (22617476282563/50000000000000 : ℝ)^4431 := by
    have hnat : (5249860193 : ℕ)^5455*50000000000000^4431 ≤ 22617476282563^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249860193 10000000000 22617476282563 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186197773/10000000000 : ℝ)^5455 ≤ (7247624223253/100000000000000 : ℝ)^4431 := by
    have hnat : (1186197773 : ℕ)^5455*100000000000000^4431 ≤ 7247624223253^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186197773 10000000000 7247624223253 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464032981/10000000000 : ℝ)^5455 ≤ (23758711596333/50000000000000 : ℝ)^4431 := by
    have hnat : (5464032981 : ℕ)^5455*50000000000000^4431 ≤ 23758711596333^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464032981 10000000000 23758711596333 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5249860193/10000000000 : ℝ), (-1186197773/10000000000 : ℝ), (5464032981/10000000000 : ℝ)] ![(22617476282563/50000000000000 : ℝ), (7247624223253/100000000000000 : ℝ), (23758711596333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5249860193/10000000000 : ℝ)|^5455 ≤ (22617476282563/50000000000000 : ℝ)^4431
        have hw : |(5249860193/10000000000 : ℝ)|=(5249860193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1186197773/10000000000 : ℝ)|^5455 ≤ (7247624223253/100000000000000 : ℝ)^4431
        have hw : |(-1186197773/10000000000 : ℝ)|=(1186197773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464032981/10000000000 : ℝ)|^5455 ≤ (23758711596333/50000000000000 : ℝ)^4431
        have hw : |(5464032981/10000000000 : ℝ)|=(5464032981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_6 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5249860157/10000000000 : ℝ)*x 0 + (2732016331/5000000000 : ℝ)*x 1 + (-593099139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5249860157/10000000000 : ℝ)^5455 ≤ (180939808733/400000000000 : ℝ)^4431 := by
    have hnat : (5249860157 : ℕ)^5455*400000000000^4431 ≤ 180939808733^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249860157 10000000000 180939808733 400000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732016331/5000000000 : ℝ)^5455 ≤ (4751741977741/10000000000000 : ℝ)^4431 := by
    have hnat : (2732016331 : ℕ)^5455*10000000000000^4431 ≤ 4751741977741^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732016331 5000000000 4751741977741 10000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593099139/5000000000 : ℝ)^5455 ≤ (905953502731/12500000000000 : ℝ)^4431 := by
    have hnat : (593099139 : ℕ)^5455*12500000000000^4431 ≤ 905953502731^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593099139 5000000000 905953502731 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5249860157/10000000000 : ℝ), (2732016331/5000000000 : ℝ), (-593099139/5000000000 : ℝ)] ![(180939808733/400000000000 : ℝ), (4751741977741/10000000000000 : ℝ), (905953502731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5249860157/10000000000 : ℝ)|^5455 ≤ (180939808733/400000000000 : ℝ)^4431
        have hw : |(5249860157/10000000000 : ℝ)|=(5249860157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732016331/5000000000 : ℝ)|^5455 ≤ (4751741977741/10000000000000 : ℝ)^4431
        have hw : |(2732016331/5000000000 : ℝ)|=(2732016331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-593099139/5000000000 : ℝ)|^5455 ≤ (905953502731/12500000000000 : ℝ)^4431
        have hw : |(-593099139/5000000000 : ℝ)|=(593099139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s1_7 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4079693937/10000000000 : ℝ)*x 0 + (1148650583/2500000000 : ℝ)*x 1 + (3602131083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4079693937/10000000000 : ℝ)^5455 ≤ (33162249146321/100000000000000 : ℝ)^4431 := by
    have hnat : (4079693937 : ℕ)^5455*100000000000000^4431 ≤ 33162249146321^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4079693937 10000000000 33162249146321 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1148650583/2500000000 : ℝ)^5455 ≤ (959696135921/2500000000000 : ℝ)^4431 := by
    have hnat : (1148650583 : ℕ)^5455*2500000000000^4431 ≤ 959696135921^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148650583 2500000000 959696135921 2500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3602131083/10000000000 : ℝ)^5455 ≤ (711247635051/2500000000000 : ℝ)^4431 := by
    have hnat : (3602131083 : ℕ)^5455*2500000000000^4431 ≤ 711247635051^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3602131083 10000000000 711247635051 2500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4079693937/10000000000 : ℝ), (1148650583/2500000000 : ℝ), (3602131083/10000000000 : ℝ)] ![(33162249146321/100000000000000 : ℝ), (959696135921/2500000000000 : ℝ), (711247635051/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4079693937/10000000000 : ℝ)|^5455 ≤ (33162249146321/100000000000000 : ℝ)^4431
        have hw : |(4079693937/10000000000 : ℝ)|=(4079693937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1148650583/2500000000 : ℝ)|^5455 ≤ (959696135921/2500000000000 : ℝ)^4431
        have hw : |(1148650583/2500000000 : ℝ)|=(1148650583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3602131083/10000000000 : ℝ)|^5455 ≤ (711247635051/2500000000000 : ℝ)^4431
        have hw : |(3602131083/10000000000 : ℝ)|=(3602131083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1729_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21267/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6573/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4983/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3433/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21267/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6573/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21267/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6573/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21267/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6573/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21267/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6573/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21267/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6573/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21267/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6573/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6573/100000 : ℝ) ^ (5447/1024 : ℝ) ≤ (51438417913709/100000000000000000000 : ℝ) := by
    have hpowers : (6573/100000 : ℝ)^5447 ≤ (51438417913709/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6573 : ℕ)^5447*100000000000000000000^1024 ≤ 51438417913709^1024*100000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6573 100000 51438417913709 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6573/100000 : ℝ)) (X := (51438417913709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21267/100000 : ℝ) ^ (5447/1024 : ℝ) ≤ (13268248558871711/50000000000000000000 : ℝ) := by
    have hpowers : (21267/100000 : ℝ)^5447 ≤ (13268248558871711/50000000000000000000 : ℝ)^1024 := by
      have hnat : (21267 : ℕ)^5447*50000000000000000000^1024 ≤ 13268248558871711^1024*100000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21267 100000 13268248558871711 50000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21267/100000 : ℝ)) (X := (13268248558871711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051438417913709/50000000000000000000 : ℝ) ≤ (10000001934015713/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50000051438417913709/50000000000000000000 : ℝ)^1024 ≤ (10000001934015713/10000000000000000 : ℝ)^5447 := by
      have hnat : (50000051438417913709 : ℕ)^1024*10000000000000000^5447 ≤ 10000001934015713^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051438417913709 50000000000000000000 10000001934015713 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001934015713/10000000000000000 : ℝ)) (X := (50000051438417913709/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026587935535657131/100000000000000000000 : ℝ) ≤ (2000099956333637/2000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (100026587935535657131/100000000000000000000 : ℝ)^1024 ≤ (2000099956333637/2000000000000000 : ℝ)^5447 := by
      have hnat : (100026587935535657131 : ℕ)^1024*2000000000000000^5447 ≤ 2000099956333637^5447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026587935535657131 100000000000000000000 2000099956333637 2000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000099956333637/2000000000000000 : ℝ)) (X := (100026587935535657131/100000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013268248558871711/25000000000000000000 : ℝ) ≤ (10000997629320657/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (25013268248558871711/25000000000000000000 : ℝ)^1024 ≤ (10000997629320657/10000000000000000 : ℝ)^5447 := by
      have hnat : (25013268248558871711 : ℕ)^1024*10000000000000000^5447 ≤ 10000997629320657^5447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013268248558871711 25000000000000000000 10000997629320657 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000997629320657/10000000000000000 : ℝ)) (X := (25013268248558871711/25000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51438417913709/100000000000000000000 : ℝ) ≤ ((4897782790439582997/4898000000000000000 : ℝ)+2*(62230956559/183675000000000 : ℝ)*(6573/100000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (4897782790439582997/4898000000000000000 : ℝ)+2*(62230956559/183675000000000 : ℝ)*(6573/100000 : ℝ)=(10000001934015713/10000000000000000 : ℝ) by norm_num, show 1+2*(51438417913709/100000000000000000000 : ℝ)=(50000051438417913709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13268248558871711/50000000000000000000 : ℝ)+(51438417913709/100000000000000000000 : ℝ) ≤ ((4897782790439582997/4898000000000000000 : ℝ)+(62230956559/183675000000000 : ℝ)*((21267/100000 : ℝ)+(6573/100000 : ℝ)))^(5447/1024 : ℝ) := by
    rw [show (4897782790439582997/4898000000000000000 : ℝ)+(62230956559/183675000000000 : ℝ)*((21267/100000 : ℝ)+(6573/100000 : ℝ))=(2000099956333637/2000000000000000 : ℝ) by norm_num, show 1+(13268248558871711/50000000000000000000 : ℝ)+(51438417913709/100000000000000000000 : ℝ)=(100026587935535657131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13268248558871711/50000000000000000000 : ℝ) ≤ ((4897782790439582997/4898000000000000000 : ℝ)+2*(62230956559/183675000000000 : ℝ)*(21267/100000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (4897782790439582997/4898000000000000000 : ℝ)+2*(62230956559/183675000000000 : ℝ)*(21267/100000 : ℝ)=(10000997629320657/10000000000000000 : ℝ) by norm_num, show 1+2*(13268248558871711/50000000000000000000 : ℝ)=(25013268248558871711/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4897782790439582997/4898000000000000000 : ℝ)*(X 1 0+X 2 0)+(62230956559/183675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (6573/100000 : ℝ)) (hi := (21267/100000 : ℝ)) (c := (4897782790439582997/4898000000000000000 : ℝ)) (alpha := (62230956559/183675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4897782790439582997/4898000000000000000 : ℝ)*(X 0 1+X 2 1)+(62230956559/183675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (6573/100000 : ℝ)) (hi := (21267/100000 : ℝ)) (c := (4897782790439582997/4898000000000000000 : ℝ)) (alpha := (62230956559/183675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4897782790439582997/4898000000000000000 : ℝ)*(X 0 2+X 1 2)+(62230956559/183675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (6573/100000 : ℝ)) (hi := (21267/100000 : ℝ)) (c := (4897782790439582997/4898000000000000000 : ℝ)) (alpha := (62230956559/183675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1343892279/10000000000 : ℝ)*X 0 0+(1093619271/2000000000 : ℝ)*X 0 1+(320747891/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133496041/250000000 : ℝ)*X 1 0+(-379566189/2500000000 : ℝ)*X 1 1+(2565982673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339840247/10000000000 : ℝ)*X 2 0+(2565983143/5000000000 : ℝ)*X 2 1+(-12146123/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2039595269/5000000000 : ℝ)*X 0 0+(717968537/2000000000 : ℝ)*X 0 1+(2303350101/5000000000 : ℝ)*X 0 2+(2039595269/5000000000 : ℝ)*X 1 0+(717968537/2000000000 : ℝ)*X 1 1+(2303350101/5000000000 : ℝ)*X 1 2+(2039595269/5000000000 : ℝ)*X 2 0+(717968537/2000000000 : ℝ)*X 2 1+(2303350101/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268812071/2000000000 : ℝ)*X 0 0+(5135964893/10000000000 : ℝ)*X 0 1+(683004211/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5249860193/10000000000 : ℝ)*X 1 0+(-1186197773/10000000000 : ℝ)*X 1 1+(5464032981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5249860157/10000000000 : ℝ)*X 2 0+(2732016331/5000000000 : ℝ)*X 2 1+(-593099139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4079693937/10000000000 : ℝ)*X 0 0+(1148650583/2500000000 : ℝ)*X 0 1+(3602131083/10000000000 : ℝ)*X 0 2+(4079693937/10000000000 : ℝ)*X 1 0+(1148650583/2500000000 : ℝ)*X 1 1+(3602131083/10000000000 : ℝ)*X 1 2+(4079693937/10000000000 : ℝ)*X 2 0+(1148650583/2500000000 : ℝ)*X 2 1+(3602131083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7032845111075223313463887/478320312500000000000000000000 : ℝ) := by norm_num
    linear_combination (978752853/50000000000000 : ℝ)*(base19) + (1483411001/100000000000000 : ℝ)*(base23) + (67244269/100000000000000 : ℝ)*(lower2) + (138360957/50000000000000 : ℝ)*(upper3) + (228512577/100000000000000 : ℝ)*(lower4) + (30925790437453/1562500000000 : ℝ)*(major0) + (30925790437453/1562500000000 : ℝ)*(major1) + (30925790437453/1562500000000 : ℝ)*(major2) + (2975060146940439/100000000000000 : ℝ)*(sp0) + (1487535199909011/50000000000000 : ℝ)*(sp1) + (371883859239091/12500000000000 : ℝ)*(sp2) + (491712498506599/50000000000000 : ℝ)*(sp3) + (12210383289/100000000000000 : ℝ)*(sp4) + (3331549973/100000000000000 : ℝ)*(sp7) + (983428328563171/100000000000000 : ℝ)*(f.failure) + (185942022332733/6250000000000 : ℝ)*(f.sum) + (76077855451403/36735000000000000000000000000 : ℝ)*base66 + (98466543138342577/22959375000000000000000000000000 : ℝ)*base68 + (50873318452858399/11479687500000000000000000000000 : ℝ)*base69 + (12600294228959863/5739843750000000000000000000000 : ℝ)*base72 + (7257074299061/18367500000000000000000000000 : ℝ)*base73 + (1154914300910351/11479687500000000000000000000000 : ℝ)*base76 + (41540171632391113/5739843750000000000000000000000 : ℝ)*base78 + (229941459095348827/22959375000000000000000000000000 : ℝ)*base80 + (159715748442187/36735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31989231/5000000000000000000000 : ℝ)*base90 + (31989231/5000000000000000000000 : ℝ)*base92 + (31989231/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140200803021734295441455097/48980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81222623/10000000000000 : ℝ)*(base19) + (3058357/250000000000 : ℝ)*(base23) + (130967893/50000000000000 : ℝ)*(upper2) + (119183457/50000000000000 : ℝ)*(upper5) + (405573154369767/20000000000000 : ℝ)*(major0) + (405573154369767/20000000000000 : ℝ)*(major1) + (405573154369767/20000000000000 : ℝ)*(major2) + (23070687/781250000000 : ℝ)*(sp0) + (944763101/12500000000000 : ℝ)*(sp1) + (913449673/25000000000000 : ℝ)*(sp2) + (3048144787213567/100000000000000 : ℝ)*(sp4) + (95254355310327/3125000000000 : ℝ)*(sp5) + (3048142863120011/100000000000000 : ℝ)*(sp6) + (503791854011261/50000000000000 : ℝ)*(sp7) + (503791854011261/50000000000000 : ℝ)*(f.failure) + (1524073870130751/50000000000000 : ℝ)*(f.sum) + (1441014382561/2449000000000000000000000000 : ℝ)*base66 + (72339566549268301/97960000000000000000000000000000 : ℝ)*base68 + (817506212758348301/97960000000000000000000000000000 : ℝ)*base70 + (158221453127571699/97960000000000000000000000000000 : ℝ)*base71 + (822374446003/612250000000000000000000000 : ℝ)*base74 + (218565372283251699/97960000000000000000000000000000 : ℝ)*base75 + (141696211455268301/97960000000000000000000000000000 : ℝ)*base78 + (867531882859948301/97960000000000000000000000000000 : ℝ)*base80 + (781539197957/612250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (26995279/2500000000000000000000 : ℝ)*base89 + (26995279/2500000000000000000000 : ℝ)*base91 + (26995279/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1729_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21267/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6573/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1729_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1729_s2_0 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1346213249/10000000000 : ℝ)*x 0 + (2729224057/5000000000 : ℝ)*x 1 + (514005029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346213249/10000000000 : ℝ)^5455 ≤ (66167223277/781250000000 : ℝ)^4431 := by
    have hnat : (1346213249 : ℕ)^5455*781250000000^4431 ≤ 66167223277^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346213249 10000000000 66167223277 781250000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729224057/5000000000 : ℝ)^5455 ≤ (5932204741957/12500000000000 : ℝ)^4431 := by
    have hnat : (2729224057 : ℕ)^5455*12500000000000^4431 ≤ 5932204741957^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729224057 5000000000 5932204741957 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514005029/1000000000 : ℝ)^5455 ≤ (44072957468107/100000000000000 : ℝ)^4431 := by
    have hnat : (514005029 : ℕ)^5455*100000000000000^4431 ≤ 44072957468107^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514005029 1000000000 44072957468107 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1346213249/10000000000 : ℝ), (2729224057/5000000000 : ℝ), (514005029/1000000000 : ℝ)] ![(66167223277/781250000000 : ℝ), (5932204741957/12500000000000 : ℝ), (44072957468107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1346213249/10000000000 : ℝ)|^5455 ≤ (66167223277/781250000000 : ℝ)^4431
        have hw : |(-1346213249/10000000000 : ℝ)|=(1346213249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729224057/5000000000 : ℝ)|^5455 ≤ (5932204741957/12500000000000 : ℝ)^4431
        have hw : |(2729224057/5000000000 : ℝ)|=(2729224057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514005029/1000000000 : ℝ)|^5455 ≤ (44072957468107/100000000000000 : ℝ)^4431
        have hw : |(514005029/1000000000 : ℝ)|=(514005029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_1 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333575323/625000000 : ℝ)*x 0 + (-1511071239/10000000000 : ℝ)*x 1 + (2570025167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333575323/625000000 : ℝ)^5455 ≤ (11540812910059/25000000000000 : ℝ)^4431 := by
    have hnat : (333575323 : ℕ)^5455*25000000000000^4431 ≤ 11540812910059^4431*625000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333575323 625000000 11540812910059 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1511071239/10000000000 : ℝ)^5455 ≤ (78110323311/800000000000 : ℝ)^4431 := by
    have hnat : (1511071239 : ℕ)^5455*800000000000^4431 ≤ 78110323311^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511071239 10000000000 78110323311 800000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570025167/5000000000 : ℝ)^5455 ≤ (44072957932569/100000000000000 : ℝ)^4431 := by
    have hnat : (2570025167 : ℕ)^5455*100000000000000^4431 ≤ 44072957932569^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570025167 5000000000 44072957932569 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333575323/625000000 : ℝ), (-1511071239/10000000000 : ℝ), (2570025167/5000000000 : ℝ)] ![(11540812910059/25000000000000 : ℝ), (78110323311/800000000000 : ℝ), (44072957932569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333575323/625000000 : ℝ)|^5455 ≤ (11540812910059/25000000000000 : ℝ)^4431
        have hw : |(333575323/625000000 : ℝ)|=(333575323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1511071239/10000000000 : ℝ)|^5455 ≤ (78110323311/800000000000 : ℝ)^4431
        have hw : |(-1511071239/10000000000 : ℝ)|=(1511071239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570025167/5000000000 : ℝ)|^5455 ≤ (44072957932569/100000000000000 : ℝ)^4431
        have hw : |(2570025167/5000000000 : ℝ)|=(2570025167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_2 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337205161/10000000000 : ℝ)*x 0 + (5140050339/10000000000 : ℝ)*x 1 + (-755535621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337205161/10000000000 : ℝ)^5455 ≤ (46163251565699/100000000000000 : ℝ)^4431 := by
    have hnat : (5337205161 : ℕ)^5455*100000000000000^4431 ≤ 46163251565699^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337205161 10000000000 46163251565699 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140050339/10000000000 : ℝ)^5455 ≤ (44072957985349/100000000000000 : ℝ)^4431 := by
    have hnat : (5140050339 : ℕ)^5455*100000000000000^4431 ≤ 44072957985349^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140050339 10000000000 44072957985349 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755535621/5000000000 : ℝ)^5455 ≤ (9763790437739/100000000000000 : ℝ)^4431 := by
    have hnat : (755535621 : ℕ)^5455*100000000000000^4431 ≤ 9763790437739^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755535621 5000000000 9763790437739 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337205161/10000000000 : ℝ), (5140050339/10000000000 : ℝ), (-755535621/5000000000 : ℝ)] ![(46163251565699/100000000000000 : ℝ), (44072957985349/100000000000000 : ℝ), (9763790437739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337205161/10000000000 : ℝ)|^5455 ≤ (46163251565699/100000000000000 : ℝ)^4431
        have hw : |(5337205161/10000000000 : ℝ)|=(5337205161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140050339/10000000000 : ℝ)|^5455 ≤ (44072957985349/100000000000000 : ℝ)^4431
        have hw : |(5140050339/10000000000 : ℝ)|=(5140050339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-755535621/5000000000 : ℝ)|^5455 ≤ (9763790437739/100000000000000 : ℝ)^4431
        have hw : |(-755535621/5000000000 : ℝ)|=(755535621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_3 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16323997/40000000 : ℝ)*x 0 + (3616509259/10000000000 : ℝ)*x 1 + (1144932159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16323997/40000000 : ℝ)^5455 ≤ (33175312061817/100000000000000 : ℝ)^4431 := by
    have hnat : (16323997 : ℕ)^5455*100000000000000^4431 ≤ 33175312061817^4431*40000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16323997 40000000 33175312061817 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3616509259/10000000000 : ℝ)^5455 ≤ (5717954667903/20000000000000 : ℝ)^4431 := by
    have hnat : (3616509259 : ℕ)^5455*20000000000000^4431 ≤ 5717954667903^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3616509259 10000000000 5717954667903 20000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144932159/2500000000 : ℝ)^5455 ≤ (38234914588487/100000000000000 : ℝ)^4431 := by
    have hnat : (1144932159 : ℕ)^5455*100000000000000^4431 ≤ 38234914588487^4431*2500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144932159 2500000000 38234914588487 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16323997/40000000 : ℝ), (3616509259/10000000000 : ℝ), (1144932159/2500000000 : ℝ)] ![(33175312061817/100000000000000 : ℝ), (5717954667903/20000000000000 : ℝ), (38234914588487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16323997/40000000 : ℝ)|^5455 ≤ (33175312061817/100000000000000 : ℝ)^4431
        have hw : |(16323997/40000000 : ℝ)|=(16323997/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3616509259/10000000000 : ℝ)|^5455 ≤ (5717954667903/20000000000000 : ℝ)^4431
        have hw : |(3616509259/10000000000 : ℝ)|=(3616509259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1144932159/2500000000 : ℝ)|^5455 ≤ (38234914588487/100000000000000 : ℝ)^4431
        have hw : |(1144932159/2500000000 : ℝ)|=(1144932159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_4 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168294361/1250000000 : ℝ)*x 0 + (5143640571/10000000000 : ℝ)*x 1 + (5454804297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168294361/1250000000 : ℝ)^5455 ≤ (8470501613627/100000000000000 : ℝ)^4431 := by
    have hnat : (168294361 : ℕ)^5455*100000000000000^4431 ≤ 8470501613627^4431*1250000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168294361 1250000000 8470501613627 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143640571/10000000000 : ℝ)^5455 ≤ (44110859397327/100000000000000 : ℝ)^4431 := by
    have hnat : (5143640571 : ℕ)^5455*100000000000000^4431 ≤ 44110859397327^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143640571 10000000000 44110859397327 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454804297/10000000000 : ℝ)^5455 ≤ (23709319489511/50000000000000 : ℝ)^4431 := by
    have hnat : (5454804297 : ℕ)^5455*50000000000000^4431 ≤ 23709319489511^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454804297 10000000000 23709319489511 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168294361/1250000000 : ℝ), (5143640571/10000000000 : ℝ), (5454804297/10000000000 : ℝ)] ![(8470501613627/100000000000000 : ℝ), (44110859397327/100000000000000 : ℝ), (23709319489511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168294361/1250000000 : ℝ)|^5455 ≤ (8470501613627/100000000000000 : ℝ)^4431
        have hw : |(-168294361/1250000000 : ℝ)|=(168294361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143640571/10000000000 : ℝ)|^5455 ≤ (44110859397327/100000000000000 : ℝ)^4431
        have hw : |(5143640571/10000000000 : ℝ)|=(5143640571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454804297/10000000000 : ℝ)|^5455 ≤ (23709319489511/50000000000000 : ℝ)^4431
        have hw : |(5454804297/10000000000 : ℝ)|=(5454804297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_5 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251989703/10000000000 : ℝ)*x 0 + (-4785269/40000000 : ℝ)*x 1 + (545480437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251989703/10000000000 : ℝ)^5455 ≤ (22628771366101/50000000000000 : ℝ)^4431 := by
    have hnat : (5251989703 : ℕ)^5455*50000000000000^4431 ≤ 22628771366101^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251989703 10000000000 22628771366101 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4785269/40000000 : ℝ)^5455 ≤ (7323817491327/100000000000000 : ℝ)^4431 := by
    have hnat : (4785269 : ℕ)^5455*100000000000000^4431 ≤ 7323817491327^4431*40000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785269 40000000 7323817491327 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545480437/1000000000 : ℝ)^5455 ≤ (5927329970033/12500000000000 : ℝ)^4431 := by
    have hnat : (545480437 : ℕ)^5455*12500000000000^4431 ≤ 5927329970033^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545480437 1000000000 5927329970033 12500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251989703/10000000000 : ℝ), (-4785269/40000000 : ℝ), (545480437/1000000000 : ℝ)] ![(22628771366101/50000000000000 : ℝ), (7323817491327/100000000000000 : ℝ), (5927329970033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251989703/10000000000 : ℝ)|^5455 ≤ (22628771366101/50000000000000 : ℝ)^4431
        have hw : |(5251989703/10000000000 : ℝ)|=(5251989703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4785269/40000000 : ℝ)|^5455 ≤ (7323817491327/100000000000000 : ℝ)^4431
        have hw : |(-4785269/40000000 : ℝ)|=(4785269/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545480437/1000000000 : ℝ)|^5455 ≤ (5927329970033/12500000000000 : ℝ)^4431
        have hw : |(545480437/1000000000 : ℝ)|=(545480437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_6 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262599487/500000000 : ℝ)*x 0 + (5454804311/10000000000 : ℝ)*x 1 + (-1196317283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262599487/500000000 : ℝ)^5455 ≤ (22628771562361/50000000000000 : ℝ)^4431 := by
    have hnat : (262599487 : ℕ)^5455*50000000000000^4431 ≤ 22628771562361^4431*500000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262599487 500000000 22628771562361 50000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454804311/10000000000 : ℝ)^5455 ≤ (47418639128849/100000000000000 : ℝ)^4431 := by
    have hnat : (5454804311 : ℕ)^5455*100000000000000^4431 ≤ 47418639128849^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454804311 10000000000 47418639128849 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196317283/10000000000 : ℝ)^5455 ≤ (183095443501/2500000000000 : ℝ)^4431 := by
    have hnat : (1196317283 : ℕ)^5455*2500000000000^4431 ≤ 183095443501^4431*10000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196317283 10000000000 183095443501 2500000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262599487/500000000 : ℝ), (5454804311/10000000000 : ℝ), (-1196317283/10000000000 : ℝ)] ![(22628771562361/50000000000000 : ℝ), (47418639128849/100000000000000 : ℝ), (183095443501/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262599487/500000000 : ℝ)|^5455 ≤ (22628771562361/50000000000000 : ℝ)^4431
        have hw : |(262599487/500000000 : ℝ)|=(262599487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454804311/10000000000 : ℝ)|^5455 ≤ (47418639128849/100000000000000 : ℝ)^4431
        have hw : |(5454804311/10000000000 : ℝ)|=(5454804311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1196317283/10000000000 : ℝ)|^5455 ≤ (183095443501/2500000000000 : ℝ)^4431
        have hw : |(-1196317283/10000000000 : ℝ)|=(1196317283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1729_s2_7 (p : ℝ) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2040713663/5000000000 : ℝ)*x 0 + (35694273/78125000 : ℝ)*x 1 + (362753291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040713663/5000000000 : ℝ)^5455 ≤ (33179596241233/100000000000000 : ℝ)^4431 := by
    have hnat : (2040713663 : ℕ)^5455*100000000000000^4431 ≤ 33179596241233^4431*5000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040713663 5000000000 33179596241233 100000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35694273/78125000 : ℝ)^5455 ≤ (9530826876121/25000000000000 : ℝ)^4431 := by
    have hnat : (35694273 : ℕ)^5455*25000000000000^4431 ≤ 9530826876121^4431*78125000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35694273 78125000 9530826876121 25000000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362753291/1000000000 : ℝ)^5455 ≤ (896784257557/3125000000000 : ℝ)^4431 := by
    have hnat : (362753291 : ℕ)^5455*3125000000000^4431 ≤ 896784257557^4431*1000000000^5455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362753291 1000000000 896784257557 3125000000000 5455 4431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5455/1024 : ℝ)) 5455 4431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2040713663/5000000000 : ℝ), (35694273/78125000 : ℝ), (362753291/1000000000 : ℝ)] ![(33179596241233/100000000000000 : ℝ), (9530826876121/25000000000000 : ℝ), (896784257557/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2040713663/5000000000 : ℝ)|^5455 ≤ (33179596241233/100000000000000 : ℝ)^4431
        have hw : |(2040713663/5000000000 : ℝ)|=(2040713663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35694273/78125000 : ℝ)|^5455 ≤ (9530826876121/25000000000000 : ℝ)^4431
        have hw : |(35694273/78125000 : ℝ)|=(35694273/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362753291/1000000000 : ℝ)|^5455 ≤ (896784257557/3125000000000 : ℝ)^4431
        have hw : |(362753291/1000000000 : ℝ)|=(362753291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1729_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8481/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3433/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4983/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3433/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4983/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3433/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4983/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3433/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4983/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3433/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4983/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3433/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4983/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4983/50000 : ℝ) ^ (5447/1024 : ℝ) ≤ (470756300693053/100000000000000000000 : ℝ) := by
    have hpowers : (4983/50000 : ℝ)^5447 ≤ (470756300693053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4983 : ℕ)^5447*100000000000000000000^1024 ≤ 470756300693053^1024*50000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4983 50000 470756300693053 100000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4983/50000 : ℝ)) (X := (470756300693053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3433/20000 : ℝ) ^ (5447/1024 : ℝ) ≤ (4244077501312177/50000000000000000000 : ℝ) := by
    have hpowers : (3433/20000 : ℝ)^5447 ≤ (4244077501312177/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3433 : ℕ)^5447*50000000000000000000^1024 ≤ 4244077501312177^1024*20000^5447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3433 20000 4244077501312177 50000000000000000000 5447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3433/20000 : ℝ)) (X := (4244077501312177/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000470756300693053/50000000000000000000 : ℝ) ≤ (10000017699746989/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (50000470756300693053/50000000000000000000 : ℝ)^1024 ≤ (10000017699746989/10000000000000000 : ℝ)^5447 := by
      have hnat : (50000470756300693053 : ℕ)^1024*10000000000000000^5447 ≤ 10000017699746989^5447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000470756300693053 50000000000000000000 10000017699746989 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000017699746989/10000000000000000 : ℝ)) (X := (50000470756300693053/50000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008958911303317407/100000000000000000000 : ℝ) ≤ (10000168415485683/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (100008958911303317407/100000000000000000000 : ℝ)^1024 ≤ (10000168415485683/10000000000000000 : ℝ)^5447 := by
      have hnat : (100008958911303317407 : ℕ)^1024*10000000000000000^5447 ≤ 10000168415485683^5447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008958911303317407 100000000000000000000 10000168415485683 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000168415485683/10000000000000000 : ℝ)) (X := (100008958911303317407/100000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004244077501312177/25000000000000000000 : ℝ) ≤ (10000319131224377/10000000000000000 : ℝ) ^ (5447/1024 : ℝ) := by
    have hpowers : (25004244077501312177/25000000000000000000 : ℝ)^1024 ≤ (10000319131224377/10000000000000000 : ℝ)^5447 := by
      have hnat : (25004244077501312177 : ℕ)^1024*10000000000000000^5447 ≤ 10000319131224377^5447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004244077501312177 25000000000000000000 10000319131224377 10000000000000000 1024 5447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000319131224377/10000000000000000 : ℝ)) (X := (25004244077501312177/25000000000000000000 : ℝ)) (by norm_num) 5447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(470756300693053/100000000000000000000 : ℝ) ≤ ((71987123354374925003/71990000000000000000 : ℝ)+2*(75357869347/359950000000000 : ℝ)*(4983/50000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (71987123354374925003/71990000000000000000 : ℝ)+2*(75357869347/359950000000000 : ℝ)*(4983/50000 : ℝ)=(10000017699746989/10000000000000000 : ℝ) by norm_num, show 1+2*(470756300693053/100000000000000000000 : ℝ)=(50000470756300693053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4244077501312177/50000000000000000000 : ℝ)+(470756300693053/100000000000000000000 : ℝ) ≤ ((71987123354374925003/71990000000000000000 : ℝ)+(75357869347/359950000000000 : ℝ)*((3433/20000 : ℝ)+(4983/50000 : ℝ)))^(5447/1024 : ℝ) := by
    rw [show (71987123354374925003/71990000000000000000 : ℝ)+(75357869347/359950000000000 : ℝ)*((3433/20000 : ℝ)+(4983/50000 : ℝ))=(10000168415485683/10000000000000000 : ℝ) by norm_num, show 1+(4244077501312177/50000000000000000000 : ℝ)+(470756300693053/100000000000000000000 : ℝ)=(100008958911303317407/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4244077501312177/50000000000000000000 : ℝ) ≤ ((71987123354374925003/71990000000000000000 : ℝ)+2*(75357869347/359950000000000 : ℝ)*(3433/20000 : ℝ))^(5447/1024 : ℝ) := by
    rw [show (71987123354374925003/71990000000000000000 : ℝ)+2*(75357869347/359950000000000 : ℝ)*(3433/20000 : ℝ)=(10000319131224377/10000000000000000 : ℝ) by norm_num, show 1+2*(4244077501312177/50000000000000000000 : ℝ)=(25004244077501312177/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71987123354374925003/71990000000000000000 : ℝ)*(X 1 0+X 2 0)+(75357869347/359950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (71987123354374925003/71990000000000000000 : ℝ)) (alpha := (75357869347/359950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71987123354374925003/71990000000000000000 : ℝ)*(X 0 1+X 2 1)+(75357869347/359950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (71987123354374925003/71990000000000000000 : ℝ)) (alpha := (75357869347/359950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71987123354374925003/71990000000000000000 : ℝ)*(X 0 2+X 1 2)+(75357869347/359950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5447/1024 : ℝ)) (lo := (4983/50000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (71987123354374925003/71990000000000000000 : ℝ)) (alpha := (75357869347/359950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1346213249/10000000000 : ℝ)*X 0 0+(2729224057/5000000000 : ℝ)*X 0 1+(514005029/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((333575323/625000000 : ℝ)*X 1 0+(-1511071239/10000000000 : ℝ)*X 1 1+(2570025167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5337205161/10000000000 : ℝ)*X 2 0+(5140050339/10000000000 : ℝ)*X 2 1+(-755535621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16323997/40000000 : ℝ)*X 0 0+(3616509259/10000000000 : ℝ)*X 0 1+(1144932159/2500000000 : ℝ)*X 0 2+(16323997/40000000 : ℝ)*X 1 0+(3616509259/10000000000 : ℝ)*X 1 1+(1144932159/2500000000 : ℝ)*X 1 2+(16323997/40000000 : ℝ)*X 2 0+(3616509259/10000000000 : ℝ)*X 2 1+(1144932159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-168294361/1250000000 : ℝ)*X 0 0+(5143640571/10000000000 : ℝ)*X 0 1+(5454804297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251989703/10000000000 : ℝ)*X 1 0+(-4785269/40000000 : ℝ)*X 1 1+(545480437/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262599487/500000000 : ℝ)*X 2 0+(5454804311/10000000000 : ℝ)*X 2 1+(-1196317283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2040713663/5000000000 : ℝ)*X 0 0+(35694273/78125000 : ℝ)*X 0 1+(362753291/1000000000 : ℝ)*X 0 2+(2040713663/5000000000 : ℝ)*X 1 0+(35694273/78125000 : ℝ)*X 1 1+(362753291/1000000000 : ℝ)*X 1 2+(2040713663/5000000000 : ℝ)*X 2 0+(35694273/78125000 : ℝ)*X 2 1+(362753291/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1729_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2955787920765023477549084511/449937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24987131/2500000000000 : ℝ)*(base19) + (859333267/100000000000000 : ℝ)*(base23) + (36301731/50000000000000 : ℝ)*(lower2) + (37027509/20000000000000 : ℝ)*(upper3) + (43418471/50000000000000 : ℝ)*(upper5) + (261183657846407/12500000000000 : ℝ)*(major0) + (261183657846407/12500000000000 : ℝ)*(major1) + (261183657846407/12500000000000 : ℝ)*(major2) + (785183935473507/25000000000000 : ℝ)*(sp0) + (3140744732004617/100000000000000 : ℝ)*(sp1) + (314074487215659/10000000000000 : ℝ)*(sp2) + (519094195925387/50000000000000 : ℝ)*(sp3) + (2497398957/25000000000000 : ℝ)*(sp4) + (2091612101/50000000000000 : ℝ)*(sp7) + (32443517971093/3125000000000 : ℝ)*(f.failure) + (3140745731489857/100000000000000 : ℝ)*(f.sum) + (32777647650189/8998750000000000000000000000 : ℝ)*base66 + (16565625324280564221/899875000000000000000000000000000 : ℝ)*base67 + (15706067436503814221/899875000000000000000000000000000 : ℝ)*base69 + (8146999653664814221/899875000000000000000000000000000 : ℝ)*base71 + (84913201227119/35995000000000000000000000000 : ℝ)*base73 + (6291529255084064221/899875000000000000000000000000000 : ℝ)*base75 + (7700751340606564221/899875000000000000000000000000000 : ℝ)*base77 + (11730612220159314221/899875000000000000000000000000000 : ℝ)*base79 + (5627571071523/4499375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (928073/156250000000000000000 : ℝ)*base90 + (928073/156250000000000000000 : ℝ)*base92 + (928073/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9225465474792459786625860813/899875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1370586121/100000000000000 : ℝ)*(base19) + (1487307873/100000000000000 : ℝ)*(base23) + (41900291/20000000000000 : ℝ)*(upper3) + (46426371/100000000000000 : ℝ)*(lower4) + (111252749/50000000000000 : ℝ)*(upper5) + (1069016040681757/50000000000000 : ℝ)*(major0) + (1069016040681757/50000000000000 : ℝ)*(major1) + (1069016040681757/50000000000000 : ℝ)*(major2) + (3470305501/25000000000000 : ℝ)*(sp1) + (14231510083/100000000000000 : ℝ)*(sp2) + (642748377027459/20000000000000 : ℝ)*(sp4) + (321372663332917/10000000000000 : ℝ)*(sp5) + (1606863083159669/50000000000000 : ℝ)*(sp6) + (1062321935858359/100000000000000 : ℝ)*(sp7) + (1062321935858359/100000000000000 : ℝ)*(f.failure) + (642748377027459/20000000000000 : ℝ)*(f.sum) + (6123797898543/17997500000000000000000000000 : ℝ)*base65 + (15259463673028429729/3599500000000000000000000000000000 : ℝ)*base68 + (7818472757946429729/3599500000000000000000000000000000 : ℝ)*base70 + (20229980377590929729/3599500000000000000000000000000000 : ℝ)*base72 + (27629482016979/8998750000000000000000000000 : ℝ)*base73 + (25642713060735929729/3599500000000000000000000000000000 : ℝ)*base76 + (2941860122540429729/3599500000000000000000000000000000 : ℝ)*base78 + (13306388580376570271/3599500000000000000000000000000000 : ℝ)*base79 + (21305177312733/17997500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (50481901/5000000000000000000000 : ℝ)*base89 + (50481901/5000000000000000000000 : ℝ)*base91 + (50481901/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1729_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1729_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1729_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1729_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1729_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1729_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5447/1024 : ℝ) ≤ p) (hpb : p ≤ (5455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100630139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8481/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1729_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1076_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:13:53.424878+00:00
-- url     : https://prove2.me/submissions/9d36c1ba-021a-4e1d-b2a9-f3ab3b83038e

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
theorem support_rectangle_w1076_s0_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-956437619/5000000000 : ℝ)*x 0 + (6069711433/10000000000 : ℝ)*x 1 + (1193017227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956437619/5000000000 : ℝ)^8269 ≤ (5548588142681/50000000000000 : ℝ)^6221 := by
    have hnat : (956437619 : ℕ)^8269*50000000000000^6221 ≤ 5548588142681^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956437619 5000000000 5548588142681 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6069711433/10000000000 : ℝ)^8269 ≤ (51497403594331/100000000000000 : ℝ)^6221 := by
    have hnat : (6069711433 : ℕ)^8269*100000000000000^6221 ≤ 51497403594331^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6069711433 10000000000 51497403594331 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193017227/2500000000 : ℝ)^8269 ≤ (37405420112871/100000000000000 : ℝ)^6221 := by
    have hnat : (1193017227 : ℕ)^8269*100000000000000^6221 ≤ 37405420112871^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193017227 2500000000 37405420112871 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956437619/5000000000 : ℝ), (6069711433/10000000000 : ℝ), (1193017227/2500000000 : ℝ)] ![(5548588142681/50000000000000 : ℝ), (51497403594331/100000000000000 : ℝ), (37405420112871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956437619/5000000000 : ℝ)|^8269 ≤ (5548588142681/50000000000000 : ℝ)^6221
        have hw : |(-956437619/5000000000 : ℝ)|=(956437619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6069711433/10000000000 : ℝ)|^8269 ≤ (51497403594331/100000000000000 : ℝ)^6221
        have hw : |(6069711433/10000000000 : ℝ)|=(6069711433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193017227/2500000000 : ℝ)|^8269 ≤ (37405420112871/100000000000000 : ℝ)^6221
        have hw : |(1193017227/2500000000 : ℝ)|=(1193017227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520509971/10000000000 : ℝ)*x 0 + (-2659509411/10000000000 : ℝ)*x 1 + (4772068821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520509971/10000000000 : ℝ)^8269 ≤ (45398009327437/100000000000000 : ℝ)^6221 := by
    have hnat : (5520509971 : ℕ)^8269*100000000000000^6221 ≤ 45398009327437^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520509971 10000000000 45398009327437 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659509411/10000000000 : ℝ)^8269 ≤ (687862857947/4000000000000 : ℝ)^6221 := by
    have hnat : (2659509411 : ℕ)^8269*4000000000000^6221 ≤ 687862857947^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659509411 10000000000 687862857947 4000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772068821/10000000000 : ℝ)^8269 ≤ (37405419206429/100000000000000 : ℝ)^6221 := by
    have hnat : (4772068821 : ℕ)^8269*100000000000000^6221 ≤ 37405419206429^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772068821 10000000000 37405419206429 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520509971/10000000000 : ℝ), (-2659509411/10000000000 : ℝ), (4772068821/10000000000 : ℝ)] ![(45398009327437/100000000000000 : ℝ), (687862857947/4000000000000 : ℝ), (37405419206429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520509971/10000000000 : ℝ)|^8269 ≤ (45398009327437/100000000000000 : ℝ)^6221
        have hw : |(5520509971/10000000000 : ℝ)|=(5520509971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2659509411/10000000000 : ℝ)|^8269 ≤ (687862857947/4000000000000 : ℝ)^6221
        have hw : |(-2659509411/10000000000 : ℝ)|=(2659509411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772068821/10000000000 : ℝ)|^8269 ≤ (37405419206429/100000000000000 : ℝ)^6221
        have hw : |(4772068821/10000000000 : ℝ)|=(4772068821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2760255887/5000000000 : ℝ)*x 0 + (4772067017/10000000000 : ℝ)*x 1 + (-531901861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760255887/5000000000 : ℝ)^8269 ≤ (45398029035601/100000000000000 : ℝ)^6221 := by
    have hnat : (2760255887 : ℕ)^8269*100000000000000^6221 ≤ 45398029035601^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760255887 5000000000 45398029035601 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4772067017/10000000000 : ℝ)^8269 ≤ (37405400410789/100000000000000 : ℝ)^6221 := by
    have hnat : (4772067017 : ℕ)^8269*100000000000000^6221 ≤ 37405400410789^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772067017 10000000000 37405400410789 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531901861/2000000000 : ℝ)^8269 ≤ (17196570537631/100000000000000 : ℝ)^6221 := by
    have hnat : (531901861 : ℕ)^8269*100000000000000^6221 ≤ 17196570537631^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531901861 2000000000 17196570537631 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760255887/5000000000 : ℝ), (4772067017/10000000000 : ℝ), (-531901861/2000000000 : ℝ)] ![(45398029035601/100000000000000 : ℝ), (37405400410789/100000000000000 : ℝ), (17196570537631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760255887/5000000000 : ℝ)|^8269 ≤ (45398029035601/100000000000000 : ℝ)^6221
        have hw : |(2760255887/5000000000 : ℝ)|=(2760255887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4772067017/10000000000 : ℝ)|^8269 ≤ (37405400410789/100000000000000 : ℝ)^6221
        have hw : |(4772067017/10000000000 : ℝ)|=(4772067017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531901861/2000000000 : ℝ)|^8269 ≤ (17196570537631/100000000000000 : ℝ)^6221
        have hw : |(-531901861/2000000000 : ℝ)|=(531901861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10515947/25000000 : ℝ)*x 0 + (781085009/2500000000 : ℝ)*x 1 + (2836292631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10515947/25000000 : ℝ)^8269 ≤ (31629781318893/100000000000000 : ℝ)^6221 := by
    have hnat : (10515947 : ℕ)^8269*100000000000000^6221 ≤ 31629781318893^6221*25000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10515947 25000000 31629781318893 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781085009/2500000000 : ℝ)^8269 ≤ (4260483808587/20000000000000 : ℝ)^6221 := by
    have hnat : (781085009 : ℕ)^8269*20000000000000^6221 ≤ 4260483808587^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781085009 2500000000 4260483808587 20000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2836292631/5000000000 : ℝ)^8269 ≤ (23533899807363/50000000000000 : ℝ)^6221 := by
    have hnat : (2836292631 : ℕ)^8269*50000000000000^6221 ≤ 23533899807363^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836292631 5000000000 23533899807363 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10515947/25000000 : ℝ), (781085009/2500000000 : ℝ), (2836292631/5000000000 : ℝ)] ![(31629781318893/100000000000000 : ℝ), (4260483808587/20000000000000 : ℝ), (23533899807363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10515947/25000000 : ℝ)|^8269 ≤ (31629781318893/100000000000000 : ℝ)^6221
        have hw : |(10515947/25000000 : ℝ)|=(10515947/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781085009/2500000000 : ℝ)|^8269 ≤ (4260483808587/20000000000000 : ℝ)^6221
        have hw : |(781085009/2500000000 : ℝ)|=(781085009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2836292631/5000000000 : ℝ)|^8269 ≤ (23533899807363/50000000000000 : ℝ)^6221
        have hw : |(2836292631/5000000000 : ℝ)|=(2836292631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-239777457/1250000000 : ℝ)*x 0 + (480557111/1000000000 : ℝ)*x 1 + (3017517697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239777457/1250000000 : ℝ)^8269 ≤ (11138406785737/100000000000000 : ℝ)^6221 := by
    have hnat : (239777457 : ℕ)^8269*100000000000000^6221 ≤ 11138406785737^6221*1250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239777457 1250000000 11138406785737 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480557111/1000000000 : ℝ)^8269 ≤ (37754877937493/100000000000000 : ℝ)^6221 := by
    have hnat : (480557111 : ℕ)^8269*100000000000000^6221 ≤ 37754877937493^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480557111 1000000000 37754877937493 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3017517697/5000000000 : ℝ)^8269 ≤ (51106715257101/100000000000000 : ℝ)^6221 := by
    have hnat : (3017517697 : ℕ)^8269*100000000000000^6221 ≤ 51106715257101^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017517697 5000000000 51106715257101 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239777457/1250000000 : ℝ), (480557111/1000000000 : ℝ), (3017517697/5000000000 : ℝ)] ![(11138406785737/100000000000000 : ℝ), (37754877937493/100000000000000 : ℝ), (51106715257101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239777457/1250000000 : ℝ)|^8269 ≤ (11138406785737/100000000000000 : ℝ)^6221
        have hw : |(-239777457/1250000000 : ℝ)|=(239777457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(480557111/1000000000 : ℝ)|^8269 ≤ (37754877937493/100000000000000 : ℝ)^6221
        have hw : |(480557111/1000000000 : ℝ)|=(480557111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3017517697/5000000000 : ℝ)|^8269 ≤ (51106715257101/100000000000000 : ℝ)^6221
        have hw : |(3017517697/5000000000 : ℝ)|=(3017517697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20673021/40000000 : ℝ)*x 0 + (-698272979/5000000000 : ℝ)*x 1 + (6035033351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20673021/40000000 : ℝ)^8269 ≤ (4158863130153/10000000000000 : ℝ)^6221 := by
    have hnat : (20673021 : ℕ)^8269*10000000000000^6221 ≤ 4158863130153^6221*40000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20673021 40000000 4158863130153 10000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698272979/5000000000 : ℝ)^8269 ≤ (7304676427949/100000000000000 : ℝ)^6221 := by
    have hnat : (698272979 : ℕ)^8269*100000000000000^6221 ≤ 7304676427949^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698272979 5000000000 7304676427949 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6035033351/10000000000 : ℝ)^8269 ≤ (51106692260731/100000000000000 : ℝ)^6221 := by
    have hnat : (6035033351 : ℕ)^8269*100000000000000^6221 ≤ 51106692260731^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035033351 10000000000 51106692260731 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20673021/40000000 : ℝ), (-698272979/5000000000 : ℝ), (6035033351/10000000000 : ℝ)] ![(4158863130153/10000000000000 : ℝ), (7304676427949/100000000000000 : ℝ), (51106692260731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20673021/40000000 : ℝ)|^8269 ≤ (4158863130153/10000000000000 : ℝ)^6221
        have hw : |(20673021/40000000 : ℝ)|=(20673021/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698272979/5000000000 : ℝ)|^8269 ≤ (7304676427949/100000000000000 : ℝ)^6221
        have hw : |(-698272979/5000000000 : ℝ)|=(698272979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6035033351/10000000000 : ℝ)|^8269 ≤ (51106692260731/100000000000000 : ℝ)^6221
        have hw : |(6035033351/10000000000 : ℝ)|=(6035033351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168255143/10000000000 : ℝ)*x 0 + (603503489/1000000000 : ℝ)*x 1 + (-1396543629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168255143/10000000000 : ℝ)^8269 ≤ (41588630157053/100000000000000 : ℝ)^6221 := by
    have hnat : (5168255143 : ℕ)^8269*100000000000000^6221 ≤ 41588630157053^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168255143 10000000000 41588630157053 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603503489/1000000000 : ℝ)^8269 ≤ (51106709583987/100000000000000 : ℝ)^6221 := by
    have hnat : (603503489 : ℕ)^8269*100000000000000^6221 ≤ 51106709583987^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603503489 1000000000 51106709583987 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396543629/10000000000 : ℝ)^8269 ≤ (7304660235673/100000000000000 : ℝ)^6221 := by
    have hnat : (1396543629 : ℕ)^8269*100000000000000^6221 ≤ 7304660235673^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396543629 10000000000 7304660235673 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168255143/10000000000 : ℝ), (603503489/1000000000 : ℝ), (-1396543629/10000000000 : ℝ)] ![(41588630157053/100000000000000 : ℝ), (51106709583987/100000000000000 : ℝ), (7304660235673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168255143/10000000000 : ℝ)|^8269 ≤ (41588630157053/100000000000000 : ℝ)^6221
        have hw : |(5168255143/10000000000 : ℝ)|=(5168255143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603503489/1000000000 : ℝ)|^8269 ≤ (51106709583987/100000000000000 : ℝ)^6221
        have hw : |(603503489/1000000000 : ℝ)|=(603503489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1396543629/10000000000 : ℝ)|^8269 ≤ (7304660235673/100000000000000 : ℝ)^6221
        have hw : |(-1396543629/10000000000 : ℝ)|=(1396543629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s0_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (843374727/2000000000 : ℝ)*x 0 + (2803395581/5000000000 : ℝ)*x 1 + (3192432717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843374727/2000000000 : ℝ)^8269 ≤ (7933679929617/25000000000000 : ℝ)^6221 := by
    have hnat : (843374727 : ℕ)^8269*25000000000000^6221 ≤ 7933679929617^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843374727 2000000000 7933679929617 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803395581/5000000000 : ℝ)^8269 ≤ (46343546280517/100000000000000 : ℝ)^6221 := by
    have hnat : (2803395581 : ℕ)^8269*100000000000000^6221 ≤ 46343546280517^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803395581 5000000000 46343546280517 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192432717/10000000000 : ℝ)^8269 ≤ (2740216749223/12500000000000 : ℝ)^6221 := by
    have hnat : (3192432717 : ℕ)^8269*12500000000000^6221 ≤ 2740216749223^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192432717 10000000000 2740216749223 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843374727/2000000000 : ℝ), (2803395581/5000000000 : ℝ), (3192432717/10000000000 : ℝ)] ![(7933679929617/25000000000000 : ℝ), (46343546280517/100000000000000 : ℝ), (2740216749223/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843374727/2000000000 : ℝ)|^8269 ≤ (7933679929617/25000000000000 : ℝ)^6221
        have hw : |(843374727/2000000000 : ℝ)|=(843374727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803395581/5000000000 : ℝ)|^8269 ≤ (46343546280517/100000000000000 : ℝ)^6221
        have hw : |(2803395581/5000000000 : ℝ)|=(2803395581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192432717/10000000000 : ℝ)|^8269 ≤ (2740216749223/12500000000000 : ℝ)^6221
        have hw : |(3192432717/10000000000 : ℝ)|=(3192432717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (139/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/10000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpowlo : (0 : ℝ) ^ (2067/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2067 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2067*1^512 ≤ 0^512*1^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2067/512 : ℝ) ≤ (618603921766072609/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2067 ≤ (618603921766072609/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2067*25000000000000000000^512 ≤ 618603921766072609^512*5^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 618603921766072609 25000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (618603921766072609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2067 := by
      have hnat : (1 : ℕ)^512*1^2067 ≤ 1^2067*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25618603921766072609/25000000000000000000 : ℝ) ≤ (10060729402108513/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (25618603921766072609/25000000000000000000 : ℝ)^512 ≤ (10060729402108513/10000000000000000 : ℝ)^2067 := by
      have hnat : (25618603921766072609 : ℕ)^512*10000000000000000^2067 ≤ 10060729402108513^2067*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25618603921766072609 25000000000000000000 10060729402108513 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060729402108513/10000000000000000 : ℝ)) (X := (25618603921766072609/25000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13118603921766072609/12500000000000000000 : ℝ) ≤ (5060729402108513/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (13118603921766072609/12500000000000000000 : ℝ)^512 ≤ (5060729402108513/5000000000000000 : ℝ)^2067 := by
      have hnat : (13118603921766072609 : ℕ)^512*5000000000000000^2067 ≤ 5060729402108513^2067*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13118603921766072609 12500000000000000000 5060729402108513 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060729402108513/5000000000000000 : ℝ)) (X := (13118603921766072609/12500000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60729402108513/4000000000000000 : ℝ)*(0 : ℝ))^(2067/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60729402108513/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(618603921766072609/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60729402108513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (1 : ℝ)+(60729402108513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060729402108513/10000000000000000 : ℝ) by norm_num, show 1+(618603921766072609/25000000000000000000 : ℝ)+(0 : ℝ)=(25618603921766072609/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(618603921766072609/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60729402108513/4000000000000000 : ℝ)*(2/5 : ℝ))^(2067/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60729402108513/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060729402108513/5000000000000000 : ℝ) by norm_num, show 1+2*(618603921766072609/25000000000000000000 : ℝ)=(13118603921766072609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60729402108513/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60729402108513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60729402108513/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60729402108513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60729402108513/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60729402108513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-956437619/5000000000 : ℝ)*X 0 0+(6069711433/10000000000 : ℝ)*X 0 1+(1193017227/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520509971/10000000000 : ℝ)*X 1 0+(-2659509411/10000000000 : ℝ)*X 1 1+(4772068821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760255887/5000000000 : ℝ)*X 2 0+(4772067017/10000000000 : ℝ)*X 2 1+(-531901861/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((10515947/25000000 : ℝ)*X 0 0+(781085009/2500000000 : ℝ)*X 0 1+(2836292631/5000000000 : ℝ)*X 0 2+(10515947/25000000 : ℝ)*X 1 0+(781085009/2500000000 : ℝ)*X 1 1+(2836292631/5000000000 : ℝ)*X 1 2+(10515947/25000000 : ℝ)*X 2 0+(781085009/2500000000 : ℝ)*X 2 1+(2836292631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-239777457/1250000000 : ℝ)*X 0 0+(480557111/1000000000 : ℝ)*X 0 1+(3017517697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20673021/40000000 : ℝ)*X 1 0+(-698272979/5000000000 : ℝ)*X 1 1+(6035033351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168255143/10000000000 : ℝ)*X 2 0+(603503489/1000000000 : ℝ)*X 2 1+(-1396543629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((843374727/2000000000 : ℝ)*X 0 0+(2803395581/5000000000 : ℝ)*X 0 1+(3192432717/10000000000 : ℝ)*X 0 2+(843374727/2000000000 : ℝ)*X 1 0+(2803395581/5000000000 : ℝ)*X 1 1+(3192432717/10000000000 : ℝ)*X 1 2+(843374727/2000000000 : ℝ)*X 2 0+(2803395581/5000000000 : ℝ)*X 2 1+(3192432717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80874538931256797303619/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33004477/10000000000000 : ℝ)*(base19) + (468002931/100000000000000 : ℝ)*(base23) + (28746621/50000000000000 : ℝ)*(base24) + (79260163/100000000000000 : ℝ)*(base61) + (15522739/50000000000000 : ℝ)*(upper4) + (58152928476907/10000000000000 : ℝ)*(major0) + (58152928476907/10000000000000 : ℝ)*(major1) + (58152928476907/10000000000000 : ℝ)*(major2) + (770629387067489/100000000000000 : ℝ)*(sp0) + (385315185063411/50000000000000 : ℝ)*(sp1) + (770630174675419/100000000000000 : ℝ)*(sp2) + (196213573052837/50000000000000 : ℝ)*(sp3) + (1313104103/100000000000000 : ℝ)*(sp4) + (147117493/25000000000000 : ℝ)*(sp7) + (196213867287823/50000000000000 : ℝ)*(f.failure) + (96328837521449/12500000000000 : ℝ)*(f.sum) + (47697159209291/20000000000000000000000000000 : ℝ)*base65 + (278437283190709/40000000000000000000000000000 : ℝ)*base68 + (149472735630709/40000000000000000000000000000 : ℝ)*base70 + (42653765329291/40000000000000000000000000000 : ℝ)*base71 + (128441169110709/20000000000000000000000000000 : ℝ)*base74 + (66107266350709/40000000000000000000000000000 : ℝ)*base76 + (190639880430709/40000000000000000000000000000 : ℝ)*base78 + (21052845430709/40000000000000000000000000000 : ℝ)*base80 + (46884105730709/20000000000000000000000000000 : ℝ)*base82 + (39760853/5000000000000000000000 : ℝ)*base89 + (39760853/5000000000000000000000 : ℝ)*base91 + (39760853/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (220792077186900621048789/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375969621/50000000000000 : ℝ)*(base19) + (983263537/100000000000000 : ℝ)*(base23) + (208492801/100000000000000 : ℝ)*(base39) + (49324929/50000000000000 : ℝ)*(base45) + (33321769/100000000000000 : ℝ)*(upper3) + (289930359/100000000000000 : ℝ)*(upper5) + (613774809849299/100000000000000 : ℝ)*(major0) + (613774809849299/100000000000000 : ℝ)*(major1) + (306887300678249/50000000000000 : ℝ)*(major2) + (671904197/100000000000000 : ℝ)*(sp2) + (162672319258429/20000000000000 : ℝ)*(sp4) + (813360844352903/100000000000000 : ℝ)*(sp5) + (813360149617211/100000000000000 : ℝ)*(sp6) + (414187667718929/100000000000000 : ℝ)*(sp7) + (414187667718929/100000000000000 : ℝ)*(f.failure) + (162672360956989/20000000000000 : ℝ)*(f.sum) + (6747650649861/400000000000000000000000000000 : ℝ)*base65 + (927988307233737/200000000000000000000000000000 : ℝ)*base67 + (2591261714217613/400000000000000000000000000000 : ℝ)*base70 + (303230063833737/200000000000000000000000000000 : ℝ)*base71 + (1217165799049861/400000000000000000000000000000 : ℝ)*base73 + (4743056843417613/400000000000000000000000000000 : ℝ)*base76 + (959882948582387/400000000000000000000000000000 : ℝ)*base77 + (810583320182387/400000000000000000000000000000 : ℝ)*base79 + (1195459282817613/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7988619/10000000000000000000000 : ℝ)*base89 + (7988619/10000000000000000000000 : ℝ)*base91 + (7988619/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1076_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1076_s1_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122294061/10000000000 : ℝ)*x 0 + (285975899/500000000 : ℝ)*x 1 + (4988156523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122294061/10000000000 : ℝ)^8269 ≤ (6370226708913/50000000000000 : ℝ)^6221 := by
    have hnat : (2122294061 : ℕ)^8269*50000000000000^6221 ≤ 6370226708913^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122294061 10000000000 6370226708913 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285975899/500000000 : ℝ)^8269 ≤ (47586123616433/100000000000000 : ℝ)^6221 := by
    have hnat : (285975899 : ℕ)^8269*100000000000000^6221 ≤ 47586123616433^6221*500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285975899 500000000 47586123616433 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988156523/10000000000 : ℝ)^8269 ≤ (19836711477939/50000000000000 : ℝ)^6221 := by
    have hnat : (4988156523 : ℕ)^8269*50000000000000^6221 ≤ 19836711477939^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988156523 10000000000 19836711477939 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122294061/10000000000 : ℝ), (285975899/500000000 : ℝ), (4988156523/10000000000 : ℝ)] ![(6370226708913/50000000000000 : ℝ), (47586123616433/100000000000000 : ℝ), (19836711477939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122294061/10000000000 : ℝ)|^8269 ≤ (6370226708913/50000000000000 : ℝ)^6221
        have hw : |(-2122294061/10000000000 : ℝ)|=(2122294061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285975899/500000000 : ℝ)|^8269 ≤ (47586123616433/100000000000000 : ℝ)^6221
        have hw : |(285975899/500000000 : ℝ)|=(285975899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988156523/10000000000 : ℝ)|^8269 ≤ (19836711477939/50000000000000 : ℝ)^6221
        have hw : |(4988156523/10000000000 : ℝ)|=(4988156523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42365301/78125000 : ℝ)*x 0 + (-1259167023/5000000000 : ℝ)*x 1 + (4988156817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42365301/78125000 : ℝ)^8269 ≤ (44332638358699/100000000000000 : ℝ)^6221 := by
    have hnat : (42365301 : ℕ)^8269*100000000000000^6221 ≤ 44332638358699^6221*78125000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42365301 78125000 44332638358699 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259167023/5000000000 : ℝ)^8269 ≤ (7996967781501/50000000000000 : ℝ)^6221 := by
    have hnat : (1259167023 : ℕ)^8269*50000000000000^6221 ≤ 7996967781501^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259167023 5000000000 7996967781501 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988156817/10000000000 : ℝ)^8269 ≤ (9918356516003/25000000000000 : ℝ)^6221 := by
    have hnat : (4988156817 : ℕ)^8269*25000000000000^6221 ≤ 9918356516003^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988156817 10000000000 9918356516003 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42365301/78125000 : ℝ), (-1259167023/5000000000 : ℝ), (4988156817/10000000000 : ℝ)] ![(44332638358699/100000000000000 : ℝ), (7996967781501/50000000000000 : ℝ), (9918356516003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42365301/78125000 : ℝ)|^8269 ≤ (44332638358699/100000000000000 : ℝ)^6221
        have hw : |(42365301/78125000 : ℝ)|=(42365301/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1259167023/5000000000 : ℝ)|^8269 ≤ (7996967781501/50000000000000 : ℝ)^6221
        have hw : |(-1259167023/5000000000 : ℝ)|=(1259167023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988156817/10000000000 : ℝ)|^8269 ≤ (9918356516003/25000000000000 : ℝ)^6221
        have hw : |(4988156817/10000000000 : ℝ)|=(4988156817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711379609/5000000000 : ℝ)*x 0 + (2494078033/5000000000 : ℝ)*x 1 + (-1259167049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711379609/5000000000 : ℝ)^8269 ≤ (8866529171339/20000000000000 : ℝ)^6221 := by
    have hnat : (2711379609 : ℕ)^8269*20000000000000^6221 ≤ 8866529171339^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711379609 5000000000 8866529171339 20000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2494078033/5000000000 : ℝ)^8269 ≤ (39673418124527/100000000000000 : ℝ)^6221 := by
    have hnat : (2494078033 : ℕ)^8269*100000000000000^6221 ≤ 39673418124527^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494078033 5000000000 39673418124527 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259167049/5000000000 : ℝ)^8269 ≤ (1999242000247/12500000000000 : ℝ)^6221 := by
    have hnat : (1259167049 : ℕ)^8269*12500000000000^6221 ≤ 1999242000247^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259167049 5000000000 1999242000247 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711379609/5000000000 : ℝ), (2494078033/5000000000 : ℝ), (-1259167049/5000000000 : ℝ)] ![(8866529171339/20000000000000 : ℝ), (39673418124527/100000000000000 : ℝ), (1999242000247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711379609/5000000000 : ℝ)|^8269 ≤ (8866529171339/20000000000000 : ℝ)^6221
        have hw : |(2711379609/5000000000 : ℝ)|=(2711379609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2494078033/5000000000 : ℝ)|^8269 ≤ (39673418124527/100000000000000 : ℝ)^6221
        have hw : |(2494078033/5000000000 : ℝ)|=(2494078033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1259167049/5000000000 : ℝ)|^8269 ≤ (1999242000247/12500000000000 : ℝ)^6221
        have hw : |(-1259167049/5000000000 : ℝ)|=(1259167049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2161487731/5000000000 : ℝ)*x 0 + (1832243679/5000000000 : ℝ)*x 1 + (637587327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161487731/5000000000 : ℝ)^8269 ≤ (2050027730717/6250000000000 : ℝ)^6221 := by
    have hnat : (2161487731 : ℕ)^8269*6250000000000^6221 ≤ 2050027730717^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161487731 5000000000 2050027730717 6250000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1832243679/5000000000 : ℝ)^8269 ≤ (13165977446491/50000000000000 : ℝ)^6221 := by
    have hnat : (1832243679 : ℕ)^8269*50000000000000^6221 ≤ 13165977446491^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832243679 5000000000 13165977446491 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637587327/1250000000 : ℝ)^8269 ≤ (40867601400841/100000000000000 : ℝ)^6221 := by
    have hnat : (637587327 : ℕ)^8269*100000000000000^6221 ≤ 40867601400841^6221*1250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637587327 1250000000 40867601400841 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161487731/5000000000 : ℝ), (1832243679/5000000000 : ℝ), (637587327/1250000000 : ℝ)] ![(2050027730717/6250000000000 : ℝ), (13165977446491/50000000000000 : ℝ), (40867601400841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161487731/5000000000 : ℝ)|^8269 ≤ (2050027730717/6250000000000 : ℝ)^6221
        have hw : |(2161487731/5000000000 : ℝ)|=(2161487731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1832243679/5000000000 : ℝ)|^8269 ≤ (13165977446491/50000000000000 : ℝ)^6221
        have hw : |(1832243679/5000000000 : ℝ)|=(1832243679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637587327/1250000000 : ℝ)|^8269 ≤ (40867601400841/100000000000000 : ℝ)^6221
        have hw : |(637587327/1250000000 : ℝ)|=(637587327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123197299/10000000000 : ℝ)*x 0 + (624799553/1250000000 : ℝ)*x 1 + (5709070853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123197299/10000000000 : ℝ)^8269 ≤ (1593457656397/12500000000000 : ℝ)^6221 := by
    have hnat : (2123197299 : ℕ)^8269*12500000000000^6221 ≤ 1593457656397^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123197299 10000000000 1593457656397 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624799553/1250000000 : ℝ)^8269 ≤ (39781714564877/100000000000000 : ℝ)^6221 := by
    have hnat : (624799553 : ℕ)^8269*100000000000000^6221 ≤ 39781714564877^6221*1250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624799553 1250000000 39781714564877 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5709070853/10000000000 : ℝ)^8269 ≤ (23735312083343/50000000000000 : ℝ)^6221 := by
    have hnat : (5709070853 : ℕ)^8269*50000000000000^6221 ≤ 23735312083343^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5709070853 10000000000 23735312083343 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123197299/10000000000 : ℝ), (624799553/1250000000 : ℝ), (5709070853/10000000000 : ℝ)] ![(1593457656397/12500000000000 : ℝ), (39781714564877/100000000000000 : ℝ), (23735312083343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123197299/10000000000 : ℝ)|^8269 ≤ (1593457656397/12500000000000 : ℝ)^6221
        have hw : |(-2123197299/10000000000 : ℝ)|=(2123197299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624799553/1250000000 : ℝ)|^8269 ≤ (39781714564877/100000000000000 : ℝ)^6221
        have hw : |(624799553/1250000000 : ℝ)|=(624799553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5709070853/10000000000 : ℝ)|^8269 ≤ (23735312083343/50000000000000 : ℝ)^6221
        have hw : |(5709070853/10000000000 : ℝ)|=(5709070853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308970523/2500000000 : ℝ)*x 0 + (-449354931/2500000000 : ℝ)*x 1 + (356816933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308970523/2500000000 : ℝ)^8269 ≤ (21156762440687/50000000000000 : ℝ)^6221 := by
    have hnat : (1308970523 : ℕ)^8269*50000000000000^6221 ≤ 21156762440687^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308970523 2500000000 21156762440687 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449354931/2500000000 : ℝ)^8269 ≤ (10215850113161/100000000000000 : ℝ)^6221 := by
    have hnat : (449354931 : ℕ)^8269*100000000000000^6221 ≤ 10215850113161^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449354931 2500000000 10215850113161 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356816933/625000000 : ℝ)^8269 ≤ (5933828124451/12500000000000 : ℝ)^6221 := by
    have hnat : (356816933 : ℕ)^8269*12500000000000^6221 ≤ 5933828124451^6221*625000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356816933 625000000 5933828124451 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308970523/2500000000 : ℝ), (-449354931/2500000000 : ℝ), (356816933/625000000 : ℝ)] ![(21156762440687/50000000000000 : ℝ), (10215850113161/100000000000000 : ℝ), (5933828124451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308970523/2500000000 : ℝ)|^8269 ≤ (21156762440687/50000000000000 : ℝ)^6221
        have hw : |(1308970523/2500000000 : ℝ)|=(1308970523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449354931/2500000000 : ℝ)|^8269 ≤ (10215850113161/100000000000000 : ℝ)^6221
        have hw : |(-449354931/2500000000 : ℝ)|=(449354931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356816933/625000000 : ℝ)|^8269 ≤ (5933828124451/12500000000000 : ℝ)^6221
        have hw : |(356816933/625000000 : ℝ)|=(356816933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617940967/5000000000 : ℝ)*x 0 + (5709070873/10000000000 : ℝ)*x 1 + (-1797420027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617940967/5000000000 : ℝ)^8269 ≤ (846270463683/2000000000000 : ℝ)^6221 := by
    have hnat : (2617940967 : ℕ)^8269*2000000000000^6221 ≤ 846270463683^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617940967 5000000000 846270463683 2000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5709070873/10000000000 : ℝ)^8269 ≤ (11867656096933/25000000000000 : ℝ)^6221 := by
    have hnat : (5709070873 : ℕ)^8269*25000000000000^6221 ≤ 11867656096933^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5709070873 10000000000 11867656096933 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1797420027/10000000000 : ℝ)^8269 ≤ (5107926201119/50000000000000 : ℝ)^6221 := by
    have hnat : (1797420027 : ℕ)^8269*50000000000000^6221 ≤ 5107926201119^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797420027 10000000000 5107926201119 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617940967/5000000000 : ℝ), (5709070873/10000000000 : ℝ), (-1797420027/10000000000 : ℝ)] ![(846270463683/2000000000000 : ℝ), (11867656096933/25000000000000 : ℝ), (5107926201119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617940967/5000000000 : ℝ)|^8269 ≤ (846270463683/2000000000000 : ℝ)^6221
        have hw : |(2617940967/5000000000 : ℝ)|=(2617940967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5709070873/10000000000 : ℝ)|^8269 ≤ (11867656096933/25000000000000 : ℝ)^6221
        have hw : |(5709070873/10000000000 : ℝ)|=(5709070873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1797420027/10000000000 : ℝ)|^8269 ≤ (5107926201119/50000000000000 : ℝ)^6221
        have hw : |(-1797420027/10000000000 : ℝ)|=(1797420027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s1_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864949683/2000000000 : ℝ)*x 0 + (635073803/1250000000 : ℝ)*x 1 + (3685002587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864949683/2000000000 : ℝ)^8269 ≤ (32818325699111/100000000000000 : ℝ)^6221 := by
    have hnat : (864949683 : ℕ)^8269*100000000000000^6221 ≤ 32818325699111^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864949683 2000000000 32818325699111 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635073803/1250000000 : ℝ)^8269 ≤ (20326795928333/50000000000000 : ℝ)^6221 := by
    have hnat : (635073803 : ℕ)^8269*50000000000000^6221 ≤ 20326795928333^6221*1250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635073803 1250000000 20326795928333 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685002587/10000000000 : ℝ)^8269 ≤ (26528082423507/100000000000000 : ℝ)^6221 := by
    have hnat : (3685002587 : ℕ)^8269*100000000000000^6221 ≤ 26528082423507^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685002587 10000000000 26528082423507 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864949683/2000000000 : ℝ), (635073803/1250000000 : ℝ), (3685002587/10000000000 : ℝ)] ![(32818325699111/100000000000000 : ℝ), (20326795928333/50000000000000 : ℝ), (26528082423507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864949683/2000000000 : ℝ)|^8269 ≤ (32818325699111/100000000000000 : ℝ)^6221
        have hw : |(864949683/2000000000 : ℝ)|=(864949683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635073803/1250000000 : ℝ)|^8269 ≤ (20326795928333/50000000000000 : ℝ)^6221
        have hw : |(635073803/1250000000 : ℝ)|=(635073803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685002587/10000000000 : ℝ)|^8269 ≤ (26528082423507/100000000000000 : ℝ)^6221
        have hw : |(3685002587/10000000000 : ℝ)|=(3685002587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (659/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (139/100000 : ℝ) ^ (2067/512 : ℝ) ≤ (73110251/25000000000000000000 : ℝ) := by
    have hpowers : (139/100000 : ℝ)^2067 ≤ (73110251/25000000000000000000 : ℝ)^512 := by
      have hnat : (139 : ℕ)^2067*25000000000000000000^512 ≤ 73110251^512*100000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139 100000 73110251 25000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (139/100000 : ℝ)) (X := (73110251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/10000 : ℝ) ^ (2067/512 : ℝ) ≤ (592235274782223707/100000000000000000000 : ℝ) := by
    have hpowers : (2807/10000 : ℝ)^2067 ≤ (592235274782223707/100000000000000000000 : ℝ)^512 := by
      have hnat : (2807 : ℕ)^2067*100000000000000000000^512 ≤ 592235274782223707^512*10000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 10000 592235274782223707 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/10000 : ℝ)) (X := (592235274782223707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000073110251/12500000000000000000 : ℝ) ≤ (1250000000001811/1250000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (12500000000073110251/12500000000000000000 : ℝ)^512 ≤ (1250000000001811/1250000000000000 : ℝ)^2067 := by
      have hnat : (12500000000073110251 : ℕ)^512*1250000000000000^2067 ≤ 1250000000001811^2067*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000073110251 12500000000000000000 1250000000001811 1250000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000001811/1250000000000000 : ℝ)) (X := (12500000000073110251/12500000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100592235275074664711/100000000000000000000 : ℝ) ≤ (10014637218133301/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (100592235275074664711/100000000000000000000 : ℝ)^512 ≤ (10014637218133301/10000000000000000 : ℝ)^2067 := by
      have hnat : (100592235275074664711 : ℕ)^512*10000000000000000^2067 ≤ 10014637218133301^2067*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100592235275074664711 100000000000000000000 10014637218133301 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014637218133301/10000000000000000 : ℝ)) (X := (100592235275074664711/100000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50592235274782223707/50000000000000000000 : ℝ) ≤ (5014637218126057/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50592235274782223707/50000000000000000000 : ℝ)^512 ≤ (5014637218126057/5000000000000000 : ℝ)^2067 := by
      have hnat : (50592235274782223707 : ℕ)^512*5000000000000000^2067 ≤ 5014637218126057^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50592235274782223707 50000000000000000000 5014637218126057 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014637218126057/5000000000000000 : ℝ)) (X := (50592235274782223707/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(73110251/25000000000000000000 : ℝ) ≤ ((139652965426883817157/139655000000000000000 : ℝ)+2*(14637218118813/2793100000000000 : ℝ)*(139/100000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (139652965426883817157/139655000000000000000 : ℝ)+2*(14637218118813/2793100000000000 : ℝ)*(139/100000 : ℝ)=(1250000000001811/1250000000000000 : ℝ) by norm_num, show 1+2*(73110251/25000000000000000000 : ℝ)=(12500000000073110251/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(592235274782223707/100000000000000000000 : ℝ)+(73110251/25000000000000000000 : ℝ) ≤ ((139652965426883817157/139655000000000000000 : ℝ)+(14637218118813/2793100000000000 : ℝ)*((2807/10000 : ℝ)+(139/100000 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (139652965426883817157/139655000000000000000 : ℝ)+(14637218118813/2793100000000000 : ℝ)*((2807/10000 : ℝ)+(139/100000 : ℝ))=(10014637218133301/10000000000000000 : ℝ) by norm_num, show 1+(592235274782223707/100000000000000000000 : ℝ)+(73110251/25000000000000000000 : ℝ)=(100592235275074664711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(592235274782223707/100000000000000000000 : ℝ) ≤ ((139652965426883817157/139655000000000000000 : ℝ)+2*(14637218118813/2793100000000000 : ℝ)*(2807/10000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (139652965426883817157/139655000000000000000 : ℝ)+2*(14637218118813/2793100000000000 : ℝ)*(2807/10000 : ℝ)=(5014637218126057/5000000000000000 : ℝ) by norm_num, show 1+2*(592235274782223707/100000000000000000000 : ℝ)=(50592235274782223707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139652965426883817157/139655000000000000000 : ℝ)*(X 1 0+X 2 0)+(14637218118813/2793100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (139/100000 : ℝ)) (hi := (2807/10000 : ℝ)) (c := (139652965426883817157/139655000000000000000 : ℝ)) (alpha := (14637218118813/2793100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139652965426883817157/139655000000000000000 : ℝ)*(X 0 1+X 2 1)+(14637218118813/2793100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (139/100000 : ℝ)) (hi := (2807/10000 : ℝ)) (c := (139652965426883817157/139655000000000000000 : ℝ)) (alpha := (14637218118813/2793100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139652965426883817157/139655000000000000000 : ℝ)*(X 0 2+X 1 2)+(14637218118813/2793100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (139/100000 : ℝ)) (hi := (2807/10000 : ℝ)) (c := (139652965426883817157/139655000000000000000 : ℝ)) (alpha := (14637218118813/2793100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122294061/10000000000 : ℝ)*X 0 0+(285975899/500000000 : ℝ)*X 0 1+(4988156523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42365301/78125000 : ℝ)*X 1 0+(-1259167023/5000000000 : ℝ)*X 1 1+(4988156817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711379609/5000000000 : ℝ)*X 2 0+(2494078033/5000000000 : ℝ)*X 2 1+(-1259167049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161487731/5000000000 : ℝ)*X 0 0+(1832243679/5000000000 : ℝ)*X 0 1+(637587327/1250000000 : ℝ)*X 0 2+(2161487731/5000000000 : ℝ)*X 1 0+(1832243679/5000000000 : ℝ)*X 1 1+(637587327/1250000000 : ℝ)*X 1 2+(2161487731/5000000000 : ℝ)*X 2 0+(1832243679/5000000000 : ℝ)*X 2 1+(637587327/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2123197299/10000000000 : ℝ)*X 0 0+(624799553/1250000000 : ℝ)*X 0 1+(5709070853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1308970523/2500000000 : ℝ)*X 1 0+(-449354931/2500000000 : ℝ)*X 1 1+(356816933/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617940967/5000000000 : ℝ)*X 2 0+(5709070873/10000000000 : ℝ)*X 2 1+(-1797420027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864949683/2000000000 : ℝ)*X 0 0+(635073803/1250000000 : ℝ)*X 0 1+(3685002587/10000000000 : ℝ)*X 0 2+(864949683/2000000000 : ℝ)*X 1 0+(635073803/1250000000 : ℝ)*X 1 1+(3685002587/10000000000 : ℝ)*X 1 2+(864949683/2000000000 : ℝ)*X 2 0+(635073803/1250000000 : ℝ)*X 2 1+(3685002587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (412618026025633635216435423/82150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118844199/100000000000000 : ℝ)*(base1) + (1048974953/100000000000000 : ℝ)*(base19) + (1222955099/100000000000000 : ℝ)*(base23) + (97253019/100000000000000 : ℝ)*(upper3) + (25349161/20000000000000 : ℝ)*(upper5) + (206360471110107/20000000000000 : ℝ)*(major0) + (206360471110107/20000000000000 : ℝ)*(major1) + (206360471110107/20000000000000 : ℝ)*(major2) + (273463573011657/20000000000000 : ℝ)*(sp0) + (437543160341/32000000000 : ℝ)*(sp1) + (1367322202085479/100000000000000 : ℝ)*(sp2) + (27851145595933/4000000000000 : ℝ)*(sp3) + (1419706623/25000000000000 : ℝ)*(sp4) + (1179946661/50000000000000 : ℝ)*(sp7) + (139256223727169/20000000000000 : ℝ)*(f.failure) + (683661712520289/50000000000000 : ℝ)*(f.sum) + (1511535009359/821500000000000000000000000 : ℝ)*base66 + (1316862641883784953/164300000000000000000000000000000 : ℝ)*base68 + (186851629007484953/164300000000000000000000000000000 : ℝ)*base70 + (940703212797984953/164300000000000000000000000000000 : ℝ)*base72 + (4263140437481/1643000000000000000000000000 : ℝ)*base74 + (542353272091684953/164300000000000000000000000000000 : ℝ)*base76 + (778834100632584953/164300000000000000000000000000000 : ℝ)*base78 + (493659952679584953/164300000000000000000000000000000 : ℝ)*base80 + (2257886893927/1643000000000000000000000000 : ℝ)*base81 + (10096741/2000000000000000000000 : ℝ)*base90 + (10096741/2000000000000000000000 : ℝ)*base92 + (10096741/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246127732143572017658518131/51343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6267499/20000000000000 : ℝ)*(base1) + (1009518861/100000000000000 : ℝ)*(base19) + (468993157/50000000000000 : ℝ)*(base23) + (1941317/2000000000000 : ℝ)*(upper3) + (129755947/100000000000000 : ℝ)*(upper5) + (265457268062837/25000000000000 : ℝ)*(major0) + (265457268062837/25000000000000 : ℝ)*(major1) + (265457268062837/25000000000000 : ℝ)*(major2) + (2280258401/50000000000000 : ℝ)*(sp1) + (936498317/25000000000000 : ℝ)*(sp2) + (140711426108507/10000000000000 : ℝ)*(sp4) + (1407108659711911/100000000000000 : ℝ)*(sp5) + (1407109545767991/100000000000000 : ℝ)*(sp6) + (179135930906711/25000000000000 : ℝ)*(sp7) + (716543754964339/100000000000000 : ℝ)*(f.failure) + (703557114873787/50000000000000 : ℝ)*(f.sum) + (7371796185111/4107500000000000000000000000 : ℝ)*base65 + (1033004266375485623/205375000000000000000000000000000 : ℝ)*base68 + (1803279346761235623/205375000000000000000000000000000 : ℝ)*base70 + (413532884482485623/205375000000000000000000000000000 : ℝ)*base72 + (2778777183707/2053750000000000000000000000 : ℝ)*base74 + (898458284545735623/205375000000000000000000000000000 : ℝ)*base76 + (8643003388735623/205375000000000000000000000000000 : ℝ)*base78 + (85180427612889377/205375000000000000000000000000000 : ℝ)*base79 + (27593322627333/8215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (13395871/10000000000000000000000 : ℝ)*base90 + (13395871/10000000000000000000000 : ℝ)*base92 + (13395871/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1076_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (659/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1076_s2_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-5447881/25000000 : ℝ)*x 0 + (5523837449/10000000000 : ℝ)*x 1 + (2573876217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447881/25000000 : ℝ)^8269 ≤ (6598069858533/50000000000000 : ℝ)^6221 := by
    have hnat : (5447881 : ℕ)^8269*50000000000000^6221 ≤ 6598069858533^6221*25000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447881 25000000 6598069858533 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523837449/10000000000 : ℝ)^8269 ≤ (5679298100323/12500000000000 : ℝ)^6221 := by
    have hnat : (5523837449 : ℕ)^8269*12500000000000^6221 ≤ 5679298100323^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523837449 10000000000 5679298100323 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573876217/5000000000 : ℝ)^8269 ≤ (20684737732413/50000000000000 : ℝ)^6221 := by
    have hnat : (2573876217 : ℕ)^8269*50000000000000^6221 ≤ 20684737732413^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573876217 5000000000 20684737732413 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5447881/25000000 : ℝ), (5523837449/10000000000 : ℝ), (2573876217/5000000000 : ℝ)] ![(6598069858533/50000000000000 : ℝ), (5679298100323/12500000000000 : ℝ), (20684737732413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5447881/25000000 : ℝ)|^8269 ≤ (6598069858533/50000000000000 : ℝ)^6221
        have hw : |(-5447881/25000000 : ℝ)|=(5447881/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523837449/10000000000 : ℝ)|^8269 ≤ (5679298100323/12500000000000 : ℝ)^6221
        have hw : |(5523837449/10000000000 : ℝ)|=(5523837449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573876217/5000000000 : ℝ)|^8269 ≤ (20684737732413/50000000000000 : ℝ)^6221
        have hw : |(2573876217/5000000000 : ℝ)|=(2573876217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376753497/10000000000 : ℝ)*x 0 + (-475040583/2000000000 : ℝ)*x 1 + (5147752881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376753497/10000000000 : ℝ)^8269 ≤ (2739588546497/6250000000000 : ℝ)^6221 := by
    have hnat : (5376753497 : ℕ)^8269*6250000000000^6221 ≤ 2739588546497^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376753497 10000000000 2739588546497 6250000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475040583/2000000000 : ℝ)^8269 ≤ (14797103013689/100000000000000 : ℝ)^6221 := by
    have hnat : (475040583 : ℕ)^8269*100000000000000^6221 ≤ 14797103013689^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475040583 2000000000 14797103013689 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147752881/10000000000 : ℝ)^8269 ≤ (41369480239709/100000000000000 : ℝ)^6221 := by
    have hnat : (5147752881 : ℕ)^8269*100000000000000^6221 ≤ 41369480239709^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147752881 10000000000 41369480239709 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376753497/10000000000 : ℝ), (-475040583/2000000000 : ℝ), (5147752881/10000000000 : ℝ)] ![(2739588546497/6250000000000 : ℝ), (14797103013689/100000000000000 : ℝ), (41369480239709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376753497/10000000000 : ℝ)|^8269 ≤ (2739588546497/6250000000000 : ℝ)^6221
        have hw : |(5376753497/10000000000 : ℝ)|=(5376753497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475040583/2000000000 : ℝ)|^8269 ≤ (14797103013689/100000000000000 : ℝ)^6221
        have hw : |(-475040583/2000000000 : ℝ)|=(475040583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147752881/10000000000 : ℝ)|^8269 ≤ (41369480239709/100000000000000 : ℝ)^6221
        have hw : |(5147752881/10000000000 : ℝ)|=(5147752881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376753671/10000000000 : ℝ)*x 0 + (2573876349/5000000000 : ℝ)*x 1 + (-1187601461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376753671/10000000000 : ℝ)^8269 ≤ (8766683725891/20000000000000 : ℝ)^6221 := by
    have hnat : (5376753671 : ℕ)^8269*20000000000000^6221 ≤ 8766683725891^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376753671 10000000000 8766683725891 20000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573876349/5000000000 : ℝ)^8269 ≤ (41369478284891/100000000000000 : ℝ)^6221 := by
    have hnat : (2573876349 : ℕ)^8269*100000000000000^6221 ≤ 41369478284891^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573876349 5000000000 41369478284891 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187601461/5000000000 : ℝ)^8269 ≤ (2959420614331/20000000000000 : ℝ)^6221 := by
    have hnat : (1187601461 : ℕ)^8269*20000000000000^6221 ≤ 2959420614331^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187601461 5000000000 2959420614331 20000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376753671/10000000000 : ℝ), (2573876349/5000000000 : ℝ), (-1187601461/5000000000 : ℝ)] ![(8766683725891/20000000000000 : ℝ), (41369478284891/100000000000000 : ℝ), (2959420614331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376753671/10000000000 : ℝ)|^8269 ≤ (8766683725891/20000000000000 : ℝ)^6221
        have hw : |(5376753671/10000000000 : ℝ)|=(5376753671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573876349/5000000000 : ℝ)|^8269 ≤ (41369478284891/100000000000000 : ℝ)^6221
        have hw : |(2573876349/5000000000 : ℝ)|=(2573876349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187601461/5000000000 : ℝ)|^8269 ≤ (2959420614331/20000000000000 : ℝ)^6221
        have hw : |(-1187601461/5000000000 : ℝ)|=(1187601461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218090003/500000000 : ℝ)*x 0 + (1002064557/2500000000 : ℝ)*x 1 + (237339761/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218090003/500000000 : ℝ)^8269 ≤ (33192579921453/100000000000000 : ℝ)^6221 := by
    have hnat : (218090003 : ℕ)^8269*100000000000000^6221 ≤ 33192579921453^6221*500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218090003 500000000 33192579921453 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002064557/2500000000 : ℝ)^8269 ≤ (29665093388111/100000000000000 : ℝ)^6221 := by
    have hnat : (1002064557 : ℕ)^8269*100000000000000^6221 ≤ 29665093388111^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002064557 2500000000 29665093388111 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237339761/500000000 : ℝ)^8269 ≤ (37142326671613/100000000000000 : ℝ)^6221 := by
    have hnat : (237339761 : ℕ)^8269*100000000000000^6221 ≤ 37142326671613^6221*500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237339761 500000000 37142326671613 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218090003/500000000 : ℝ), (1002064557/2500000000 : ℝ), (237339761/500000000 : ℝ)] ![(33192579921453/100000000000000 : ℝ), (29665093388111/100000000000000 : ℝ), (37142326671613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218090003/500000000 : ℝ)|^8269 ≤ (33192579921453/100000000000000 : ℝ)^6221
        have hw : |(218090003/500000000 : ℝ)|=(218090003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002064557/2500000000 : ℝ)|^8269 ≤ (29665093388111/100000000000000 : ℝ)^6221
        have hw : |(1002064557/2500000000 : ℝ)|=(1002064557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237339761/500000000 : ℝ)|^8269 ≤ (37142326671613/100000000000000 : ℝ)^6221
        have hw : |(237339761/500000000 : ℝ)|=(237339761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179275001/10000000000 : ℝ)*x 0 + (5150468751/10000000000 : ℝ)*x 1 + (2760546371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179275001/10000000000 : ℝ)^8269 ≤ (52788506259/400000000000 : ℝ)^6221 := by
    have hnat : (2179275001 : ℕ)^8269*400000000000^6221 ≤ 52788506259^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179275001 10000000000 52788506259 400000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150468751/10000000000 : ℝ)^8269 ≤ (41398493855229/100000000000000 : ℝ)^6221 := by
    have hnat : (5150468751 : ℕ)^8269*100000000000000^6221 ≤ 41398493855229^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150468751 10000000000 41398493855229 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760546371/5000000000 : ℝ)^8269 ≤ (45404379568689/100000000000000 : ℝ)^6221 := by
    have hnat : (2760546371 : ℕ)^8269*100000000000000^6221 ≤ 45404379568689^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760546371 5000000000 45404379568689 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179275001/10000000000 : ℝ), (5150468751/10000000000 : ℝ), (2760546371/5000000000 : ℝ)] ![(52788506259/400000000000 : ℝ), (41398493855229/100000000000000 : ℝ), (45404379568689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179275001/10000000000 : ℝ)|^8269 ≤ (52788506259/400000000000 : ℝ)^6221
        have hw : |(-2179275001/10000000000 : ℝ)|=(2179275001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150468751/10000000000 : ℝ)|^8269 ≤ (41398493855229/100000000000000 : ℝ)^6221
        have hw : |(5150468751/10000000000 : ℝ)|=(5150468751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760546371/5000000000 : ℝ)|^8269 ≤ (45404379568689/100000000000000 : ℝ)^6221
        have hw : |(2760546371/5000000000 : ℝ)|=(2760546371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82527491/156250000 : ℝ)*x 0 + (-2001862991/10000000000 : ℝ)*x 1 + (2760546417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82527491/156250000 : ℝ)^8269 ≤ (42807045147231/100000000000000 : ℝ)^6221 := by
    have hnat : (82527491 : ℕ)^8269*100000000000000^6221 ≤ 42807045147231^6221*156250000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82527491 156250000 42807045147231 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001862991/10000000000 : ℝ)^8269 ≤ (11788574263729/100000000000000 : ℝ)^6221 := by
    have hnat : (2001862991 : ℕ)^8269*100000000000000^6221 ≤ 11788574263729^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001862991 10000000000 11788574263729 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760546417/5000000000 : ℝ)^8269 ≤ (22702190287177/50000000000000 : ℝ)^6221 := by
    have hnat : (2760546417 : ℕ)^8269*50000000000000^6221 ≤ 22702190287177^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760546417 5000000000 22702190287177 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82527491/156250000 : ℝ), (-2001862991/10000000000 : ℝ), (2760546417/5000000000 : ℝ)] ![(42807045147231/100000000000000 : ℝ), (11788574263729/100000000000000 : ℝ), (22702190287177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82527491/156250000 : ℝ)|^8269 ≤ (42807045147231/100000000000000 : ℝ)^6221
        have hw : |(82527491/156250000 : ℝ)|=(82527491/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001862991/10000000000 : ℝ)|^8269 ≤ (11788574263729/100000000000000 : ℝ)^6221
        have hw : |(-2001862991/10000000000 : ℝ)|=(2001862991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760546417/5000000000 : ℝ)|^8269 ≤ (22702190287177/50000000000000 : ℝ)^6221
        have hw : |(2760546417/5000000000 : ℝ)|=(2760546417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056351933/2000000000 : ℝ)*x 0 + (220843707/400000000 : ℝ)*x 1 + (-2001862881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056351933/2000000000 : ℝ)^8269 ≤ (42807047743481/100000000000000 : ℝ)^6221 := by
    have hnat : (1056351933 : ℕ)^8269*100000000000000^6221 ≤ 42807047743481^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056351933 2000000000 42807047743481 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220843707/400000000 : ℝ)^8269 ≤ (22702189418151/50000000000000 : ℝ)^6221 := by
    have hnat : (220843707 : ℕ)^8269*50000000000000^6221 ≤ 22702189418151^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220843707 400000000 22702189418151 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001862881/10000000000 : ℝ)^8269 ≤ (1178857340271/10000000000000 : ℝ)^6221 := by
    have hnat : (2001862881 : ℕ)^8269*10000000000000^6221 ≤ 1178857340271^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001862881 10000000000 1178857340271 10000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056351933/2000000000 : ℝ), (220843707/400000000 : ℝ), (-2001862881/10000000000 : ℝ)] ![(42807047743481/100000000000000 : ℝ), (22702189418151/50000000000000 : ℝ), (1178857340271/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056351933/2000000000 : ℝ)|^8269 ≤ (42807047743481/100000000000000 : ℝ)^6221
        have hw : |(1056351933/2000000000 : ℝ)|=(1056351933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220843707/400000000 : ℝ)|^8269 ≤ (22702189418151/50000000000000 : ℝ)^6221
        have hw : |(220843707/400000000 : ℝ)|=(220843707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2001862881/10000000000 : ℝ)|^8269 ≤ (1178857340271/10000000000000 : ℝ)^6221
        have hw : |(-2001862881/10000000000 : ℝ)|=(2001862881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s2_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362040941/10000000000 : ℝ)*x 0 + (2370730741/5000000000 : ℝ)*x 1 + (2006823709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362040941/10000000000 : ℝ)^8269 ≤ (33195016467029/100000000000000 : ℝ)^6221 := by
    have hnat : (4362040941 : ℕ)^8269*100000000000000^6221 ≤ 33195016467029^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362040941 10000000000 33195016467029 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370730741/5000000000 : ℝ)^8269 ≤ (37086862475231/100000000000000 : ℝ)^6221 := by
    have hnat : (2370730741 : ℕ)^8269*100000000000000^6221 ≤ 37086862475231^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370730741 5000000000 37086862475231 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006823709/5000000000 : ℝ)^8269 ≤ (1857382564939/6250000000000 : ℝ)^6221 := by
    have hnat : (2006823709 : ℕ)^8269*6250000000000^6221 ≤ 1857382564939^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006823709 5000000000 1857382564939 6250000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362040941/10000000000 : ℝ), (2370730741/5000000000 : ℝ), (2006823709/5000000000 : ℝ)] ![(33195016467029/100000000000000 : ℝ), (37086862475231/100000000000000 : ℝ), (1857382564939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362040941/10000000000 : ℝ)|^8269 ≤ (33195016467029/100000000000000 : ℝ)^6221
        have hw : |(4362040941/10000000000 : ℝ)|=(4362040941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2370730741/5000000000 : ℝ)|^8269 ≤ (37086862475231/100000000000000 : ℝ)^6221
        have hw : |(2370730741/5000000000 : ℝ)|=(2370730741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006823709/5000000000 : ℝ)|^8269 ≤ (1857382564939/6250000000000 : ℝ)^6221
        have hw : |(2006823709/5000000000 : ℝ)|=(2006823709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (659/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (8761/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4177/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (659/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (659/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (659/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (659/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (659/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (659/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (659/12500 : ℝ) ^ (2067/512 : ℝ) ≤ (692587919796811/100000000000000000000 : ℝ) := by
    have hpowers : (659/12500 : ℝ)^2067 ≤ (692587919796811/100000000000000000000 : ℝ)^512 := by
      have hnat : (659 : ℕ)^2067*100000000000000000000^512 ≤ 692587919796811^512*12500^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        659 12500 692587919796811 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (659/12500 : ℝ)) (X := (692587919796811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20743/100000 : ℝ) ^ (2067/512 : ℝ) ≤ (174636814210715471/100000000000000000000 : ℝ) := by
    have hpowers : (20743/100000 : ℝ)^2067 ≤ (174636814210715471/100000000000000000000 : ℝ)^512 := by
      have hnat : (20743 : ℕ)^2067*100000000000000000000^512 ≤ 174636814210715471^512*100000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20743 100000 174636814210715471 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20743/100000 : ℝ)) (X := (174636814210715471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000692587919796811/50000000000000000000 : ℝ) ≤ (10000034310901533/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50000692587919796811/50000000000000000000 : ℝ)^512 ≤ (10000034310901533/10000000000000000 : ℝ)^2067 := by
      have hnat : (50000692587919796811 : ℕ)^512*10000000000000000^2067 ≤ 10000034310901533^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000692587919796811 50000000000000000000 10000034310901533 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034310901533/10000000000000000 : ℝ)) (X := (50000692587919796811/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50087664701065256141/50000000000000000000 : ℝ) ≤ (78158906897087/78125000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50087664701065256141/50000000000000000000 : ℝ)^512 ≤ (78158906897087/78125000000000 : ℝ)^2067 := by
      have hnat : (50087664701065256141 : ℕ)^512*78125000000000^2067 ≤ 78158906897087^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50087664701065256141 50000000000000000000 78158906897087 78125000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78158906897087/78125000000000 : ℝ)) (X := (50087664701065256141/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50174636814210715471/50000000000000000000 : ℝ) ≤ (10008645854752739/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50174636814210715471/50000000000000000000 : ℝ)^512 ≤ (10008645854752739/10000000000000000 : ℝ)^2067 := by
      have hnat : (50174636814210715471 : ℕ)^512*10000000000000000^2067 ≤ 10008645854752739^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50174636814210715471 50000000000000000000 10008645854752739 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008645854752739/10000000000000000 : ℝ)) (X := (50174636814210715471/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(692587919796811/100000000000000000000 : ℝ) ≤ ((154665130764774059011/154710000000000000000 : ℝ)+2*(4305771925603/1547100000000000 : ℝ)*(659/12500 : ℝ))^(2067/512 : ℝ) := by
    rw [show (154665130764774059011/154710000000000000000 : ℝ)+2*(4305771925603/1547100000000000 : ℝ)*(659/12500 : ℝ)=(10000034310901533/10000000000000000 : ℝ) by norm_num, show 1+2*(692587919796811/100000000000000000000 : ℝ)=(50000692587919796811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(174636814210715471/100000000000000000000 : ℝ)+(692587919796811/100000000000000000000 : ℝ) ≤ ((154665130764774059011/154710000000000000000 : ℝ)+(4305771925603/1547100000000000 : ℝ)*((20743/100000 : ℝ)+(659/12500 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (154665130764774059011/154710000000000000000 : ℝ)+(4305771925603/1547100000000000 : ℝ)*((20743/100000 : ℝ)+(659/12500 : ℝ))=(78158906897087/78125000000000 : ℝ) by norm_num, show 1+(174636814210715471/100000000000000000000 : ℝ)+(692587919796811/100000000000000000000 : ℝ)=(50087664701065256141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(174636814210715471/100000000000000000000 : ℝ) ≤ ((154665130764774059011/154710000000000000000 : ℝ)+2*(4305771925603/1547100000000000 : ℝ)*(20743/100000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (154665130764774059011/154710000000000000000 : ℝ)+2*(4305771925603/1547100000000000 : ℝ)*(20743/100000 : ℝ)=(10008645854752739/10000000000000000 : ℝ) by norm_num, show 1+2*(174636814210715471/100000000000000000000 : ℝ)=(50174636814210715471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (154665130764774059011/154710000000000000000 : ℝ)*(X 1 0+X 2 0)+(4305771925603/1547100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (659/12500 : ℝ)) (hi := (20743/100000 : ℝ)) (c := (154665130764774059011/154710000000000000000 : ℝ)) (alpha := (4305771925603/1547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (154665130764774059011/154710000000000000000 : ℝ)*(X 0 1+X 2 1)+(4305771925603/1547100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (659/12500 : ℝ)) (hi := (20743/100000 : ℝ)) (c := (154665130764774059011/154710000000000000000 : ℝ)) (alpha := (4305771925603/1547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (154665130764774059011/154710000000000000000 : ℝ)*(X 0 2+X 1 2)+(4305771925603/1547100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (659/12500 : ℝ)) (hi := (20743/100000 : ℝ)) (c := (154665130764774059011/154710000000000000000 : ℝ)) (alpha := (4305771925603/1547100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5447881/25000000 : ℝ)*X 0 0+(5523837449/10000000000 : ℝ)*X 0 1+(2573876217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376753497/10000000000 : ℝ)*X 1 0+(-475040583/2000000000 : ℝ)*X 1 1+(5147752881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376753671/10000000000 : ℝ)*X 2 0+(2573876349/5000000000 : ℝ)*X 2 1+(-1187601461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218090003/500000000 : ℝ)*X 0 0+(1002064557/2500000000 : ℝ)*X 0 1+(237339761/500000000 : ℝ)*X 0 2+(218090003/500000000 : ℝ)*X 1 0+(1002064557/2500000000 : ℝ)*X 1 1+(237339761/500000000 : ℝ)*X 1 2+(218090003/500000000 : ℝ)*X 2 0+(1002064557/2500000000 : ℝ)*X 2 1+(237339761/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179275001/10000000000 : ℝ)*X 0 0+(5150468751/10000000000 : ℝ)*X 0 1+(2760546371/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82527491/156250000 : ℝ)*X 1 0+(-2001862991/10000000000 : ℝ)*X 1 1+(2760546417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056351933/2000000000 : ℝ)*X 2 0+(220843707/400000000 : ℝ)*X 2 1+(-2001862881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362040941/10000000000 : ℝ)*X 0 0+(2370730741/5000000000 : ℝ)*X 0 1+(2006823709/5000000000 : ℝ)*X 0 2+(4362040941/10000000000 : ℝ)*X 1 0+(2370730741/5000000000 : ℝ)*X 1 1+(2006823709/5000000000 : ℝ)*X 1 2+(4362040941/10000000000 : ℝ)*X 2 0+(2370730741/5000000000 : ℝ)*X 2 1+(2006823709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5481874868747053869691/1432500000000000000000000000 : ℝ) := by norm_num
    linear_combination (40201579/6250000000000 : ℝ)*(base19) + (5809119/800000000000 : ℝ)*(base23) + (12954137/20000000000000 : ℝ)*(upper3) + (1685309/100000000000000 : ℝ)*(upper4) + (3853929/5000000000000 : ℝ)*(upper5) + (62703576294057/3125000000000 : ℝ)*(major0) + (62703576294057/3125000000000 : ℝ)*(major1) + (62703576294057/3125000000000 : ℝ)*(major2) + (2658982379170563/100000000000000 : ℝ)*(sp0) + (1329495772279129/50000000000000 : ℝ)*(sp1) + (20773370794091/781250000000 : ℝ)*(sp2) + (677016187088469/50000000000000 : ℝ)*(sp3) + (9808612959/100000000000000 : ℝ)*(sp4) + (4193299559/100000000000000 : ℝ)*(sp7) + (1354036567476497/100000000000000 : ℝ)*(f.failure) + (1329496093891761/50000000000000 : ℝ)*(f.sum) + (2358537866227/2148750000000000000000000000 : ℝ)*base65 + (61871195229721097/53718750000000000000000000000000 : ℝ)*base68 + (380267495737903903/53718750000000000000000000000000 : ℝ)*base69 + (240130286919872653/53718750000000000000000000000000 : ℝ)*base71 + (3884677398229/1074375000000000000000000000 : ℝ)*base74 + (97044944661533597/53718750000000000000000000000000 : ℝ)*base76 + (31477277375689847/53718750000000000000000000000000 : ℝ)*base78 + (310635873349903903/53718750000000000000000000000000 : ℝ)*base79 + (11115780659219/4297500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10921333/10000000000000000000000 : ℝ)*base90 + (10921333/10000000000000000000000 : ℝ)*base92 + (10921333/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455355780815866462906139341/71625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12370657/1000000000000 : ℝ)*(base19) + (91502029/6250000000000 : ℝ)*(base23) + (176160839/100000000000000 : ℝ)*(upper3) + (33187153/100000000000000 : ℝ)*(lower4) + (127989973/100000000000000 : ℝ)*(upper5) + (509016226955093/25000000000000 : ℝ)*(major0) + (509016226955093/25000000000000 : ℝ)*(major1) + (509016226955093/25000000000000 : ℝ)*(major2) + (10787283737/100000000000000 : ℝ)*(sp1) + (816752917/6250000000000 : ℝ)*(sp2) + (1349075891628417/50000000000000 : ℝ)*(sp4) + (674534939726849/25000000000000 : ℝ)*(sp5) + (84316789099303/3125000000000 : ℝ)*(sp6) + (343494455116827/25000000000000 : ℝ)*(sp7) + (343494455116827/25000000000000 : ℝ)*(f.failure) + (1349075891628417/50000000000000 : ℝ)*(f.sum) + (191946316250777/38677500000000000000000000000 : ℝ)*base66 + (49135567649085606977/3867750000000000000000000000000000 : ℝ)*base68 + (31289323514666106977/3867750000000000000000000000000000 : ℝ)*base70 + (32703858120035856977/3867750000000000000000000000000000 : ℝ)*base72 + (373813714681759/77355000000000000000000000000 : ℝ)*base74 + (6969289521476856977/3867750000000000000000000000000000 : ℝ)*base76 + (2316828258608106977/3867750000000000000000000000000000 : ℝ)*base78 + (257664196301106977/3867750000000000000000000000000000 : ℝ)*base80 + (65686412798251/19338750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (19030297/2500000000000000000000 : ℝ)*base89 + (19030297/2500000000000000000000 : ℝ)*base91 + (19030297/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1076_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (659/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4177/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1076_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4177/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1076_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1076_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1076_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4177/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1076_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

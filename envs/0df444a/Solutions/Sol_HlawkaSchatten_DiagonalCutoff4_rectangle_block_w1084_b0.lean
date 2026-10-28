-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:16.401214+00:00
-- url     : https://prove2.me/submissions/fbd7d74b-6d9e-4483-acd6-1ca76f1bface

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
theorem support_rectangle_w1084_s0_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-191030373/1000000000 : ℝ)*x 0 + (6067833297/10000000000 : ℝ)*x 1 + (954618643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191030373/1000000000 : ℝ)^8277 ≤ (11085106954221/100000000000000 : ℝ)^6229 := by
    have hnat : (191030373 : ℕ)^8277*100000000000000^6229 ≤ 11085106954221^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191030373 1000000000 11085106954221 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6067833297/10000000000 : ℝ)^8277 ≤ (20112147831/39062500000 : ℝ)^6229 := by
    have hnat : (6067833297 : ℕ)^8277*39062500000^6229 ≤ 20112147831^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6067833297 10000000000 20112147831 39062500000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954618643/2000000000 : ℝ)^8277 ≤ (37427794584187/100000000000000 : ℝ)^6229 := by
    have hnat : (954618643 : ℕ)^8277*100000000000000^6229 ≤ 37427794584187^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954618643 2000000000 37427794584187 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191030373/1000000000 : ℝ), (6067833297/10000000000 : ℝ), (954618643/2000000000 : ℝ)] ![(11085106954221/100000000000000 : ℝ), (20112147831/39062500000 : ℝ), (37427794584187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191030373/1000000000 : ℝ)|^8277 ≤ (11085106954221/100000000000000 : ℝ)^6229
        have hw : |(-191030373/1000000000 : ℝ)|=(191030373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6067833297/10000000000 : ℝ)|^8277 ≤ (20112147831/39062500000 : ℝ)^6229
        have hw : |(6067833297/10000000000 : ℝ)|=(6067833297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(954618643/2000000000 : ℝ)|^8277 ≤ (37427794584187/100000000000000 : ℝ)^6229
        have hw : |(954618643/2000000000 : ℝ)|=(954618643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2760029939/5000000000 : ℝ)*x 0 + (-1327515471/5000000000 : ℝ)*x 1 + (2386546433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760029939/5000000000 : ℝ)^8277 ≤ (45404495070697/100000000000000 : ℝ)^6229 := by
    have hnat : (2760029939 : ℕ)^8277*100000000000000^6229 ≤ 45404495070697^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760029939 5000000000 45404495070697 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327515471/5000000000 : ℝ)^8277 ≤ (17167713973887/100000000000000 : ℝ)^6229 := by
    have hnat : (1327515471 : ℕ)^8277*100000000000000^6229 ≤ 17167713973887^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327515471 5000000000 17167713973887 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386546433/5000000000 : ℝ)^8277 ≤ (9356947736941/25000000000000 : ℝ)^6229 := by
    have hnat : (2386546433 : ℕ)^8277*25000000000000^6229 ≤ 9356947736941^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386546433 5000000000 9356947736941 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760029939/5000000000 : ℝ), (-1327515471/5000000000 : ℝ), (2386546433/5000000000 : ℝ)] ![(45404495070697/100000000000000 : ℝ), (17167713973887/100000000000000 : ℝ), (9356947736941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760029939/5000000000 : ℝ)|^8277 ≤ (45404495070697/100000000000000 : ℝ)^6229
        have hw : |(2760029939/5000000000 : ℝ)|=(2760029939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1327515471/5000000000 : ℝ)|^8277 ≤ (17167713973887/100000000000000 : ℝ)^6229
        have hw : |(-1327515471/5000000000 : ℝ)|=(1327515471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386546433/5000000000 : ℝ)|^8277 ≤ (9356947736941/25000000000000 : ℝ)^6229
        have hw : |(2386546433/5000000000 : ℝ)|=(2386546433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1104011967/2000000000 : ℝ)*x 0 + (238654661/500000000 : ℝ)*x 1 + (-2655030567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104011967/2000000000 : ℝ)^8277 ≤ (22702247300359/50000000000000 : ℝ)^6229 := by
    have hnat : (1104011967 : ℕ)^8277*50000000000000^6229 ≤ 22702247300359^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104011967 2000000000 22702247300359 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238654661/500000000 : ℝ)^8277 ≤ (7485558927257/20000000000000 : ℝ)^6229 := by
    have hnat : (238654661 : ℕ)^8277*20000000000000^6229 ≤ 7485558927257^6229*500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238654661 500000000 7485558927257 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2655030567/10000000000 : ℝ)^8277 ≤ (17167710751863/100000000000000 : ℝ)^6229 := by
    have hnat : (2655030567 : ℕ)^8277*100000000000000^6229 ≤ 17167710751863^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655030567 10000000000 17167710751863 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104011967/2000000000 : ℝ), (238654661/500000000 : ℝ), (-2655030567/10000000000 : ℝ)] ![(22702247300359/50000000000000 : ℝ), (7485558927257/20000000000000 : ℝ), (17167710751863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104011967/2000000000 : ℝ)|^8277 ≤ (22702247300359/50000000000000 : ℝ)^6229
        have hw : |(1104011967/2000000000 : ℝ)|=(1104011967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238654661/500000000 : ℝ)|^8277 ≤ (7485558927257/20000000000000 : ℝ)^6229
        have hw : |(238654661/500000000 : ℝ)|=(238654661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2655030567/10000000000 : ℝ)|^8277 ≤ (17167710751863/100000000000000 : ℝ)^6229
        have hw : |(-2655030567/10000000000 : ℝ)|=(2655030567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2102861733/5000000000 : ℝ)*x 0 + (1561960579/5000000000 : ℝ)*x 1 + (708812437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102861733/5000000000 : ℝ)^8277 ≤ (15817407142973/50000000000000 : ℝ)^6229 := by
    have hnat : (2102861733 : ℕ)^8277*50000000000000^6229 ≤ 15817407142973^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102861733 5000000000 15817407142973 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561960579/5000000000 : ℝ)^8277 ≤ (1331818937027/6250000000000 : ℝ)^6229 := by
    have hnat : (1561960579 : ℕ)^8277*6250000000000^6229 ≤ 1331818937027^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561960579 5000000000 1331818937027 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708812437/1250000000 : ℝ)^8277 ≤ (47056082700223/100000000000000 : ℝ)^6229 := by
    have hnat : (708812437 : ℕ)^8277*100000000000000^6229 ≤ 47056082700223^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708812437 1250000000 47056082700223 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102861733/5000000000 : ℝ), (1561960579/5000000000 : ℝ), (708812437/1250000000 : ℝ)] ![(15817407142973/50000000000000 : ℝ), (1331818937027/6250000000000 : ℝ), (47056082700223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102861733/5000000000 : ℝ)|^8277 ≤ (15817407142973/50000000000000 : ℝ)^6229
        have hw : |(2102861733/5000000000 : ℝ)|=(2102861733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561960579/5000000000 : ℝ)|^8277 ≤ (1331818937027/6250000000000 : ℝ)^6229
        have hw : |(1561960579/5000000000 : ℝ)|=(1561960579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708812437/1250000000 : ℝ)|^8277 ≤ (47056082700223/100000000000000 : ℝ)^6229
        have hw : |(708812437/1250000000 : ℝ)|=(708812437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915623191/10000000000 : ℝ)*x 0 + (1201629517/2500000000 : ℝ)*x 1 + (603323719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915623191/10000000000 : ℝ)^8277 ≤ (5563071162183/50000000000000 : ℝ)^6229 := by
    have hnat : (1915623191 : ℕ)^8277*50000000000000^6229 ≤ 5563071162183^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915623191 10000000000 5563071162183 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201629517/2500000000 : ℝ)^8277 ≤ (18888233401017/50000000000000 : ℝ)^6229 := by
    have hnat : (1201629517 : ℕ)^8277*50000000000000^6229 ≤ 18888233401017^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201629517 2500000000 18888233401017 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603323719/1000000000 : ℝ)^8277 ≤ (2043895634443/4000000000000 : ℝ)^6229 := by
    have hnat : (603323719 : ℕ)^8277*4000000000000^6229 ≤ 2043895634443^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603323719 1000000000 2043895634443 4000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915623191/10000000000 : ℝ), (1201629517/2500000000 : ℝ), (603323719/1000000000 : ℝ)] ![(5563071162183/50000000000000 : ℝ), (18888233401017/50000000000000 : ℝ), (2043895634443/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915623191/10000000000 : ℝ)|^8277 ≤ (5563071162183/50000000000000 : ℝ)^6229
        have hw : |(-1915623191/10000000000 : ℝ)|=(1915623191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201629517/2500000000 : ℝ)|^8277 ≤ (18888233401017/50000000000000 : ℝ)^6229
        have hw : |(1201629517/2500000000 : ℝ)|=(1201629517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603323719/1000000000 : ℝ)|^8277 ≤ (2043895634443/4000000000000 : ℝ)^6229
        have hw : |(603323719/1000000000 : ℝ)|=(603323719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (323034353/625000000 : ℝ)*x 0 + (-348722359/2500000000 : ℝ)*x 1 + (3016617833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323034353/625000000 : ℝ)^8277 ≤ (4160338799793/10000000000000 : ℝ)^6229 := by
    have hnat : (323034353 : ℕ)^8277*10000000000000^6229 ≤ 4160338799793^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323034353 625000000 4160338799793 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348722359/2500000000 : ℝ)^8277 ≤ (7299238274733/100000000000000 : ℝ)^6229 := by
    have hnat : (348722359 : ℕ)^8277*100000000000000^6229 ≤ 7299238274733^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348722359 2500000000 7299238274733 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016617833/5000000000 : ℝ)^8277 ≤ (51097373710137/100000000000000 : ℝ)^6229 := by
    have hnat : (3016617833 : ℕ)^8277*100000000000000^6229 ≤ 51097373710137^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016617833 5000000000 51097373710137 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323034353/625000000 : ℝ), (-348722359/2500000000 : ℝ), (3016617833/5000000000 : ℝ)] ![(4160338799793/10000000000000 : ℝ), (7299238274733/100000000000000 : ℝ), (51097373710137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323034353/625000000 : ℝ)|^8277 ≤ (4160338799793/10000000000000 : ℝ)^6229
        have hw : |(323034353/625000000 : ℝ)|=(323034353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348722359/2500000000 : ℝ)|^8277 ≤ (7299238274733/100000000000000 : ℝ)^6229
        have hw : |(-348722359/2500000000 : ℝ)|=(348722359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016617833/5000000000 : ℝ)|^8277 ≤ (51097373710137/100000000000000 : ℝ)^6229
        have hw : |(3016617833/5000000000 : ℝ)|=(3016617833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584274857/5000000000 : ℝ)*x 0 + (3016618503/5000000000 : ℝ)*x 1 + (-697443583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584274857/5000000000 : ℝ)^8277 ≤ (8320677740771/20000000000000 : ℝ)^6229 := by
    have hnat : (2584274857 : ℕ)^8277*20000000000000^6229 ≤ 8320677740771^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584274857 5000000000 8320677740771 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016618503/5000000000 : ℝ)^8277 ≤ (25548694395179/50000000000000 : ℝ)^6229 := by
    have hnat : (3016618503 : ℕ)^8277*50000000000000^6229 ≤ 25548694395179^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016618503 5000000000 25548694395179 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697443583/5000000000 : ℝ)^8277 ≤ (1459844498139/20000000000000 : ℝ)^6229 := by
    have hnat : (697443583 : ℕ)^8277*20000000000000^6229 ≤ 1459844498139^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697443583 5000000000 1459844498139 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584274857/5000000000 : ℝ), (3016618503/5000000000 : ℝ), (-697443583/5000000000 : ℝ)] ![(8320677740771/20000000000000 : ℝ), (25548694395179/50000000000000 : ℝ), (1459844498139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584274857/5000000000 : ℝ)|^8277 ≤ (8320677740771/20000000000000 : ℝ)^6229
        have hw : |(2584274857/5000000000 : ℝ)|=(2584274857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3016618503/5000000000 : ℝ)|^8277 ≤ (25548694395179/50000000000000 : ℝ)^6229
        have hw : |(3016618503/5000000000 : ℝ)|=(3016618503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-697443583/5000000000 : ℝ)|^8277 ≤ (1459844498139/20000000000000 : ℝ)^6229
        have hw : |(-697443583/5000000000 : ℝ)|=(697443583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s0_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2108091521/5000000000 : ℝ)*x 0 + (2802378141/5000000000 : ℝ)*x 1 + (3191967091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108091521/5000000000 : ℝ)^8277 ≤ (31739399599431/100000000000000 : ℝ)^6229 := by
    have hnat : (2108091521 : ℕ)^8277*100000000000000^6229 ≤ 31739399599431^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108091521 5000000000 31739399599431 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802378141/5000000000 : ℝ)^8277 ≤ (46332531421099/100000000000000 : ℝ)^6229 := by
    have hnat : (2802378141 : ℕ)^8277*100000000000000^6229 ≤ 46332531421099^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802378141 5000000000 46332531421099 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191967091/10000000000 : ℝ)^8277 ≤ (4385613792997/20000000000000 : ℝ)^6229 := by
    have hnat : (3191967091 : ℕ)^8277*20000000000000^6229 ≤ 4385613792997^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191967091 10000000000 4385613792997 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108091521/5000000000 : ℝ), (2802378141/5000000000 : ℝ), (3191967091/10000000000 : ℝ)] ![(31739399599431/100000000000000 : ℝ), (46332531421099/100000000000000 : ℝ), (4385613792997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108091521/5000000000 : ℝ)|^8277 ≤ (31739399599431/100000000000000 : ℝ)^6229
        have hw : |(2108091521/5000000000 : ℝ)|=(2108091521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802378141/5000000000 : ℝ)|^8277 ≤ (46332531421099/100000000000000 : ℝ)^6229
        have hw : |(2802378141/5000000000 : ℝ)|=(2802378141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191967091/10000000000 : ℝ)|^8277 ≤ (4385613792997/20000000000000 : ℝ)^6229
        have hw : |(3191967091/10000000000 : ℝ)|=(3191967091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (43/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28039/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2069/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2069 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2069*1^512 ≤ 0^512*1^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2069/512 : ℝ) ≤ (154098433713713383/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2069 ≤ (154098433713713383/6250000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2069*6250000000000000000^512 ≤ 154098433713713383^512*5^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 154098433713713383 6250000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (154098433713713383/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2069 := by
      have hnat : (1 : ℕ)^512*1^2069 ≤ 1^2069*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6404098433713713383/6250000000000000000 : ℝ) ≤ (10060455725340849/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (6404098433713713383/6250000000000000000 : ℝ)^512 ≤ (10060455725340849/10000000000000000 : ℝ)^2069 := by
      have hnat : (6404098433713713383 : ℕ)^512*10000000000000000^2069 ≤ 10060455725340849^2069*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6404098433713713383 6250000000000000000 10060455725340849 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060455725340849/10000000000000000 : ℝ)) (X := (6404098433713713383/6250000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3279098433713713383/3125000000000000000 : ℝ) ≤ (5060455725340849/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (3279098433713713383/3125000000000000000 : ℝ)^512 ≤ (5060455725340849/5000000000000000 : ℝ)^2069 := by
      have hnat : (3279098433713713383 : ℕ)^512*5000000000000000^2069 ≤ 5060455725340849^2069*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3279098433713713383 3125000000000000000 5060455725340849 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060455725340849/5000000000000000 : ℝ)) (X := (3279098433713713383/3125000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60455725340849/4000000000000000 : ℝ)*(0 : ℝ))^(2069/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60455725340849/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(154098433713713383/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60455725340849/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (1 : ℝ)+(60455725340849/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060455725340849/10000000000000000 : ℝ) by norm_num, show 1+(154098433713713383/6250000000000000000 : ℝ)+(0 : ℝ)=(6404098433713713383/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(154098433713713383/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60455725340849/4000000000000000 : ℝ)*(2/5 : ℝ))^(2069/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60455725340849/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060455725340849/5000000000000000 : ℝ) by norm_num, show 1+2*(154098433713713383/6250000000000000000 : ℝ)=(3279098433713713383/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60455725340849/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60455725340849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60455725340849/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60455725340849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60455725340849/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60455725340849/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-191030373/1000000000 : ℝ)*X 0 0+(6067833297/10000000000 : ℝ)*X 0 1+(954618643/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2760029939/5000000000 : ℝ)*X 1 0+(-1327515471/5000000000 : ℝ)*X 1 1+(2386546433/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104011967/2000000000 : ℝ)*X 2 0+(238654661/500000000 : ℝ)*X 2 1+(-2655030567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2102861733/5000000000 : ℝ)*X 0 0+(1561960579/5000000000 : ℝ)*X 0 1+(708812437/1250000000 : ℝ)*X 0 2+(2102861733/5000000000 : ℝ)*X 1 0+(1561960579/5000000000 : ℝ)*X 1 1+(708812437/1250000000 : ℝ)*X 1 2+(2102861733/5000000000 : ℝ)*X 2 0+(1561960579/5000000000 : ℝ)*X 2 1+(708812437/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1915623191/10000000000 : ℝ)*X 0 0+(1201629517/2500000000 : ℝ)*X 0 1+(603323719/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323034353/625000000 : ℝ)*X 1 0+(-348722359/2500000000 : ℝ)*X 1 1+(3016617833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584274857/5000000000 : ℝ)*X 2 0+(3016618503/5000000000 : ℝ)*X 2 1+(-697443583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108091521/5000000000 : ℝ)*X 0 0+(2802378141/5000000000 : ℝ)*X 0 1+(3191967091/10000000000 : ℝ)*X 0 2+(2108091521/5000000000 : ℝ)*X 1 0+(2802378141/5000000000 : ℝ)*X 1 1+(3191967091/10000000000 : ℝ)*X 1 2+(2108091521/5000000000 : ℝ)*X 2 0+(2802378141/5000000000 : ℝ)*X 2 1+(3191967091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (718043990978004700398921/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66538891/50000000000000 : ℝ)*(base1) + (780073219/50000000000000 : ℝ)*(base19) + (1425540859/100000000000000 : ℝ)*(base23) + (64294529/50000000000000 : ℝ)*(base24) + (342691869/100000000000000 : ℝ)*(upper3) + (582525511260243/100000000000000 : ℝ)*(major0) + (582525511260243/100000000000000 : ℝ)*(major1) + (582525511260243/100000000000000 : ℝ)*(major2) + (772360505840231/100000000000000 : ℝ)*(sp0) + (96545230806919/12500000000000 : ℝ)*(sp1) + (772361852471873/100000000000000 : ℝ)*(sp2) + (392684976555109/100000000000000 : ℝ)*(sp3) + (3033839341/100000000000000 : ℝ)*(sp4) + (1133468903/50000000000000 : ℝ)*(sp7) + (392687376570697/100000000000000 : ℝ)*(f.failure) + (77236340660179/10000000000000 : ℝ)*(f.sum) + (555422259433693/200000000000000000000000000000 : ℝ)*base66 + (256397393966307/400000000000000000000000000000 : ℝ)*base67 + (267071971566307/400000000000000000000000000000 : ℝ)*base69 + (1820947563233693/400000000000000000000000000000 : ℝ)*base72 + (199449668433693/200000000000000000000000000000 : ℝ)*base74 + (913845779233693/400000000000000000000000000000 : ℝ)*base76 + (429329122833693/400000000000000000000000000000 : ℝ)*base78 + (826529112033693/400000000000000000000000000000 : ℝ)*base80 + (57483633766307/200000000000000000000000000000 : ℝ)*base81 + (378099/400000000000000000000 : ℝ)*base90 + (378099/400000000000000000000 : ℝ)*base92 + (378099/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (266060720947033563857889/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225099489/25000000000000 : ℝ)*(base19) + (611469033/50000000000000 : ℝ)*(base23) + (277698827/100000000000000 : ℝ)*(base39) + (88258489/50000000000000 : ℝ)*(base45) + (56416149/100000000000000 : ℝ)*(upper3) + (158570663/50000000000000 : ℝ)*(upper5) + (307409444488809/50000000000000 : ℝ)*(major0) + (307409444488809/50000000000000 : ℝ)*(major1) + (61481861127879/10000000000000 : ℝ)*(major2) + (125136509/20000000000000 : ℝ)*(sp2) + (163036119249369/20000000000000 : ℝ)*(sp4) + (815179695848889/100000000000000 : ℝ)*(sp5) + (815179025325061/100000000000000 : ℝ)*(sp6) + (20722836331787/5000000000000 : ℝ)*(sp7) + (20722836331787/5000000000000 : ℝ)*(f.failure) + (815180873945673/100000000000000 : ℝ)*(f.sum) + (50155652801299/50000000000000000000000000000 : ℝ)*base65 + (154692285829271/40000000000000000000000000000 : ℝ)*base67 + (224506513058841/200000000000000000000000000000 : ℝ)*base69 + (113490365349271/40000000000000000000000000000 : ℝ)*base71 + (84368483251299/50000000000000000000000000000 : ℝ)*base73 + (307084608258841/200000000000000000000000000000 : ℝ)*base75 + (1283669349258841/200000000000000000000000000000 : ℝ)*base77 + (982831901858841/200000000000000000000000000000 : ℝ)*base79 + (759824871158841/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (129129/20000000000000000000 : ℝ)*base90 + (129129/20000000000000000000 : ℝ)*base92 + (70871/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s1_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119147503/10000000000 : ℝ)*x 0 + (5717302233/10000000000 : ℝ)*x 1 + (2494945959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119147503/10000000000 : ℝ)^8277 ≤ (6361847989677/50000000000000 : ℝ)^6229 := by
    have hnat : (2119147503 : ℕ)^8277*50000000000000^6229 ≤ 6361847989677^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119147503 10000000000 6361847989677 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5717302233/10000000000 : ℝ)^8277 ≤ (47572865581999/100000000000000 : ℝ)^6229 := by
    have hnat : (5717302233 : ℕ)^8277*100000000000000^6229 ≤ 47572865581999^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717302233 10000000000 47572865581999 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2494945959/5000000000 : ℝ)^8277 ≤ (39703438423447/100000000000000 : ℝ)^6229 := by
    have hnat : (2494945959 : ℕ)^8277*100000000000000^6229 ≤ 39703438423447^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494945959 5000000000 39703438423447 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119147503/10000000000 : ℝ), (5717302233/10000000000 : ℝ), (2494945959/5000000000 : ℝ)] ![(6361847989677/50000000000000 : ℝ), (47572865581999/100000000000000 : ℝ), (39703438423447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119147503/10000000000 : ℝ)|^8277 ≤ (6361847989677/50000000000000 : ℝ)^6229
        have hw : |(-2119147503/10000000000 : ℝ)|=(2119147503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5717302233/10000000000 : ℝ)|^8277 ≤ (47572865581999/100000000000000 : ℝ)^6229
        have hw : |(5717302233/10000000000 : ℝ)|=(5717302233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2494945959/5000000000 : ℝ)|^8277 ≤ (39703438423447/100000000000000 : ℝ)^6229
        have hw : |(2494945959/5000000000 : ℝ)|=(2494945959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711158811/5000000000 : ℝ)*x 0 + (-2512881549/10000000000 : ℝ)*x 1 + (199595687/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711158811/5000000000 : ℝ)^8277 ≤ (44339320048799/100000000000000 : ℝ)^6229 := by
    have hnat : (2711158811 : ℕ)^8277*100000000000000^6229 ≤ 44339320048799^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711158811 5000000000 44339320048799 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512881549/10000000000 : ℝ)^8277 ≤ (7978619399029/50000000000000 : ℝ)^6229 := by
    have hnat : (2512881549 : ℕ)^8277*50000000000000^6229 ≤ 7978619399029^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512881549 10000000000 7978619399029 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199595687/400000000 : ℝ)^8277 ≤ (39703441140667/100000000000000 : ℝ)^6229 := by
    have hnat : (199595687 : ℕ)^8277*100000000000000^6229 ≤ 39703441140667^6229*400000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199595687 400000000 39703441140667 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711158811/5000000000 : ℝ), (-2512881549/10000000000 : ℝ), (199595687/400000000 : ℝ)] ![(44339320048799/100000000000000 : ℝ), (7978619399029/50000000000000 : ℝ), (39703441140667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711158811/5000000000 : ℝ)|^8277 ≤ (44339320048799/100000000000000 : ℝ)^6229
        have hw : |(2711158811/5000000000 : ℝ)|=(2711158811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2512881549/10000000000 : ℝ)|^8277 ≤ (7978619399029/50000000000000 : ℝ)^6229
        have hw : |(-2512881549/10000000000 : ℝ)|=(2512881549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199595687/400000000 : ℝ)|^8277 ≤ (39703441140667/100000000000000 : ℝ)^6229
        have hw : |(199595687/400000000 : ℝ)|=(199595687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677789803/1250000000 : ℝ)*x 0 + (1247472833/2500000000 : ℝ)*x 1 + (-2512881573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677789803/1250000000 : ℝ)^8277 ≤ (4433932876311/10000000000000 : ℝ)^6229 := by
    have hnat : (677789803 : ℕ)^8277*10000000000000^6229 ≤ 4433932876311^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677789803 1250000000 4433932876311 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247472833/2500000000 : ℝ)^8277 ≤ (9925858056941/25000000000000 : ℝ)^6229 := by
    have hnat : (1247472833 : ℕ)^8277*25000000000000^6229 ≤ 9925858056941^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247472833 2500000000 9925858056941 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512881573/10000000000 : ℝ)^8277 ≤ (15957239000571/100000000000000 : ℝ)^6229 := by
    have hnat : (2512881573 : ℕ)^8277*100000000000000^6229 ≤ 15957239000571^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512881573 10000000000 15957239000571 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677789803/1250000000 : ℝ), (1247472833/2500000000 : ℝ), (-2512881573/10000000000 : ℝ)] ![(4433932876311/10000000000000 : ℝ), (9925858056941/25000000000000 : ℝ), (15957239000571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677789803/1250000000 : ℝ)|^8277 ≤ (4433932876311/10000000000000 : ℝ)^6229
        have hw : |(677789803/1250000000 : ℝ)|=(677789803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1247472833/2500000000 : ℝ)|^8277 ≤ (9925858056941/25000000000000 : ℝ)^6229
        have hw : |(1247472833/2500000000 : ℝ)|=(1247472833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2512881573/10000000000 : ℝ)|^8277 ≤ (15957239000571/100000000000000 : ℝ)^6229
        have hw : |(-2512881573/10000000000 : ℝ)|=(2512881573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864461599/2000000000 : ℝ)*x 0 + (3666011229/10000000000 : ℝ)*x 1 + (1274182189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864461599/2000000000 : ℝ)^8277 ≤ (32805344531043/100000000000000 : ℝ)^6229 := by
    have hnat : (864461599 : ℕ)^8277*100000000000000^6229 ≤ 32805344531043^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864461599 2000000000 32805344531043 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3666011229/10000000000 : ℝ)^8277 ≤ (1054307658431/4000000000000 : ℝ)^6229 := by
    have hnat : (3666011229 : ℕ)^8277*4000000000000^6229 ≤ 1054307658431^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666011229 10000000000 1054307658431 4000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274182189/2500000000 : ℝ)^8277 ≤ (40836963993791/100000000000000 : ℝ)^6229 := by
    have hnat : (1274182189 : ℕ)^8277*100000000000000^6229 ≤ 40836963993791^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274182189 2500000000 40836963993791 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864461599/2000000000 : ℝ), (3666011229/10000000000 : ℝ), (1274182189/2500000000 : ℝ)] ![(32805344531043/100000000000000 : ℝ), (1054307658431/4000000000000 : ℝ), (40836963993791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864461599/2000000000 : ℝ)|^8277 ≤ (32805344531043/100000000000000 : ℝ)^6229
        have hw : |(864461599/2000000000 : ℝ)|=(864461599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3666011229/10000000000 : ℝ)|^8277 ≤ (1054307658431/4000000000000 : ℝ)^6229
        have hw : |(3666011229/10000000000 : ℝ)|=(3666011229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274182189/2500000000 : ℝ)|^8277 ≤ (40836963993791/100000000000000 : ℝ)^6229
        have hw : |(1274182189/2500000000 : ℝ)|=(1274182189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-265004793/1250000000 : ℝ)*x 0 + (1250011523/2500000000 : ℝ)*x 1 + (5706943173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265004793/1250000000 : ℝ)^8277 ≤ (12730803807627/100000000000000 : ℝ)^6229 := by
    have hnat : (265004793 : ℕ)^8277*100000000000000^6229 ≤ 12730803807627^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265004793 1250000000 12730803807627 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250011523/2500000000 : ℝ)^8277 ≤ (796216655303/2000000000000 : ℝ)^6229 := by
    have hnat : (1250011523 : ℕ)^8277*2000000000000^6229 ≤ 796216655303^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250011523 2500000000 796216655303 2000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5706943173/10000000000 : ℝ)^8277 ≤ (23729181707773/50000000000000 : ℝ)^6229 := by
    have hnat : (5706943173 : ℕ)^8277*50000000000000^6229 ≤ 23729181707773^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706943173 10000000000 23729181707773 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265004793/1250000000 : ℝ), (1250011523/2500000000 : ℝ), (5706943173/10000000000 : ℝ)] ![(12730803807627/100000000000000 : ℝ), (796216655303/2000000000000 : ℝ), (23729181707773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265004793/1250000000 : ℝ)|^8277 ≤ (12730803807627/100000000000000 : ℝ)^6229
        have hw : |(-265004793/1250000000 : ℝ)|=(265004793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250011523/2500000000 : ℝ)|^8277 ≤ (796216655303/2000000000000 : ℝ)^6229
        have hw : |(1250011523/2500000000 : ℝ)|=(1250011523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5706943173/10000000000 : ℝ)|^8277 ≤ (23729181707773/50000000000000 : ℝ)^6229
        have hw : |(5706943173/10000000000 : ℝ)|=(5706943173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5236373683/10000000000 : ℝ)*x 0 + (-1795830339/10000000000 : ℝ)*x 1 + (356683939/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236373683/10000000000 : ℝ)^8277 ≤ (42330382939149/100000000000000 : ℝ)^6229 := by
    have hnat : (5236373683 : ℕ)^8277*100000000000000^6229 ≤ 42330382939149^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236373683 10000000000 42330382939149 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1795830339/10000000000 : ℝ)^8277 ≤ (5105627640811/50000000000000 : ℝ)^6229 := by
    have hnat : (1795830339 : ℕ)^8277*50000000000000^6229 ≤ 5105627640811^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795830339 10000000000 5105627640811 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356683939/625000000 : ℝ)^8277 ≤ (47458361769091/100000000000000 : ℝ)^6229 := by
    have hnat : (356683939 : ℕ)^8277*100000000000000^6229 ≤ 47458361769091^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356683939 625000000 47458361769091 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236373683/10000000000 : ℝ), (-1795830339/10000000000 : ℝ), (356683939/625000000 : ℝ)] ![(42330382939149/100000000000000 : ℝ), (5105627640811/50000000000000 : ℝ), (47458361769091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236373683/10000000000 : ℝ)|^8277 ≤ (42330382939149/100000000000000 : ℝ)^6229
        have hw : |(5236373683/10000000000 : ℝ)|=(5236373683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1795830339/10000000000 : ℝ)|^8277 ≤ (5105627640811/50000000000000 : ℝ)^6229
        have hw : |(-1795830339/10000000000 : ℝ)|=(1795830339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356683939/625000000 : ℝ)|^8277 ≤ (47458361769091/100000000000000 : ℝ)^6229
        have hw : |(356683939/625000000 : ℝ)|=(356683939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52363737/100000000 : ℝ)*x 0 + (5706943139/10000000000 : ℝ)*x 1 + (-359166029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52363737/100000000 : ℝ)^8277 ≤ (42330383121759/100000000000000 : ℝ)^6229 := by
    have hnat : (52363737 : ℕ)^8277*100000000000000^6229 ≤ 42330383121759^6229*100000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52363737 100000000 42330383121759 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5706943139/10000000000 : ℝ)^8277 ≤ (9491672607969/20000000000000 : ℝ)^6229 := by
    have hnat : (5706943139 : ℕ)^8277*20000000000000^6229 ≤ 9491672607969^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706943139 10000000000 9491672607969 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359166029/2000000000 : ℝ)^8277 ≤ (10211253815837/100000000000000 : ℝ)^6229 := by
    have hnat : (359166029 : ℕ)^8277*100000000000000^6229 ≤ 10211253815837^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359166029 2000000000 10211253815837 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52363737/100000000 : ℝ), (5706943139/10000000000 : ℝ), (-359166029/2000000000 : ℝ)] ![(42330383121759/100000000000000 : ℝ), (9491672607969/20000000000000 : ℝ), (10211253815837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52363737/100000000 : ℝ)|^8277 ≤ (42330383121759/100000000000000 : ℝ)^6229
        have hw : |(52363737/100000000 : ℝ)|=(52363737/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5706943139/10000000000 : ℝ)|^8277 ≤ (9491672607969/20000000000000 : ℝ)^6229
        have hw : |(5706943139/10000000000 : ℝ)|=(5706943139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359166029/2000000000 : ℝ)|^8277 ≤ (10211253815837/100000000000000 : ℝ)^6229
        have hw : |(-359166029/2000000000 : ℝ)|=(359166029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s1_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4324059479/10000000000 : ℝ)*x 0 + (5076757631/10000000000 : ℝ)*x 1 + (230399089/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324059479/10000000000 : ℝ)^8277 ≤ (16411504866739/50000000000000 : ℝ)^6229 := by
    have hnat : (4324059479 : ℕ)^8277*50000000000000^6229 ≤ 16411504866739^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324059479 10000000000 16411504866739 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076757631/10000000000 : ℝ)^8277 ≤ (40624473752493/100000000000000 : ℝ)^6229 := by
    have hnat : (5076757631 : ℕ)^8277*100000000000000^6229 ≤ 40624473752493^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076757631 10000000000 40624473752493 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230399089/625000000 : ℝ)^8277 ≤ (26552516499593/100000000000000 : ℝ)^6229 := by
    have hnat : (230399089 : ℕ)^8277*100000000000000^6229 ≤ 26552516499593^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230399089 625000000 26552516499593 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324059479/10000000000 : ℝ), (5076757631/10000000000 : ℝ), (230399089/625000000 : ℝ)] ![(16411504866739/50000000000000 : ℝ), (40624473752493/100000000000000 : ℝ), (26552516499593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324059479/10000000000 : ℝ)|^8277 ≤ (16411504866739/50000000000000 : ℝ)^6229
        have hw : |(4324059479/10000000000 : ℝ)|=(4324059479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076757631/10000000000 : ℝ)|^8277 ≤ (40624473752493/100000000000000 : ℝ)^6229
        have hw : |(5076757631/10000000000 : ℝ)|=(5076757631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230399089/625000000 : ℝ)|^8277 ≤ (26552516499593/100000000000000 : ℝ)^6229
        have hw : |(230399089/625000000 : ℝ)|=(230399089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4141/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (43/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (43/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (43/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (43/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (43/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (43/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (43/25000 : ℝ) ^ (2069/512 : ℝ) ≤ (674104551/100000000000000000000 : ℝ) := by
    have hpowers : (43/25000 : ℝ)^2069 ≤ (674104551/100000000000000000000 : ℝ)^512 := by
      have hnat : (43 : ℕ)^2069*100000000000000000000^512 ≤ 674104551^512*25000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 25000 674104551 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/25000 : ℝ)) (X := (674104551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (28039/100000 : ℝ) ^ (2069/512 : ℝ) ≤ (293338942150001587/50000000000000000000 : ℝ) := by
    have hpowers : (28039/100000 : ℝ)^2069 ≤ (293338942150001587/50000000000000000000 : ℝ)^512 := by
      have hnat : (28039 : ℕ)^2069*50000000000000000000^512 ≤ 293338942150001587^512*100000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28039 100000 293338942150001587 50000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28039/100000 : ℝ)) (X := (293338942150001587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000674104551/50000000000000000000 : ℝ) ≤ (2500000000008341/2500000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50000000000674104551/50000000000000000000 : ℝ)^512 ≤ (2500000000008341/2500000000000000 : ℝ)^2069 := by
      have hnat : (50000000000674104551 : ℕ)^512*2500000000000000^2069 ≤ 2500000000008341^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000674104551 50000000000000000000 2500000000008341 2500000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000008341/2500000000000000 : ℝ)) (X := (50000000000674104551/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4023467115398964309/4000000000000000000 : ℝ) ≤ (2002897228207717/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (4023467115398964309/4000000000000000000 : ℝ)^512 ≤ (2002897228207717/2000000000000000 : ℝ)^2069 := by
      have hnat : (4023467115398964309 : ℕ)^512*2000000000000000^2069 ≤ 2002897228207717^2069*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4023467115398964309 4000000000000000000 2002897228207717 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002897228207717/2000000000000000 : ℝ)) (X := (4023467115398964309/4000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25293338942150001587/25000000000000000000 : ℝ) ≤ (5014486141021903/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (25293338942150001587/25000000000000000000 : ℝ)^512 ≤ (5014486141021903/5000000000000000 : ℝ)^2069 := by
      have hnat : (25293338942150001587 : ℕ)^512*5000000000000000^2069 ≤ 5014486141021903^2069*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25293338942150001587 25000000000000000000 5014486141021903 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014486141021903/5000000000000000 : ℝ)) (X := (25293338942150001587/25000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(674104551/100000000000000000000 : ℝ) ≤ ((23222084730701996547/23222500000000000000 : ℝ)+2*(4828713668407/928900000000000 : ℝ)*(43/25000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (23222084730701996547/23222500000000000000 : ℝ)+2*(4828713668407/928900000000000 : ℝ)*(43/25000 : ℝ)=(2500000000008341/2500000000000000 : ℝ) by norm_num, show 1+2*(674104551/100000000000000000000 : ℝ)=(50000000000674104551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(293338942150001587/50000000000000000000 : ℝ)+(674104551/100000000000000000000 : ℝ) ≤ ((23222084730701996547/23222500000000000000 : ℝ)+(4828713668407/928900000000000 : ℝ)*((28039/100000 : ℝ)+(43/25000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (23222084730701996547/23222500000000000000 : ℝ)+(4828713668407/928900000000000 : ℝ)*((28039/100000 : ℝ)+(43/25000 : ℝ))=(2002897228207717/2000000000000000 : ℝ) by norm_num, show 1+(293338942150001587/50000000000000000000 : ℝ)+(674104551/100000000000000000000 : ℝ)=(4023467115398964309/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(293338942150001587/50000000000000000000 : ℝ) ≤ ((23222084730701996547/23222500000000000000 : ℝ)+2*(4828713668407/928900000000000 : ℝ)*(28039/100000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (23222084730701996547/23222500000000000000 : ℝ)+2*(4828713668407/928900000000000 : ℝ)*(28039/100000 : ℝ)=(5014486141021903/5000000000000000 : ℝ) by norm_num, show 1+2*(293338942150001587/50000000000000000000 : ℝ)=(25293338942150001587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23222084730701996547/23222500000000000000 : ℝ)*(X 1 0+X 2 0)+(4828713668407/928900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (43/25000 : ℝ)) (hi := (28039/100000 : ℝ)) (c := (23222084730701996547/23222500000000000000 : ℝ)) (alpha := (4828713668407/928900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23222084730701996547/23222500000000000000 : ℝ)*(X 0 1+X 2 1)+(4828713668407/928900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (43/25000 : ℝ)) (hi := (28039/100000 : ℝ)) (c := (23222084730701996547/23222500000000000000 : ℝ)) (alpha := (4828713668407/928900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23222084730701996547/23222500000000000000 : ℝ)*(X 0 2+X 1 2)+(4828713668407/928900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (43/25000 : ℝ)) (hi := (28039/100000 : ℝ)) (c := (23222084730701996547/23222500000000000000 : ℝ)) (alpha := (4828713668407/928900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119147503/10000000000 : ℝ)*X 0 0+(5717302233/10000000000 : ℝ)*X 0 1+(2494945959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711158811/5000000000 : ℝ)*X 1 0+(-2512881549/10000000000 : ℝ)*X 1 1+(199595687/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677789803/1250000000 : ℝ)*X 2 0+(1247472833/2500000000 : ℝ)*X 2 1+(-2512881573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864461599/2000000000 : ℝ)*X 0 0+(3666011229/10000000000 : ℝ)*X 0 1+(1274182189/2500000000 : ℝ)*X 0 2+(864461599/2000000000 : ℝ)*X 1 0+(3666011229/10000000000 : ℝ)*X 1 1+(1274182189/2500000000 : ℝ)*X 1 2+(864461599/2000000000 : ℝ)*X 2 0+(3666011229/10000000000 : ℝ)*X 2 1+(1274182189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-265004793/1250000000 : ℝ)*X 0 0+(1250011523/2500000000 : ℝ)*X 0 1+(5706943173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236373683/10000000000 : ℝ)*X 1 0+(-1795830339/10000000000 : ℝ)*X 1 1+(356683939/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52363737/100000000 : ℝ)*X 2 0+(5706943139/10000000000 : ℝ)*X 2 1+(-359166029/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324059479/10000000000 : ℝ)*X 0 0+(5076757631/10000000000 : ℝ)*X 0 1+(230399089/625000000 : ℝ)*X 0 2+(4324059479/10000000000 : ℝ)*X 1 0+(5076757631/10000000000 : ℝ)*X 1 1+(230399089/625000000 : ℝ)*X 1 2+(4324059479/10000000000 : ℝ)*X 2 0+(5076757631/10000000000 : ℝ)*X 2 1+(230399089/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1266601411902698913866837931/145140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175036319/100000000000000 : ℝ)*(base1) + (57144247/3125000000000 : ℝ)*(base19) + (1015976127/50000000000000 : ℝ)*(base23) + (170260041/100000000000000 : ℝ)*(upper3) + (217199883/100000000000000 : ℝ)*(upper5) + (64803652951783/6250000000000 : ℝ)*(major0) + (64803652951783/6250000000000 : ℝ)*(major1) + (64803652951783/6250000000000 : ℝ)*(major2) + (10740222565927/781250000000 : ℝ)*(sp0) + (1374756161727761/100000000000000 : ℝ)*(sp1) + (137475595839141/10000000000000 : ℝ)*(sp2) + (698954150224469/100000000000000 : ℝ)*(sp3) + (9676941327/100000000000000 : ℝ)*(sp4) + (428796197/10000000000000 : ℝ)*(sp7) + (698958613222757/100000000000000 : ℝ)*(f.failure) + (274951598068733/20000000000000 : ℝ)*(f.sum) + (158216490468009/46445000000000000000000000000 : ℝ)*base66 + (239930134222451787/72570312500000000000000000000000 : ℝ)*base68 + (595845447702704463/72570312500000000000000000000000 : ℝ)*base69 + (145467479236014287/72570312500000000000000000000000 : ℝ)*base72 + (102745240222797/23222500000000000000000000000 : ℝ)*base74 + (234125061917951787/72570312500000000000000000000000 : ℝ)*base76 + (25652470908460603/18142578125000000000000000000000 : ℝ)*base78 + (325371178267141963/72570312500000000000000000000000 : ℝ)*base79 + (67032268974583/23222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2438119/400000000000000000000 : ℝ)*base90 + (2438119/400000000000000000000 : ℝ)*base92 + (2438119/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1033549722555736494490512321/580562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5052503/20000000000000 : ℝ)*(base1) + (84124103/20000000000000 : ℝ)*(base19) + (219411109/50000000000000 : ℝ)*(base23) + (4687541/12500000000000 : ℝ)*(upper3) + (2329403/6250000000000 : ℝ)*(upper5) + (533466271117019/50000000000000 : ℝ)*(major0) + (533466271117019/50000000000000 : ℝ)*(major1) + (533466271117019/50000000000000 : ℝ)*(major2) + (1500301527/100000000000000 : ℝ)*(sp1) + (117721187/6250000000000 : ℝ)*(sp2) + (1414633131976467/100000000000000 : ℝ)*(sp4) + (1414631185791909/100000000000000 : ℝ)*(sp5) + (1414630784352741/100000000000000 : ℝ)*(sp6) + (179807973287437/25000000000000 : ℝ)*(sp7) + (719231918412263/100000000000000 : ℝ)*(f.failure) + (1414633106713951/100000000000000 : ℝ)*(f.sum) + (31742181361557/23222500000000000000000000000 : ℝ)*base66 + (5923507057373258393/1161125000000000000000000000000000 : ℝ)*base67 + (5115005253551616607/1161125000000000000000000000000000 : ℝ)*base70 + (2662421332809633393/1161125000000000000000000000000000 : ℝ)*base71 + (1063486833421/2902812500000000000000000000 : ℝ)*base73 + (887040559582866607/1161125000000000000000000000000000 : ℝ)*base76 + (3624110728339258393/1161125000000000000000000000000000 : ℝ)*base77 + (6607067871556883393/1161125000000000000000000000000000 : ℝ)*base79 + (267437856823029/46445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (567779/400000000000000000000 : ℝ)*base89 + (567779/400000000000000000000 : ℝ)*base91 + (567779/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4141/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s2_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435112161/2000000000 : ℝ)*x 0 + (690275993/1250000000 : ℝ)*x 1 + (2574587749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435112161/2000000000 : ℝ)^8277 ≤ (13175732505163/100000000000000 : ℝ)^6229 := by
    have hnat : (435112161 : ℕ)^8277*100000000000000^6229 ≤ 13175732505163^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435112161 2000000000 13175732505163 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690275993/1250000000 : ℝ)^8277 ≤ (283924839797/625000000000 : ℝ)^6229 := by
    have hnat : (690275993 : ℕ)^8277*625000000000^6229 ≤ 283924839797^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690275993 1250000000 283924839797 625000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574587749/5000000000 : ℝ)^8277 ≤ (20698146559281/50000000000000 : ℝ)^6229 := by
    have hnat : (2574587749 : ℕ)^8277*50000000000000^6229 ≤ 20698146559281^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574587749 5000000000 20698146559281 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435112161/2000000000 : ℝ), (690275993/1250000000 : ℝ), (2574587749/5000000000 : ℝ)] ![(13175732505163/100000000000000 : ℝ), (283924839797/625000000000 : ℝ), (20698146559281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435112161/2000000000 : ℝ)|^8277 ≤ (13175732505163/100000000000000 : ℝ)^6229
        have hw : |(-435112161/2000000000 : ℝ)|=(435112161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690275993/1250000000 : ℝ)|^8277 ≤ (283924839797/625000000000 : ℝ)^6229
        have hw : |(690275993/1250000000 : ℝ)|=(690275993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574587749/5000000000 : ℝ)|^8277 ≤ (20698146559281/50000000000000 : ℝ)^6229
        have hw : |(2574587749/5000000000 : ℝ)|=(2574587749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688198481/5000000000 : ℝ)*x 0 + (-2369955063/10000000000 : ℝ)*x 1 + (1029835207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688198481/5000000000 : ℝ)^8277 ≤ (109602636941/250000000000 : ℝ)^6229 := by
    have hnat : (2688198481 : ℕ)^8277*250000000000^6229 ≤ 109602636941^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688198481 5000000000 109602636941 250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2369955063/10000000000 : ℝ)^8277 ≤ (922665396941/6250000000000 : ℝ)^6229 := by
    have hnat : (2369955063 : ℕ)^8277*6250000000000^6229 ≤ 922665396941^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369955063 10000000000 922665396941 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029835207/2000000000 : ℝ)^8277 ≤ (41396298855137/100000000000000 : ℝ)^6229 := by
    have hnat : (1029835207 : ℕ)^8277*100000000000000^6229 ≤ 41396298855137^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029835207 2000000000 41396298855137 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688198481/5000000000 : ℝ), (-2369955063/10000000000 : ℝ), (1029835207/2000000000 : ℝ)] ![(109602636941/250000000000 : ℝ), (922665396941/6250000000000 : ℝ), (41396298855137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688198481/5000000000 : ℝ)|^8277 ≤ (109602636941/250000000000 : ℝ)^6229
        have hw : |(2688198481/5000000000 : ℝ)|=(2688198481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2369955063/10000000000 : ℝ)|^8277 ≤ (922665396941/6250000000000 : ℝ)^6229
        have hw : |(-2369955063/10000000000 : ℝ)|=(2369955063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029835207/2000000000 : ℝ)|^8277 ≤ (41396298855137/100000000000000 : ℝ)^6229
        have hw : |(1029835207/2000000000 : ℝ)|=(1029835207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376397107/10000000000 : ℝ)*x 0 + (5149175873/10000000000 : ℝ)*x 1 + (-2369955083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376397107/10000000000 : ℝ)^8277 ≤ (43841056347531/100000000000000 : ℝ)^6229 := by
    have hnat : (5376397107 : ℕ)^8277*100000000000000^6229 ≤ 43841056347531^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376397107 10000000000 43841056347531 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149175873/10000000000 : ℝ)^8277 ≤ (41396297124551/100000000000000 : ℝ)^6229 := by
    have hnat : (5149175873 : ℕ)^8277*100000000000000^6229 ≤ 41396297124551^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149175873 10000000000 41396297124551 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2369955083/10000000000 : ℝ)^8277 ≤ (7381323258299/50000000000000 : ℝ)^6229 := by
    have hnat : (2369955083 : ℕ)^8277*50000000000000^6229 ≤ 7381323258299^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369955083 10000000000 7381323258299 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376397107/10000000000 : ℝ), (5149175873/10000000000 : ℝ), (-2369955083/10000000000 : ℝ)] ![(43841056347531/100000000000000 : ℝ), (41396297124551/100000000000000 : ℝ), (7381323258299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376397107/10000000000 : ℝ)|^8277 ≤ (43841056347531/100000000000000 : ℝ)^6229
        have hw : |(5376397107/10000000000 : ℝ)|=(5376397107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149175873/10000000000 : ℝ)|^8277 ≤ (41396297124551/100000000000000 : ℝ)^6229
        have hw : |(5149175873/10000000000 : ℝ)|=(5149175873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2369955083/10000000000 : ℝ)|^8277 ≤ (7381323258299/50000000000000 : ℝ)^6229
        have hw : |(-2369955083/10000000000 : ℝ)|=(2369955083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180425627/5000000000 : ℝ)*x 0 + (4009495507/10000000000 : ℝ)*x 1 + (4743199401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180425627/5000000000 : ℝ)^8277 ≤ (33194628812229/100000000000000 : ℝ)^6229 := by
    have hnat : (2180425627 : ℕ)^8277*100000000000000^6229 ≤ 33194628812229^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180425627 5000000000 33194628812229 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009495507/10000000000 : ℝ)^8277 ≤ (29688735521131/100000000000000 : ℝ)^6229 := by
    have hnat : (4009495507 : ℕ)^8277*100000000000000^6229 ≤ 29688735521131^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009495507 10000000000 29688735521131 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4743199401/10000000000 : ℝ)^8277 ≤ (37116635653359/100000000000000 : ℝ)^6229 := by
    have hnat : (4743199401 : ℕ)^8277*100000000000000^6229 ≤ 37116635653359^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743199401 10000000000 37116635653359 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180425627/5000000000 : ℝ), (4009495507/10000000000 : ℝ), (4743199401/10000000000 : ℝ)] ![(33194628812229/100000000000000 : ℝ), (29688735521131/100000000000000 : ℝ), (37116635653359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180425627/5000000000 : ℝ)|^8277 ≤ (33194628812229/100000000000000 : ℝ)^6229
        have hw : |(2180425627/5000000000 : ℝ)|=(2180425627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009495507/10000000000 : ℝ)|^8277 ≤ (29688735521131/100000000000000 : ℝ)^6229
        have hw : |(4009495507/10000000000 : ℝ)|=(4009495507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4743199401/10000000000 : ℝ)|^8277 ≤ (37116635653359/100000000000000 : ℝ)^6229
        have hw : |(4743199401/10000000000 : ℝ)|=(4743199401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087840381/5000000000 : ℝ)*x 0 + (5151854691/10000000000 : ℝ)*x 1 + (2759750451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087840381/5000000000 : ℝ)^8277 ≤ (13176697861607/100000000000000 : ℝ)^6229 := by
    have hnat : (1087840381 : ℕ)^8277*100000000000000^6229 ≤ 13176697861607^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087840381 5000000000 13176697861607 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151854691/10000000000 : ℝ)^8277 ≤ (8284983281379/20000000000000 : ℝ)^6229 := by
    have hnat : (5151854691 : ℕ)^8277*20000000000000^6229 ≤ 8284983281379^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151854691 10000000000 8284983281379 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759750451/5000000000 : ℝ)^8277 ≤ (9079677142419/20000000000000 : ℝ)^6229 := by
    have hnat : (2759750451 : ℕ)^8277*20000000000000^6229 ≤ 9079677142419^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759750451 5000000000 9079677142419 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087840381/5000000000 : ℝ), (5151854691/10000000000 : ℝ), (2759750451/5000000000 : ℝ)] ![(13176697861607/100000000000000 : ℝ), (8284983281379/20000000000000 : ℝ), (9079677142419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087840381/5000000000 : ℝ)|^8277 ≤ (13176697861607/100000000000000 : ℝ)^6229
        have hw : |(-1087840381/5000000000 : ℝ)|=(1087840381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151854691/10000000000 : ℝ)|^8277 ≤ (8284983281379/20000000000000 : ℝ)^6229
        have hw : |(5151854691/10000000000 : ℝ)|=(5151854691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759750451/5000000000 : ℝ)|^8277 ≤ (9079677142419/20000000000000 : ℝ)^6229
        have hw : |(2759750451/5000000000 : ℝ)|=(2759750451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282121471/10000000000 : ℝ)*x 0 + (-999815049/5000000000 : ℝ)*x 1 + (5519500997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282121471/10000000000 : ℝ)^8277 ≤ (42822499943921/100000000000000 : ℝ)^6229 := by
    have hnat : (5282121471 : ℕ)^8277*100000000000000^6229 ≤ 42822499943921^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282121471 10000000000 42822499943921 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999815049/5000000000 : ℝ)^8277 ≤ (5889556644209/50000000000000 : ℝ)^6229 := by
    have hnat : (999815049 : ℕ)^8277*50000000000000^6229 ≤ 5889556644209^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999815049 5000000000 5889556644209 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519500997/10000000000 : ℝ)^8277 ≤ (9079677350077/20000000000000 : ℝ)^6229 := by
    have hnat : (5519500997 : ℕ)^8277*20000000000000^6229 ≤ 9079677350077^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519500997 10000000000 9079677350077 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282121471/10000000000 : ℝ), (-999815049/5000000000 : ℝ), (5519500997/10000000000 : ℝ)] ![(42822499943921/100000000000000 : ℝ), (5889556644209/50000000000000 : ℝ), (9079677350077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282121471/10000000000 : ℝ)|^8277 ≤ (42822499943921/100000000000000 : ℝ)^6229
        have hw : |(5282121471/10000000000 : ℝ)|=(5282121471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999815049/5000000000 : ℝ)|^8277 ≤ (5889556644209/50000000000000 : ℝ)^6229
        have hw : |(-999815049/5000000000 : ℝ)|=(999815049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519500997/10000000000 : ℝ)|^8277 ≤ (9079677350077/20000000000000 : ℝ)^6229
        have hw : |(5519500997/10000000000 : ℝ)|=(5519500997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282121701/10000000000 : ℝ)*x 0 + (5519500849/10000000000 : ℝ)*x 1 + (-1999629989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282121701/10000000000 : ℝ)^8277 ≤ (21411251210803/50000000000000 : ℝ)^6229 := by
    have hnat : (5282121701 : ℕ)^8277*50000000000000^6229 ≤ 21411251210803^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282121701 10000000000 21411251210803 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519500849/10000000000 : ℝ)^8277 ≤ (22699192566419/50000000000000 : ℝ)^6229 := by
    have hnat : (5519500849 : ℕ)^8277*50000000000000^6229 ≤ 22699192566419^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519500849 10000000000 22699192566419 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999629989/10000000000 : ℝ)^8277 ≤ (11779112435231/100000000000000 : ℝ)^6229 := by
    have hnat : (1999629989 : ℕ)^8277*100000000000000^6229 ≤ 11779112435231^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999629989 10000000000 11779112435231 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282121701/10000000000 : ℝ), (5519500849/10000000000 : ℝ), (-1999629989/10000000000 : ℝ)] ![(21411251210803/50000000000000 : ℝ), (22699192566419/50000000000000 : ℝ), (11779112435231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282121701/10000000000 : ℝ)|^8277 ≤ (21411251210803/50000000000000 : ℝ)^6229
        have hw : |(5282121701/10000000000 : ℝ)|=(5282121701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519500849/10000000000 : ℝ)|^8277 ≤ (22699192566419/50000000000000 : ℝ)^6229
        have hw : |(5519500849/10000000000 : ℝ)|=(5519500849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999629989/10000000000 : ℝ)|^8277 ≤ (11779112435231/100000000000000 : ℝ)^6229
        have hw : |(-1999629989/10000000000 : ℝ)|=(1999629989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s2_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436108737/1000000000 : ℝ)*x 0 + (1184482593/2500000000 : ℝ)*x 1 + (4014818939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436108737/1000000000 : ℝ)^8277 ≤ (33197017065881/100000000000000 : ℝ)^6229 := by
    have hnat : (436108737 : ℕ)^8277*100000000000000^6229 ≤ 33197017065881^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436108737 1000000000 33197017065881 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1184482593/2500000000 : ℝ)^8277 ≤ (463273225513/1250000000000 : ℝ)^6229 := by
    have hnat : (1184482593 : ℕ)^8277*1250000000000^6229 ≤ 463273225513^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184482593 2500000000 463273225513 1250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014818939/10000000000 : ℝ)^8277 ≤ (29741124876859/100000000000000 : ℝ)^6229 := by
    have hnat : (4014818939 : ℕ)^8277*100000000000000^6229 ≤ 29741124876859^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014818939 10000000000 29741124876859 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436108737/1000000000 : ℝ), (1184482593/2500000000 : ℝ), (4014818939/10000000000 : ℝ)] ![(33197017065881/100000000000000 : ℝ), (463273225513/1250000000000 : ℝ), (29741124876859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436108737/1000000000 : ℝ)|^8277 ≤ (33197017065881/100000000000000 : ℝ)^6229
        have hw : |(436108737/1000000000 : ℝ)|=(436108737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1184482593/2500000000 : ℝ)|^8277 ≤ (463273225513/1250000000000 : ℝ)^6229
        have hw : |(1184482593/2500000000 : ℝ)|=(1184482593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014818939/10000000000 : ℝ)|^8277 ≤ (29741124876859/100000000000000 : ℝ)^6229
        have hw : |(4014818939/10000000000 : ℝ)|=(4014818939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4141/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8799/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4141/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4141/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4141/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4141/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4141/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4141/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2659/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (177283824519657/25000000000000000000 : ℝ) := by
    have hpowers : (2659/50000 : ℝ)^2069 ≤ (177283824519657/25000000000000000000 : ℝ)^512 := by
      have hnat : (2659 : ℕ)^2069*25000000000000000000^512 ≤ 177283824519657^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2659 50000 177283824519657 25000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2659/50000 : ℝ)) (X := (177283824519657/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4141/20000 : ℝ) ^ (2069/512 : ℝ) ≤ (172285742002381401/100000000000000000000 : ℝ) := by
    have hpowers : (4141/20000 : ℝ)^2069 ≤ (172285742002381401/100000000000000000000 : ℝ)^512 := by
      have hnat : (4141 : ℕ)^2069*100000000000000000000^512 ≤ 172285742002381401^512*20000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4141 20000 172285742002381401 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4141/20000 : ℝ)) (X := (172285742002381401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500177283824519657/12500000000000000000 : ℝ) ≤ (2000007019339489/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (12500177283824519657/12500000000000000000 : ℝ)^512 ≤ (2000007019339489/2000000000000000 : ℝ)^2069 := by
      have hnat : (12500177283824519657 : ℕ)^512*2000000000000000^2069 ≤ 2000007019339489^2069*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500177283824519657 12500000000000000000 2000007019339489 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000007019339489/2000000000000000 : ℝ)) (X := (12500177283824519657/12500000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100172994877300460029/100000000000000000000 : ℝ) ≤ (400171127657213/400000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (100172994877300460029/100000000000000000000 : ℝ)^512 ≤ (400171127657213/400000000000000 : ℝ)^2069 := by
      have hnat : (100172994877300460029 : ℕ)^512*400000000000000^2069 ≤ 400171127657213^2069*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100172994877300460029 100000000000000000000 400171127657213 400000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400171127657213/400000000000000 : ℝ)) (X := (100172994877300460029/100000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50172285742002381401/50000000000000000000 : ℝ) ≤ (2001704257232641/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50172285742002381401/50000000000000000000 : ℝ)^512 ≤ (2001704257232641/2000000000000000 : ℝ)^2069 := by
      have hnat : (50172285742002381401 : ℕ)^512*2000000000000000^2069 ≤ 2001704257232641^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50172285742002381401 50000000000000000000 2001704257232641 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001704257232641/2000000000000000 : ℝ)) (X := (50172285742002381401/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(177283824519657/25000000000000000000 : ℝ) ≤ ((10255027365153644969/10258000000000000000 : ℝ)+2*(17679561387/6411250000000 : ℝ)*(2659/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (10255027365153644969/10258000000000000000 : ℝ)+2*(17679561387/6411250000000 : ℝ)*(2659/50000 : ℝ)=(2000007019339489/2000000000000000 : ℝ) by norm_num, show 1+2*(177283824519657/25000000000000000000 : ℝ)=(12500177283824519657/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172285742002381401/100000000000000000000 : ℝ)+(177283824519657/25000000000000000000 : ℝ) ≤ ((10255027365153644969/10258000000000000000 : ℝ)+(17679561387/6411250000000 : ℝ)*((4141/20000 : ℝ)+(2659/50000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (10255027365153644969/10258000000000000000 : ℝ)+(17679561387/6411250000000 : ℝ)*((4141/20000 : ℝ)+(2659/50000 : ℝ))=(400171127657213/400000000000000 : ℝ) by norm_num, show 1+(172285742002381401/100000000000000000000 : ℝ)+(177283824519657/25000000000000000000 : ℝ)=(100172994877300460029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172285742002381401/100000000000000000000 : ℝ) ≤ ((10255027365153644969/10258000000000000000 : ℝ)+2*(17679561387/6411250000000 : ℝ)*(4141/20000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (10255027365153644969/10258000000000000000 : ℝ)+2*(17679561387/6411250000000 : ℝ)*(4141/20000 : ℝ)=(2001704257232641/2000000000000000 : ℝ) by norm_num, show 1+2*(172285742002381401/100000000000000000000 : ℝ)=(50172285742002381401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10255027365153644969/10258000000000000000 : ℝ)*(X 1 0+X 2 0)+(17679561387/6411250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2659/50000 : ℝ)) (hi := (4141/20000 : ℝ)) (c := (10255027365153644969/10258000000000000000 : ℝ)) (alpha := (17679561387/6411250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10255027365153644969/10258000000000000000 : ℝ)*(X 0 1+X 2 1)+(17679561387/6411250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2659/50000 : ℝ)) (hi := (4141/20000 : ℝ)) (c := (10255027365153644969/10258000000000000000 : ℝ)) (alpha := (17679561387/6411250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10255027365153644969/10258000000000000000 : ℝ)*(X 0 2+X 1 2)+(17679561387/6411250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2659/50000 : ℝ)) (hi := (4141/20000 : ℝ)) (c := (10255027365153644969/10258000000000000000 : ℝ)) (alpha := (17679561387/6411250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435112161/2000000000 : ℝ)*X 0 0+(690275993/1250000000 : ℝ)*X 0 1+(2574587749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688198481/5000000000 : ℝ)*X 1 0+(-2369955063/10000000000 : ℝ)*X 1 1+(1029835207/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376397107/10000000000 : ℝ)*X 2 0+(5149175873/10000000000 : ℝ)*X 2 1+(-2369955083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180425627/5000000000 : ℝ)*X 0 0+(4009495507/10000000000 : ℝ)*X 0 1+(4743199401/10000000000 : ℝ)*X 0 2+(2180425627/5000000000 : ℝ)*X 1 0+(4009495507/10000000000 : ℝ)*X 1 1+(4743199401/10000000000 : ℝ)*X 1 2+(2180425627/5000000000 : ℝ)*X 2 0+(4009495507/10000000000 : ℝ)*X 2 1+(4743199401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087840381/5000000000 : ℝ)*X 0 0+(5151854691/10000000000 : ℝ)*X 0 1+(2759750451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282121471/10000000000 : ℝ)*X 1 0+(-999815049/5000000000 : ℝ)*X 1 1+(5519500997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282121701/10000000000 : ℝ)*X 2 0+(5519500849/10000000000 : ℝ)*X 2 1+(-1999629989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436108737/1000000000 : ℝ)*X 0 0+(1184482593/2500000000 : ℝ)*X 0 1+(4014818939/10000000000 : ℝ)*X 0 2+(436108737/1000000000 : ℝ)*X 1 0+(1184482593/2500000000 : ℝ)*X 1 1+(4014818939/10000000000 : ℝ)*X 1 2+(436108737/1000000000 : ℝ)*X 2 0+(1184482593/2500000000 : ℝ)*X 2 1+(4014818939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2558732176189560461089779/278750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4916271/10000000000000 : ℝ)*(base1) + (838203621/50000000000000 : ℝ)*(base19) + (437176727/25000000000000 : ℝ)*(base23) + (35068743/20000000000000 : ℝ)*(upper3) + (89825821/50000000000000 : ℝ)*(upper5) + (25273366099023/1250000000000 : ℝ)*(major0) + (25273366099023/1250000000000 : ℝ)*(major1) + (25273366099023/1250000000000 : ℝ)*(major2) + (1340375876533343/50000000000000 : ℝ)*(sp0) + (2680770455332379/100000000000000 : ℝ)*(sp1) + (1340385191516357/50000000000000 : ℝ)*(sp2) + (681478376246231/50000000000000 : ℝ)*(sp3) + (4085567129/20000000000000 : ℝ)*(sp4) + (9336471933/100000000000000 : ℝ)*(sp7) + (5324086477059/390625000000 : ℝ)*(f.failure) + (2680772131739621/100000000000000 : ℝ)*(f.sum) + (8133168817089/2564500000000000000000000000 : ℝ)*base65 + (116220413081412787/12822500000000000000000000000000 : ℝ)*base67 + (90306984584007787/12822500000000000000000000000000 : ℝ)*base69 + (136998831096055287/12822500000000000000000000000000 : ℝ)*base71 + (4254291775577/5129000000000000000000000000 : ℝ)*base74 + (96592242660850287/12822500000000000000000000000000 : ℝ)*base75 + (56471918025555287/12822500000000000000000000000000 : ℝ)*base77 + (51629697392545287/12822500000000000000000000000000 : ℝ)*base79 + (24476126626057/5129000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (18753/1562500000000000000 : ℝ)*base90 + (18753/1562500000000000000 : ℝ)*base92 + (18753/1562500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27548045720838430345500153/5575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240689517/25000000000000 : ℝ)*(base19) + (584128987/50000000000000 : ℝ)*(base23) + (1818639/1250000000000 : ℝ)*(upper3) + (25346283/100000000000000 : ℝ)*(lower4) + (2346153/2500000000000 : ℝ)*(upper5) + (512864890188561/25000000000000 : ℝ)*(major0) + (512864890188561/25000000000000 : ℝ)*(major1) + (512864890188561/25000000000000 : ℝ)*(major2) + (1683454389/20000000000000 : ℝ)*(sp1) + (1060673291/10000000000000 : ℝ)*(sp2) + (68000141594057/2500000000000 : ℝ)*(sp4) + (1359998141866133/50000000000000 : ℝ)*(sp5) + (679998472192849/25000000000000 : ℝ)*(sp6) + (691456646517207/50000000000000 : ℝ)*(sp7) + (691456646517207/50000000000000 : ℝ)*(f.failure) + (68000141594057/2500000000000 : ℝ)*(f.sum) + (8007752655017/1282250000000000000000000000 : ℝ)*base65 + (1050097643632599609/256450000000000000000000000000000 : ℝ)*base67 + (19100474606499609/256450000000000000000000000000000 : ℝ)*base69 + (2985785303593999609/256450000000000000000000000000000 : ℝ)*base71 + (8131001142397/5129000000000000000000000000 : ℝ)*base74 + (4336094962231849609/256450000000000000000000000000000 : ℝ)*base75 + (573759807838499609/256450000000000000000000000000000 : ℝ)*base77 + (3001902651139299609/256450000000000000000000000000000 : ℝ)*base79 + (194256343953/256450000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1756269/200000000000000000000 : ℝ)*base90 + (1756269/200000000000000000000 : ℝ)*base92 + (1756269/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1084_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4141/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1084_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1084_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1084_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1084_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8341/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

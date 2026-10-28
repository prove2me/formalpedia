-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:54:43.606505+00:00
-- url     : https://prove2.me/submissions/e8ff68c7-3bf1-472a-8ebf-7c3d143bf90f

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
theorem support_rectangle_w1050_s9_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-552918351/2500000000 : ℝ)*x 0 + (1348652581/2500000000 : ℝ)*x 1 + (210567131/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552918351/2500000000 : ℝ)^8243 ≤ (13430520482307/100000000000000 : ℝ)^6195 := by
    have hnat : (552918351 : ℕ)^8243*100000000000000^6195 ≤ 13430520482307^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552918351 2500000000 13430520482307 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348652581/2500000000 : ℝ)^8243 ≤ (8797899080307/20000000000000 : ℝ)^6195 := by
    have hnat : (1348652581 : ℕ)^8243*20000000000000^6195 ≤ 8797899080307^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348652581 2500000000 8797899080307 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210567131/400000000 : ℝ)^8243 ≤ (2661249006447/6250000000000 : ℝ)^6195 := by
    have hnat : (210567131 : ℕ)^8243*6250000000000^6195 ≤ 2661249006447^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210567131 400000000 2661249006447 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552918351/2500000000 : ℝ), (1348652581/2500000000 : ℝ), (210567131/400000000 : ℝ)] ![(13430520482307/100000000000000 : ℝ), (8797899080307/20000000000000 : ℝ), (2661249006447/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552918351/2500000000 : ℝ)|^8243 ≤ (13430520482307/100000000000000 : ℝ)^6195
        have hw : |(-552918351/2500000000 : ℝ)|=(552918351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348652581/2500000000 : ℝ)|^8243 ≤ (8797899080307/20000000000000 : ℝ)^6195
        have hw : |(1348652581/2500000000 : ℝ)|=(1348652581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210567131/400000000 : ℝ)|^8243 ≤ (2661249006447/6250000000000 : ℝ)^6195
        have hw : |(210567131/400000000 : ℝ)|=(210567131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336251847/2500000000 : ℝ)*x 0 + (-2277854453/10000000000 : ℝ)*x 1 + (5264178291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336251847/2500000000 : ℝ)^8243 ≤ (2715757456953/6250000000000 : ℝ)^6195 := by
    have hnat : (1336251847 : ℕ)^8243*6250000000000^6195 ≤ 2715757456953^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336251847 2500000000 2715757456953 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277854453/10000000000 : ℝ)^8243 ≤ (558715855869/4000000000000 : ℝ)^6195 := by
    have hnat : (2277854453 : ℕ)^8243*4000000000000^6195 ≤ 558715855869^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277854453 10000000000 558715855869 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264178291/10000000000 : ℝ)^8243 ≤ (21289992137677/50000000000000 : ℝ)^6195 := by
    have hnat : (5264178291 : ℕ)^8243*50000000000000^6195 ≤ 21289992137677^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264178291 10000000000 21289992137677 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336251847/2500000000 : ℝ), (-2277854453/10000000000 : ℝ), (5264178291/10000000000 : ℝ)] ![(2715757456953/6250000000000 : ℝ), (558715855869/4000000000000 : ℝ), (21289992137677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336251847/2500000000 : ℝ)|^8243 ≤ (2715757456953/6250000000000 : ℝ)^6195
        have hw : |(1336251847/2500000000 : ℝ)|=(1336251847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2277854453/10000000000 : ℝ)|^8243 ≤ (558715855869/4000000000000 : ℝ)^6195
        have hw : |(-2277854453/10000000000 : ℝ)|=(2277854453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264178291/10000000000 : ℝ)|^8243 ≤ (21289992137677/50000000000000 : ℝ)^6195
        have hw : |(5264178291/10000000000 : ℝ)|=(5264178291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4175787/7812500 : ℝ)*x 0 + (41126393/78125000 : ℝ)*x 1 + (-2277854473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175787/7812500 : ℝ)^8243 ≤ (10863029752093/25000000000000 : ℝ)^6195 := by
    have hnat : (4175787 : ℕ)^8243*25000000000000^6195 ≤ 10863029752093^6195*7812500^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175787 7812500 10863029752093 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41126393/78125000 : ℝ)^8243 ≤ (10644996103817/25000000000000 : ℝ)^6195 := by
    have hnat : (41126393 : ℕ)^8243*25000000000000^6195 ≤ 10644996103817^6195*78125000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41126393 78125000 10644996103817 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277854473/10000000000 : ℝ)^8243 ≤ (1396789655991/10000000000000 : ℝ)^6195 := by
    have hnat : (2277854473 : ℕ)^8243*10000000000000^6195 ≤ 1396789655991^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277854473 10000000000 1396789655991 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175787/7812500 : ℝ), (41126393/78125000 : ℝ), (-2277854473/10000000000 : ℝ)] ![(10863029752093/25000000000000 : ℝ), (10644996103817/25000000000000 : ℝ), (1396789655991/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175787/7812500 : ℝ)|^8243 ≤ (10863029752093/25000000000000 : ℝ)^6195
        have hw : |(4175787/7812500 : ℝ)|=(4175787/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41126393/78125000 : ℝ)|^8243 ≤ (10644996103817/25000000000000 : ℝ)^6195
        have hw : |(41126393/78125000 : ℝ)|=(41126393/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2277854473/10000000000 : ℝ)|^8243 ≤ (1396789655991/10000000000000 : ℝ)^6195
        have hw : |(-2277854473/10000000000 : ℝ)|=(2277854473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377799593/10000000000 : ℝ)*x 0 + (2126138267/5000000000 : ℝ)*x 1 + (2253546729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377799593/10000000000 : ℝ)^8243 ≤ (6663293525959/20000000000000 : ℝ)^6195 := by
    have hnat : (4377799593 : ℕ)^8243*20000000000000^6195 ≤ 6663293525959^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377799593 10000000000 6663293525959 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126138267/5000000000 : ℝ)^8243 ≤ (32051457563357/100000000000000 : ℝ)^6195 := by
    have hnat : (2126138267 : ℕ)^8243*100000000000000^6195 ≤ 32051457563357^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126138267 5000000000 32051457563357 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253546729/5000000000 : ℝ)^8243 ≤ (8658018697313/25000000000000 : ℝ)^6195 := by
    have hnat : (2253546729 : ℕ)^8243*25000000000000^6195 ≤ 8658018697313^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253546729 5000000000 8658018697313 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377799593/10000000000 : ℝ), (2126138267/5000000000 : ℝ), (2253546729/5000000000 : ℝ)] ![(6663293525959/20000000000000 : ℝ), (32051457563357/100000000000000 : ℝ), (8658018697313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377799593/10000000000 : ℝ)|^8243 ≤ (6663293525959/20000000000000 : ℝ)^6195
        have hw : |(4377799593/10000000000 : ℝ)|=(4377799593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126138267/5000000000 : ℝ)|^8243 ≤ (32051457563357/100000000000000 : ℝ)^6195
        have hw : |(2126138267/5000000000 : ℝ)|=(2126138267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253546729/5000000000 : ℝ)|^8243 ≤ (8658018697313/25000000000000 : ℝ)^6195
        have hw : |(2253546729/5000000000 : ℝ)|=(2253546729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211677663/10000000000 : ℝ)*x 0 + (2632251831/5000000000 : ℝ)*x 1 + (5394284381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211677663/10000000000 : ℝ)^8243 ≤ (13430554895393/100000000000000 : ℝ)^6195 := by
    have hnat : (2211677663 : ℕ)^8243*100000000000000^6195 ≤ 13430554895393^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211677663 10000000000 13430554895393 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632251831/5000000000 : ℝ)^8243 ≤ (42583486162733/100000000000000 : ℝ)^6195 := by
    have hnat : (2632251831 : ℕ)^8243*100000000000000^6195 ≤ 42583486162733^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632251831 5000000000 42583486162733 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394284381/10000000000 : ℝ)^8243 ≤ (43985958929637/100000000000000 : ℝ)^6195 := by
    have hnat : (5394284381 : ℕ)^8243*100000000000000^6195 ≤ 43985958929637^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394284381 10000000000 43985958929637 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211677663/10000000000 : ℝ), (2632251831/5000000000 : ℝ), (5394284381/10000000000 : ℝ)] ![(13430554895393/100000000000000 : ℝ), (42583486162733/100000000000000 : ℝ), (43985958929637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211677663/10000000000 : ℝ)|^8243 ≤ (13430554895393/100000000000000 : ℝ)^6195
        have hw : |(-2211677663/10000000000 : ℝ)|=(2211677663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632251831/5000000000 : ℝ)|^8243 ≤ (42583486162733/100000000000000 : ℝ)^6195
        have hw : |(2632251831/5000000000 : ℝ)|=(2632251831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394284381/10000000000 : ℝ)|^8243 ≤ (43985958929637/100000000000000 : ℝ)^6195
        have hw : |(5394284381/10000000000 : ℝ)|=(5394284381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332012709/625000000 : ℝ)*x 0 + (-1073875041/5000000000 : ℝ)*x 1 + (2697137769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332012709/625000000 : ℝ)^8243 ≤ (8619527717777/20000000000000 : ℝ)^6195 := by
    have hnat : (332012709 : ℕ)^8243*20000000000000^6195 ≤ 8619527717777^6195*625000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332012709 625000000 8619527717777 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073875041/5000000000 : ℝ)^8243 ≤ (2583299682217/20000000000000 : ℝ)^6195 := by
    have hnat : (1073875041 : ℕ)^8243*20000000000000^6195 ≤ 2583299682217^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073875041 5000000000 2583299682217 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697137769/5000000000 : ℝ)^8243 ≤ (21992931492167/50000000000000 : ℝ)^6195 := by
    have hnat : (2697137769 : ℕ)^8243*50000000000000^6195 ≤ 21992931492167^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697137769 5000000000 21992931492167 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332012709/625000000 : ℝ), (-1073875041/5000000000 : ℝ), (2697137769/5000000000 : ℝ)] ![(8619527717777/20000000000000 : ℝ), (2583299682217/20000000000000 : ℝ), (21992931492167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332012709/625000000 : ℝ)|^8243 ≤ (8619527717777/20000000000000 : ℝ)^6195
        have hw : |(332012709/625000000 : ℝ)|=(332012709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073875041/5000000000 : ℝ)|^8243 ≤ (2583299682217/20000000000000 : ℝ)^6195
        have hw : |(-1073875041/5000000000 : ℝ)|=(1073875041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697137769/5000000000 : ℝ)|^8243 ≤ (21992931492167/50000000000000 : ℝ)^6195
        have hw : |(2697137769/5000000000 : ℝ)|=(2697137769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312191197/10000000000 : ℝ)*x 0 + (215771403/400000000 : ℝ)*x 1 + (-2147753537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312191197/10000000000 : ℝ)^8243 ≤ (2693594216377/6250000000000 : ℝ)^6195 := by
    have hnat : (5312191197 : ℕ)^8243*6250000000000^6195 ≤ 2693594216377^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312191197 10000000000 2693594216377 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215771403/400000000 : ℝ)^8243 ≤ (21992983229721/50000000000000 : ℝ)^6195 := by
    have hnat : (215771403 : ℕ)^8243*50000000000000^6195 ≤ 21992983229721^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215771403 400000000 21992983229721 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147753537/10000000000 : ℝ)^8243 ≤ (807282878651/6250000000000 : ℝ)^6195 := by
    have hnat : (2147753537 : ℕ)^8243*6250000000000^6195 ≤ 807282878651^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147753537 10000000000 807282878651 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312191197/10000000000 : ℝ), (215771403/400000000 : ℝ), (-2147753537/10000000000 : ℝ)] ![(2693594216377/6250000000000 : ℝ), (21992983229721/50000000000000 : ℝ), (807282878651/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312191197/10000000000 : ℝ)|^8243 ≤ (2693594216377/6250000000000 : ℝ)^6195
        have hw : |(5312191197/10000000000 : ℝ)|=(5312191197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215771403/400000000 : ℝ)|^8243 ≤ (21992983229721/50000000000000 : ℝ)^6195
        have hw : |(215771403/400000000 : ℝ)|=(215771403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147753537/10000000000 : ℝ)|^8243 ≤ (807282878651/6250000000000 : ℝ)^6195
        have hw : |(-2147753537/10000000000 : ℝ)|=(2147753537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094453213/2500000000 : ℝ)*x 0 + (2253228587/5000000000 : ℝ)*x 1 + (53161397/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094453213/2500000000 : ℝ)^8243 ≤ (16658300946661/50000000000000 : ℝ)^6195 := by
    have hnat : (1094453213 : ℕ)^8243*50000000000000^6195 ≤ 16658300946661^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094453213 2500000000 16658300946661 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253228587/5000000000 : ℝ)^8243 ≤ (17312784748561/50000000000000 : ℝ)^6195 := by
    have hnat : (2253228587 : ℕ)^8243*50000000000000^6195 ≤ 17312784748561^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253228587 5000000000 17312784748561 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53161397/125000000 : ℝ)^8243 ≤ (32057828587669/100000000000000 : ℝ)^6195 := by
    have hnat : (53161397 : ℕ)^8243*100000000000000^6195 ≤ 32057828587669^6195*125000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53161397 125000000 32057828587669 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094453213/2500000000 : ℝ), (2253228587/5000000000 : ℝ), (53161397/125000000 : ℝ)] ![(16658300946661/50000000000000 : ℝ), (17312784748561/50000000000000 : ℝ), (32057828587669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094453213/2500000000 : ℝ)|^8243 ≤ (16658300946661/50000000000000 : ℝ)^6195
        have hw : |(1094453213/2500000000 : ℝ)|=(1094453213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253228587/5000000000 : ℝ)|^8243 ≤ (17312784748561/50000000000000 : ℝ)^6195
        have hw : |(2253228587/5000000000 : ℝ)|=(2253228587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53161397/125000000 : ℝ)|^8243 ≤ (32057828587669/100000000000000 : ℝ)^6195
        have hw : |(53161397/125000000 : ℝ)|=(53161397/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_8 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-516995619/5000000000 : ℝ)*x 0 + (5720443757/10000000000 : ℝ)*x 1 + (5720195933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516995619/5000000000 : ℝ)^8243 ≤ (4883450502797/100000000000000 : ℝ)^6195 := by
    have hnat : (516995619 : ℕ)^8243*100000000000000^6195 ≤ 4883450502797^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516995619 5000000000 4883450502797 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720443757/10000000000 : ℝ)^8243 ≤ (47559645507123/100000000000000 : ℝ)^6195 := by
    have hnat : (5720443757 : ℕ)^8243*100000000000000^6195 ≤ 47559645507123^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720443757 10000000000 47559645507123 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5720195933/10000000000 : ℝ)^8243 ≤ (47556903976317/100000000000000 : ℝ)^6195 := by
    have hnat : (5720195933 : ℕ)^8243*100000000000000^6195 ≤ 47556903976317^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720195933 10000000000 47556903976317 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516995619/5000000000 : ℝ), (5720443757/10000000000 : ℝ), (5720195933/10000000000 : ℝ)] ![(4883450502797/100000000000000 : ℝ), (47559645507123/100000000000000 : ℝ), (47556903976317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516995619/5000000000 : ℝ)|^8243 ≤ (4883450502797/100000000000000 : ℝ)^6195
        have hw : |(-516995619/5000000000 : ℝ)|=(516995619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720443757/10000000000 : ℝ)|^8243 ≤ (47559645507123/100000000000000 : ℝ)^6195
        have hw : |(5720443757/10000000000 : ℝ)|=(5720443757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5720195933/10000000000 : ℝ)|^8243 ≤ (47556903976317/100000000000000 : ℝ)^6195
        have hw : |(5720195933/10000000000 : ℝ)|=(5720195933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_9 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (162954851/500000000 : ℝ)*x 0 + (-2868764243/10000000000 : ℝ)*x 1 + (2611343/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162954851/500000000 : ℝ)^8243 ≤ (22497409781549/100000000000000 : ℝ)^6195 := by
    have hnat : (162954851 : ℕ)^8243*100000000000000^6195 ≤ 22497409781549^6195*500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162954851 500000000 22497409781549 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2868764243/10000000000 : ℝ)^8243 ≤ (9492588372963/50000000000000 : ℝ)^6195 := by
    have hnat : (2868764243 : ℕ)^8243*50000000000000^6195 ≤ 9492588372963^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868764243 10000000000 9492588372963 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611343/3906250 : ℝ)^8243 ≤ (14629353365309/25000000000000 : ℝ)^6195 := by
    have hnat : (2611343 : ℕ)^8243*25000000000000^6195 ≤ 14629353365309^6195*3906250^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611343 3906250 14629353365309 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162954851/500000000 : ℝ), (-2868764243/10000000000 : ℝ), (2611343/3906250 : ℝ)] ![(22497409781549/100000000000000 : ℝ), (9492588372963/50000000000000 : ℝ), (14629353365309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162954851/500000000 : ℝ)|^8243 ≤ (22497409781549/100000000000000 : ℝ)^6195
        have hw : |(162954851/500000000 : ℝ)|=(162954851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2868764243/10000000000 : ℝ)|^8243 ≤ (9492588372963/50000000000000 : ℝ)^6195
        have hw : |(-2868764243/10000000000 : ℝ)|=(2868764243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611343/3906250 : ℝ)|^8243 ≤ (14629353365309/25000000000000 : ℝ)^6195
        have hw : |(2611343/3906250 : ℝ)|=(2611343/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_10 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (766224729/2000000000 : ℝ)*x 0 + (6151886349/10000000000 : ℝ)*x 1 + (-2950766991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766224729/2000000000 : ℝ)^8243 ≤ (27898336371391/100000000000000 : ℝ)^6195 := by
    have hnat : (766224729 : ℕ)^8243*100000000000000^6195 ≤ 27898336371391^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766224729 2000000000 27898336371391 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6151886349/10000000000 : ℝ)^8243 ≤ (52391005153243/100000000000000 : ℝ)^6195 := by
    have hnat : (6151886349 : ℕ)^8243*100000000000000^6195 ≤ 52391005153243^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6151886349 10000000000 52391005153243 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950766991/10000000000 : ℝ)^8243 ≤ (788426338413/4000000000000 : ℝ)^6195 := by
    have hnat : (2950766991 : ℕ)^8243*4000000000000^6195 ≤ 788426338413^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950766991 10000000000 788426338413 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(766224729/2000000000 : ℝ), (6151886349/10000000000 : ℝ), (-2950766991/10000000000 : ℝ)] ![(27898336371391/100000000000000 : ℝ), (52391005153243/100000000000000 : ℝ), (788426338413/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(766224729/2000000000 : ℝ)|^8243 ≤ (27898336371391/100000000000000 : ℝ)^6195
        have hw : |(766224729/2000000000 : ℝ)|=(766224729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6151886349/10000000000 : ℝ)|^8243 ≤ (52391005153243/100000000000000 : ℝ)^6195
        have hw : |(6151886349/10000000000 : ℝ)|=(6151886349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2950766991/10000000000 : ℝ)|^8243 ≤ (788426338413/4000000000000 : ℝ)^6195
        have hw : |(-2950766991/10000000000 : ℝ)|=(2950766991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s9_11 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1621370189/5000000000 : ℝ)*x 0 + (491144401/1000000000 : ℝ)*x 1 + (491144867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621370189/5000000000 : ℝ)^8243 ≤ (1396706173519/6250000000000 : ℝ)^6195 := by
    have hnat : (1621370189 : ℕ)^8243*6250000000000^6195 ≤ 1396706173519^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621370189 5000000000 1396706173519 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491144401/1000000000 : ℝ)^8243 ≤ (38826326098031/100000000000000 : ℝ)^6195 := by
    have hnat : (491144401 : ℕ)^8243*100000000000000^6195 ≤ 38826326098031^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491144401 1000000000 38826326098031 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491144867/1000000000 : ℝ)^8243 ≤ (3882637511507/10000000000000 : ℝ)^6195 := by
    have hnat : (491144867 : ℕ)^8243*10000000000000^6195 ≤ 3882637511507^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491144867 1000000000 3882637511507 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1621370189/5000000000 : ℝ), (491144401/1000000000 : ℝ), (491144867/1000000000 : ℝ)] ![(1396706173519/6250000000000 : ℝ), (38826326098031/100000000000000 : ℝ), (3882637511507/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1621370189/5000000000 : ℝ)|^8243 ≤ (1396706173519/6250000000000 : ℝ)^6195
        have hw : |(1621370189/5000000000 : ℝ)|=(1621370189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(491144401/1000000000 : ℝ)|^8243 ≤ (38826326098031/100000000000000 : ℝ)^6195
        have hw : |(491144401/1000000000 : ℝ)|=(491144401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(491144867/1000000000 : ℝ)|^8243 ≤ (3882637511507/10000000000000 : ℝ)^6195
        have hw : |(491144867/1000000000 : ℝ)|=(491144867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1123/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1749/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11229/100000 : ℝ) ^ (4121/1024 : ℝ) ≤ (7536145928992381/50000000000000000000 : ℝ) := by
    have hpowers : (11229/100000 : ℝ)^4121 ≤ (7536145928992381/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11229 : ℕ)^4121*50000000000000000000^1024 ≤ 7536145928992381^1024*100000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11229 100000 7536145928992381 50000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11229/100000 : ℝ)) (X := (7536145928992381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13993/100000 : ℝ) ^ (4121/1024 : ℝ) ≤ (36541935798727023/100000000000000000000 : ℝ) := by
    have hpowers : (13993/100000 : ℝ)^4121 ≤ (36541935798727023/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13993 : ℕ)^4121*100000000000000000000^1024 ≤ 36541935798727023^1024*100000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13993 100000 36541935798727023 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13993/100000 : ℝ)) (X := (36541935798727023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007536145928992381/25000000000000000000 : ℝ) ≤ (1250093619746093/1250000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (25007536145928992381/25000000000000000000 : ℝ)^1024 ≤ (1250093619746093/1250000000000000 : ℝ)^4121 := by
      have hnat : (25007536145928992381 : ℕ)^1024*1250000000000000^4121 ≤ 1250093619746093^4121*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007536145928992381 25000000000000000000 1250093619746093 1250000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250093619746093/1250000000000000 : ℝ)) (X := (25007536145928992381/25000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010322845531342357/20000000000000000000 : ℝ) ≤ (10001282279098579/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (20010322845531342357/20000000000000000000 : ℝ)^1024 ≤ (10001282279098579/10000000000000000 : ℝ)^4121 := by
      have hnat : (20010322845531342357 : ℕ)^1024*10000000000000000^4121 ≤ 10001282279098579^4121*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010322845531342357 20000000000000000000 10001282279098579 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001282279098579/10000000000000000 : ℝ)) (X := (20010322845531342357/20000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036541935798727023/50000000000000000000 : ℝ) ≤ (5000907800114207/5000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50036541935798727023/50000000000000000000 : ℝ)^1024 ≤ (5000907800114207/5000000000000000 : ℝ)^4121 := by
      have hnat : (50036541935798727023 : ℕ)^1024*5000000000000000^4121 ≤ 5000907800114207^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036541935798727023 50000000000000000000 5000907800114207 5000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000907800114207/5000000000000000 : ℝ)) (X := (50036541935798727023/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7536145928992381/50000000000000000000 : ℝ) ≤ ((13815046396945886993/13820000000000000000 : ℝ)+2*(106664225967/55280000000000 : ℝ)*(11229/100000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (13815046396945886993/13820000000000000000 : ℝ)+2*(106664225967/55280000000000 : ℝ)*(11229/100000 : ℝ)=(1250093619746093/1250000000000000 : ℝ) by norm_num, show 1+2*(7536145928992381/50000000000000000000 : ℝ)=(25007536145928992381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36541935798727023/100000000000000000000 : ℝ)+(7536145928992381/50000000000000000000 : ℝ) ≤ ((13815046396945886993/13820000000000000000 : ℝ)+(106664225967/55280000000000 : ℝ)*((13993/100000 : ℝ)+(11229/100000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (13815046396945886993/13820000000000000000 : ℝ)+(106664225967/55280000000000 : ℝ)*((13993/100000 : ℝ)+(11229/100000 : ℝ))=(10001282279098579/10000000000000000 : ℝ) by norm_num, show 1+(36541935798727023/100000000000000000000 : ℝ)+(7536145928992381/50000000000000000000 : ℝ)=(20010322845531342357/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36541935798727023/100000000000000000000 : ℝ) ≤ ((13815046396945886993/13820000000000000000 : ℝ)+2*(106664225967/55280000000000 : ℝ)*(13993/100000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (13815046396945886993/13820000000000000000 : ℝ)+2*(106664225967/55280000000000 : ℝ)*(13993/100000 : ℝ)=(5000907800114207/5000000000000000 : ℝ) by norm_num, show 1+2*(36541935798727023/100000000000000000000 : ℝ)=(50036541935798727023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13815046396945886993/13820000000000000000 : ℝ)*(X 1 0+X 2 0)+(106664225967/55280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (13815046396945886993/13820000000000000000 : ℝ)) (alpha := (106664225967/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13815046396945886993/13820000000000000000 : ℝ)*(X 0 1+X 2 1)+(106664225967/55280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (13815046396945886993/13820000000000000000 : ℝ)) (alpha := (106664225967/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13815046396945886993/13820000000000000000 : ℝ)*(X 0 2+X 1 2)+(106664225967/55280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (13815046396945886993/13820000000000000000 : ℝ)) (alpha := (106664225967/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552918351/2500000000 : ℝ)*X 0 0+(1348652581/2500000000 : ℝ)*X 0 1+(210567131/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336251847/2500000000 : ℝ)*X 1 0+(-2277854453/10000000000 : ℝ)*X 1 1+(5264178291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4175787/7812500 : ℝ)*X 2 0+(41126393/78125000 : ℝ)*X 2 1+(-2277854473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377799593/10000000000 : ℝ)*X 0 0+(2126138267/5000000000 : ℝ)*X 0 1+(2253546729/5000000000 : ℝ)*X 0 2+(4377799593/10000000000 : ℝ)*X 1 0+(2126138267/5000000000 : ℝ)*X 1 1+(2253546729/5000000000 : ℝ)*X 1 2+(4377799593/10000000000 : ℝ)*X 2 0+(2126138267/5000000000 : ℝ)*X 2 1+(2253546729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2211677663/10000000000 : ℝ)*X 0 0+(2632251831/5000000000 : ℝ)*X 0 1+(5394284381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332012709/625000000 : ℝ)*X 1 0+(-1073875041/5000000000 : ℝ)*X 1 1+(2697137769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312191197/10000000000 : ℝ)*X 2 0+(215771403/400000000 : ℝ)*X 2 1+(-2147753537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094453213/2500000000 : ℝ)*X 0 0+(2253228587/5000000000 : ℝ)*X 0 1+(53161397/125000000 : ℝ)*X 0 2+(1094453213/2500000000 : ℝ)*X 1 0+(2253228587/5000000000 : ℝ)*X 1 1+(53161397/125000000 : ℝ)*X 1 2+(1094453213/2500000000 : ℝ)*X 2 0+(2253228587/5000000000 : ℝ)*X 2 1+(53161397/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-516995619/5000000000 : ℝ)*X 0 0+(5720443757/10000000000 : ℝ)*X 0 1+(5720195933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((162954851/500000000 : ℝ)*X 1 0+(-2868764243/10000000000 : ℝ)*X 1 1+(2611343/3906250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((766224729/2000000000 : ℝ)*X 2 0+(6151886349/10000000000 : ℝ)*X 2 1+(-2950766991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1621370189/5000000000 : ℝ)*X 0 0+(491144401/1000000000 : ℝ)*X 0 1+(491144867/1000000000 : ℝ)*X 0 2+(1621370189/5000000000 : ℝ)*X 1 0+(491144401/1000000000 : ℝ)*X 1 1+(491144867/1000000000 : ℝ)*X 1 2+(1621370189/5000000000 : ℝ)*X 2 0+(491144401/1000000000 : ℝ)*X 2 1+(491144867/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s9_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13678023462326363447127/2764000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118631247/100000000000000 : ℝ)*(lower4) + (1159122362407599/20000000000000 : ℝ)*(major0) + (1159122362407599/20000000000000 : ℝ)*(major1) + (1159122362407599/20000000000000 : ℝ)*(major2) + (7666832742932559/100000000000000 : ℝ)*(sp0) + (7666833865982393/100000000000000 : ℝ)*(sp1) + (7666832058805527/100000000000000 : ℝ)*(sp2) + (196219420573941/5000000000000 : ℝ)*(sp3) + (207055291/20000000000000 : ℝ)*(sp6) + (3063887/6250000000000 : ℝ)*(sp7) + (152670261/10000000000000 : ℝ)*(sp8) + (50456597/12500000000000 : ℝ)*(sp9) + (1175553187/100000000000000 : ℝ)*(sp10) + (728985343/100000000000000 : ℝ)*(sp11) + (1962194594743177/50000000000000 : ℝ)*(f.failure) + (7666834269635169/100000000000000 : ℝ)*(f.sum) + (12387578232083/2764000000000000000000000000 : ℝ)*base66 + (1425455915921109807/276400000000000000000000000000000 : ℝ)*base67 + (2465956616011290193/276400000000000000000000000000000 : ℝ)*base70 + (634826734913909807/276400000000000000000000000000000 : ℝ)*base71 + (1271064982279/2764000000000000000000000000 : ℝ)*base74 + (1851270542134490193/276400000000000000000000000000000 : ℝ)*base76 + (2246900722311509807/276400000000000000000000000000000 : ℝ)*base77 + (159862461922890193/276400000000000000000000000000000 : ℝ)*base80 + (7786670133777/2764000000000000000000000000 : ℝ)*base81 + (31990443/2500000000000000000000 : ℝ)*base90 + (31990443/2500000000000000000000 : ℝ)*base92 + (31990443/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87727298028670905250033479/691000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5751757217/100000000000000 : ℝ)*(upper1) + (3444125749/100000000000000 : ℝ)*(upper2) + (1113218627/25000000000000 : ℝ)*(lower4) + (5824785335577501/100000000000000 : ℝ)*(major0) + (5824785335577501/100000000000000 : ℝ)*(major1) + (5824785335577501/100000000000000 : ℝ)*(major2) + (1271384943/4000000000000 : ℝ)*(sp0) + (65681943563/50000000000000 : ℝ)*(sp2) + (3852697695890747/50000000000000 : ℝ)*(sp4) + (963177768919341/12500000000000 : ℝ)*(sp5) + (3852647906258971/50000000000000 : ℝ)*(sp6) + (394413534108343/10000000000000 : ℝ)*(sp7) + (5025050341/100000000000000 : ℝ)*(sp9) + (2037358647/25000000000000 : ℝ)*(sp11) + (3944143490518019/100000000000000 : ℝ)*(f.failure) + (1926356794101267/25000000000000 : ℝ)*(f.sum) + (46327438599739/2764000000000000000000000000 : ℝ)*base65 + (20458980500239905507/1382000000000000000000000000000000 : ℝ)*base68 + (23095075116361905507/1382000000000000000000000000000000 : ℝ)*base70 + (28758093115824094493/1382000000000000000000000000000000 : ℝ)*base71 + (12146622378743/2764000000000000000000000000 : ℝ)*base73 + (29861555252471905507/1382000000000000000000000000000000 : ℝ)*base76 + (2968163135300094493/1382000000000000000000000000000000 : ℝ)*base77 + (4536696785371905507/1382000000000000000000000000000000 : ℝ)*base80 + (2254803751769/552800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (50415879/5000000000000000000000 : ℝ)*base89 + (50415879/5000000000000000000000 : ℝ)*base91 + (50415879/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1050_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1050_box_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-416332729/2000000000 : ℝ)*x 0 + (5377580737/10000000000 : ℝ)*x 1 + (5377579417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416332729/2000000000 : ℝ)^8243 ≤ (3097593812391/25000000000000 : ℝ)^6195 := by
    have hnat : (416332729 : ℕ)^8243*25000000000000^6195 ≤ 3097593812391^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416332729 2000000000 3097593812391 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377580737/10000000000 : ℝ)^8243 ≤ (43804819523459/100000000000000 : ℝ)^6195 := by
    have hnat : (5377580737 : ℕ)^8243*100000000000000^6195 ≤ 43804819523459^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377580737 10000000000 43804819523459 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377579417/10000000000 : ℝ)^8243 ≤ (21902402608159/50000000000000 : ℝ)^6195 := by
    have hnat : (5377579417 : ℕ)^8243*50000000000000^6195 ≤ 21902402608159^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377579417 10000000000 21902402608159 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416332729/2000000000 : ℝ), (5377580737/10000000000 : ℝ), (5377579417/10000000000 : ℝ)] ![(3097593812391/25000000000000 : ℝ), (43804819523459/100000000000000 : ℝ), (21902402608159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416332729/2000000000 : ℝ)|^8243 ≤ (3097593812391/25000000000000 : ℝ)^6195
        have hw : |(-416332729/2000000000 : ℝ)|=(416332729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377580737/10000000000 : ℝ)|^8243 ≤ (43804819523459/100000000000000 : ℝ)^6195
        have hw : |(5377580737/10000000000 : ℝ)|=(5377580737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377579417/10000000000 : ℝ)|^8243 ≤ (21902402608159/50000000000000 : ℝ)^6195
        have hw : |(5377579417/10000000000 : ℝ)|=(5377579417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295021451/10000000000 : ℝ)*x 0 + (-2193382251/10000000000 : ℝ)*x 1 + (5377580033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295021451/10000000000 : ℝ)^8243 ≤ (21456129617197/50000000000000 : ℝ)^6195 := by
    have hnat : (5295021451 : ℕ)^8243*50000000000000^6195 ≤ 21456129617197^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295021451 10000000000 21456129617197 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193382251/10000000000 : ℝ)^8243 ≤ (6641464428029/50000000000000 : ℝ)^6195 := by
    have hnat : (2193382251 : ℕ)^8243*50000000000000^6195 ≤ 6641464428029^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193382251 10000000000 6641464428029 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377580033/10000000000 : ℝ)^8243 ≤ (5475601486623/12500000000000 : ℝ)^6195 := by
    have hnat : (5377580033 : ℕ)^8243*12500000000000^6195 ≤ 5475601486623^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377580033 10000000000 5475601486623 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295021451/10000000000 : ℝ), (-2193382251/10000000000 : ℝ), (5377580033/10000000000 : ℝ)] ![(21456129617197/50000000000000 : ℝ), (6641464428029/50000000000000 : ℝ), (5475601486623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295021451/10000000000 : ℝ)|^8243 ≤ (21456129617197/50000000000000 : ℝ)^6195
        have hw : |(5295021451/10000000000 : ℝ)|=(5295021451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193382251/10000000000 : ℝ)|^8243 ≤ (6641464428029/50000000000000 : ℝ)^6195
        have hw : |(-2193382251/10000000000 : ℝ)|=(2193382251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377580033/10000000000 : ℝ)|^8243 ≤ (5475601486623/12500000000000 : ℝ)^6195
        have hw : |(5377580033/10000000000 : ℝ)|=(5377580033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165469389/312500000 : ℝ)*x 0 + (537758029/1000000000 : ℝ)*x 1 + (-137086453/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165469389/312500000 : ℝ)^8243 ≤ (10728062104649/25000000000000 : ℝ)^6195 := by
    have hnat : (165469389 : ℕ)^8243*25000000000000^6195 ≤ 10728062104649^6195*312500000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165469389 312500000 10728062104649 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537758029/1000000000 : ℝ)^8243 ≤ (43804814678541/100000000000000 : ℝ)^6195 := by
    have hnat : (537758029 : ℕ)^8243*100000000000000^6195 ≤ 43804814678541^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537758029 1000000000 43804814678541 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137086453/625000000 : ℝ)^8243 ≤ (2656587377963/20000000000000 : ℝ)^6195 := by
    have hnat : (137086453 : ℕ)^8243*20000000000000^6195 ≤ 2656587377963^6195*625000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137086453 625000000 2656587377963 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165469389/312500000 : ℝ), (537758029/1000000000 : ℝ), (-137086453/625000000 : ℝ)] ![(10728062104649/25000000000000 : ℝ), (43804814678541/100000000000000 : ℝ), (2656587377963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165469389/312500000 : ℝ)|^8243 ≤ (10728062104649/25000000000000 : ℝ)^6195
        have hw : |(165469389/312500000 : ℝ)|=(165469389/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537758029/1000000000 : ℝ)|^8243 ≤ (43804814678541/100000000000000 : ℝ)^6195
        have hw : |(537758029/1000000000 : ℝ)|=(537758029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137086453/625000000 : ℝ)|^8243 ≤ (2656587377963/20000000000000 : ℝ)^6195
        have hw : |(-137086453/625000000 : ℝ)|=(137086453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (35049729/78125000 : ℝ)*x 0 + (4325691953/10000000000 : ℝ)*x 1 + (2162844987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35049729/78125000 : ℝ)^8243 ≤ (34420309008719/100000000000000 : ℝ)^6195 := by
    have hnat : (35049729 : ℕ)^8243*100000000000000^6195 ≤ 34420309008719^6195*78125000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35049729 78125000 34420309008719 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4325691953/10000000000 : ℝ)^8243 ≤ (4098731933393/12500000000000 : ℝ)^6195 := by
    have hnat : (4325691953 : ℕ)^8243*12500000000000^6195 ≤ 4098731933393^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325691953 10000000000 4098731933393 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162844987/5000000000 : ℝ)^8243 ≤ (32789835506541/100000000000000 : ℝ)^6195 := by
    have hnat : (2162844987 : ℕ)^8243*100000000000000^6195 ≤ 32789835506541^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162844987 5000000000 32789835506541 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35049729/78125000 : ℝ), (4325691953/10000000000 : ℝ), (2162844987/5000000000 : ℝ)] ![(34420309008719/100000000000000 : ℝ), (4098731933393/12500000000000 : ℝ), (32789835506541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35049729/78125000 : ℝ)|^8243 ≤ (34420309008719/100000000000000 : ℝ)^6195
        have hw : |(35049729/78125000 : ℝ)|=(35049729/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4325691953/10000000000 : ℝ)|^8243 ≤ (4098731933393/12500000000000 : ℝ)^6195
        have hw : |(4325691953/10000000000 : ℝ)|=(4325691953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2162844987/5000000000 : ℝ)|^8243 ≤ (32789835506541/100000000000000 : ℝ)^6195
        have hw : |(2162844987/5000000000 : ℝ)|=(2162844987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1171535331/5000000000 : ℝ)*x 0 + (5279850731/10000000000 : ℝ)*x 1 + (5279850659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171535331/5000000000 : ℝ)^8243 ≤ (14502512575949/100000000000000 : ℝ)^6195 := by
    have hnat : (1171535331 : ℕ)^8243*100000000000000^6195 ≤ 14502512575949^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171535331 5000000000 14502512575949 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279850731/10000000000 : ℝ)^8243 ≤ (8549748817979/20000000000000 : ℝ)^6195 := by
    have hnat : (5279850731 : ℕ)^8243*20000000000000^6195 ≤ 8549748817979^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279850731 10000000000 8549748817979 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279850659/10000000000 : ℝ)^8243 ≤ (42748743314223/100000000000000 : ℝ)^6195 := by
    have hnat : (5279850659 : ℕ)^8243*100000000000000^6195 ≤ 42748743314223^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279850659 10000000000 42748743314223 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1171535331/5000000000 : ℝ), (5279850731/10000000000 : ℝ), (5279850659/10000000000 : ℝ)] ![(14502512575949/100000000000000 : ℝ), (8549748817979/20000000000000 : ℝ), (42748743314223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1171535331/5000000000 : ℝ)|^8243 ≤ (14502512575949/100000000000000 : ℝ)^6195
        have hw : |(-1171535331/5000000000 : ℝ)|=(1171535331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279850731/10000000000 : ℝ)|^8243 ≤ (8549748817979/20000000000000 : ℝ)^6195
        have hw : |(5279850731/10000000000 : ℝ)|=(5279850731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279850659/10000000000 : ℝ)|^8243 ≤ (42748743314223/100000000000000 : ℝ)^6195
        have hw : |(5279850659/10000000000 : ℝ)|=(5279850659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072842273/2000000000 : ℝ)*x 0 + (-2231540217/10000000000 : ℝ)*x 1 + (5279850743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072842273/2000000000 : ℝ)^8243 ≤ (21829985954661/50000000000000 : ℝ)^6195 := by
    have hnat : (1072842273 : ℕ)^8243*50000000000000^6195 ≤ 21829985954661^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072842273 2000000000 21829985954661 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231540217/10000000000 : ℝ)^8243 ≤ (2718256771417/20000000000000 : ℝ)^6195 := by
    have hnat : (2231540217 : ℕ)^8243*20000000000000^6195 ≤ 2718256771417^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231540217 10000000000 2718256771417 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279850743/10000000000 : ℝ)^8243 ≤ (21374372109587/50000000000000 : ℝ)^6195 := by
    have hnat : (5279850743 : ℕ)^8243*50000000000000^6195 ≤ 21374372109587^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279850743 10000000000 21374372109587 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072842273/2000000000 : ℝ), (-2231540217/10000000000 : ℝ), (5279850743/10000000000 : ℝ)] ![(21829985954661/50000000000000 : ℝ), (2718256771417/20000000000000 : ℝ), (21374372109587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072842273/2000000000 : ℝ)|^8243 ≤ (21829985954661/50000000000000 : ℝ)^6195
        have hw : |(1072842273/2000000000 : ℝ)|=(1072842273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231540217/10000000000 : ℝ)|^8243 ≤ (2718256771417/20000000000000 : ℝ)^6195
        have hw : |(-2231540217/10000000000 : ℝ)|=(2231540217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279850743/10000000000 : ℝ)|^8243 ≤ (21374372109587/50000000000000 : ℝ)^6195
        have hw : |(5279850743/10000000000 : ℝ)|=(5279850743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682105881/5000000000 : ℝ)*x 0 + (5279850553/10000000000 : ℝ)*x 1 + (-2231539939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682105881/5000000000 : ℝ)^8243 ≤ (10914994052191/25000000000000 : ℝ)^6195 := by
    have hnat : (2682105881 : ℕ)^8243*25000000000000^6195 ≤ 10914994052191^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682105881 5000000000 10914994052191 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279850553/10000000000 : ℝ)^8243 ≤ (42748742172261/100000000000000 : ℝ)^6195 := by
    have hnat : (5279850553 : ℕ)^8243*100000000000000^6195 ≤ 42748742172261^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279850553 10000000000 42748742172261 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231539939/10000000000 : ℝ)^8243 ≤ (13591281604171/100000000000000 : ℝ)^6195 := by
    have hnat : (2231539939 : ℕ)^8243*100000000000000^6195 ≤ 13591281604171^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231539939 10000000000 13591281604171 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682105881/5000000000 : ℝ), (5279850553/10000000000 : ℝ), (-2231539939/10000000000 : ℝ)] ![(10914994052191/25000000000000 : ℝ), (42748742172261/100000000000000 : ℝ), (13591281604171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682105881/5000000000 : ℝ)|^8243 ≤ (10914994052191/25000000000000 : ℝ)^6195
        have hw : |(2682105881/5000000000 : ℝ)|=(2682105881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279850553/10000000000 : ℝ)|^8243 ≤ (42748742172261/100000000000000 : ℝ)^6195
        have hw : |(5279850553/10000000000 : ℝ)|=(5279850553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231539939/10000000000 : ℝ)|^8243 ≤ (13591281604171/100000000000000 : ℝ)^6195
        have hw : |(-2231539939/10000000000 : ℝ)|=(2231539939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4268912969/10000000000 : ℝ)*x 0 + (4434395361/10000000000 : ℝ)*x 1 + (1108598933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268912969/10000000000 : ℝ)^8243 ≤ (1288736681379/4000000000000 : ℝ)^6195 := by
    have hnat : (4268912969 : ℕ)^8243*4000000000000^6195 ≤ 1288736681379^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268912969 10000000000 1288736681379 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4434395361/10000000000 : ℝ)^8243 ≤ (6778157917687/20000000000000 : ℝ)^6195 := by
    have hnat : (4434395361 : ℕ)^8243*20000000000000^6195 ≤ 6778157917687^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434395361 10000000000 6778157917687 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108598933/2500000000 : ℝ)^8243 ≤ (33890793361247/100000000000000 : ℝ)^6195 := by
    have hnat : (1108598933 : ℕ)^8243*100000000000000^6195 ≤ 33890793361247^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108598933 2500000000 33890793361247 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268912969/10000000000 : ℝ), (4434395361/10000000000 : ℝ), (1108598933/2500000000 : ℝ)] ![(1288736681379/4000000000000 : ℝ), (6778157917687/20000000000000 : ℝ), (33890793361247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268912969/10000000000 : ℝ)|^8243 ≤ (1288736681379/4000000000000 : ℝ)^6195
        have hw : |(4268912969/10000000000 : ℝ)|=(4268912969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4434395361/10000000000 : ℝ)|^8243 ≤ (6778157917687/20000000000000 : ℝ)^6195
        have hw : |(4434395361/10000000000 : ℝ)|=(4434395361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108598933/2500000000 : ℝ)|^8243 ≤ (33890793361247/100000000000000 : ℝ)^6195
        have hw : |(1108598933/2500000000 : ℝ)|=(1108598933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_8 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2288520009/10000000000 : ℝ)*x 0 + (521356711/1000000000 : ℝ)*x 1 + (5387177943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2288520009/10000000000 : ℝ)^8243 ≤ (14054986372223/100000000000000 : ℝ)^6195 := by
    have hnat : (2288520009 : ℕ)^8243*100000000000000^6195 ≤ 14054986372223^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288520009 10000000000 14054986372223 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521356711/1000000000 : ℝ)^8243 ≤ (42036141760859/100000000000000 : ℝ)^6195 := by
    have hnat : (521356711 : ℕ)^8243*100000000000000^6195 ≤ 42036141760859^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521356711 1000000000 42036141760859 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387177943/10000000000 : ℝ)^8243 ≤ (43908871852903/100000000000000 : ℝ)^6195 := by
    have hnat : (5387177943 : ℕ)^8243*100000000000000^6195 ≤ 43908871852903^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387177943 10000000000 43908871852903 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2288520009/10000000000 : ℝ), (521356711/1000000000 : ℝ), (5387177943/10000000000 : ℝ)] ![(14054986372223/100000000000000 : ℝ), (42036141760859/100000000000000 : ℝ), (43908871852903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2288520009/10000000000 : ℝ)|^8243 ≤ (14054986372223/100000000000000 : ℝ)^6195
        have hw : |(-2288520009/10000000000 : ℝ)|=(2288520009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521356711/1000000000 : ℝ)|^8243 ≤ (42036141760859/100000000000000 : ℝ)^6195
        have hw : |(521356711/1000000000 : ℝ)|=(521356711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387177943/10000000000 : ℝ)|^8243 ≤ (43908871852903/100000000000000 : ℝ)^6195
        have hw : |(5387177943/10000000000 : ℝ)|=(5387177943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_9 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288223181/10000000000 : ℝ)*x 0 + (-2189563049/10000000000 : ℝ)*x 1 + (1346794469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288223181/10000000000 : ℝ)^8243 ≤ (21419483003043/50000000000000 : ℝ)^6195 := by
    have hnat : (5288223181 : ℕ)^8243*50000000000000^6195 ≤ 21419483003043^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288223181 10000000000 21419483003043 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189563049/10000000000 : ℝ)^8243 ≤ (3313040713303/25000000000000 : ℝ)^6195 := by
    have hnat : (2189563049 : ℕ)^8243*25000000000000^6195 ≤ 3313040713303^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189563049 10000000000 3313040713303 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346794469/2500000000 : ℝ)^8243 ≤ (43908871126279/100000000000000 : ℝ)^6195 := by
    have hnat : (1346794469 : ℕ)^8243*100000000000000^6195 ≤ 43908871126279^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346794469 2500000000 43908871126279 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288223181/10000000000 : ℝ), (-2189563049/10000000000 : ℝ), (1346794469/2500000000 : ℝ)] ![(21419483003043/50000000000000 : ℝ), (3313040713303/25000000000000 : ℝ), (43908871126279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288223181/10000000000 : ℝ)|^8243 ≤ (21419483003043/50000000000000 : ℝ)^6195
        have hw : |(5288223181/10000000000 : ℝ)|=(5288223181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189563049/10000000000 : ℝ)|^8243 ≤ (3313040713303/25000000000000 : ℝ)^6195
        have hw : |(-2189563049/10000000000 : ℝ)|=(2189563049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346794469/2500000000 : ℝ)|^8243 ≤ (43908871126279/100000000000000 : ℝ)^6195
        have hw : |(1346794469/2500000000 : ℝ)|=(1346794469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_10 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322055757/2500000000 : ℝ)*x 0 + (538717699/1000000000 : ℝ)*x 1 + (-68423889/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322055757/2500000000 : ℝ)^8243 ≤ (42838964356919/100000000000000 : ℝ)^6195 := by
    have hnat : (1322055757 : ℕ)^8243*100000000000000^6195 ≤ 42838964356919^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322055757 2500000000 42838964356919 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538717699/1000000000 : ℝ)^8243 ≤ (4390886151749/10000000000000 : ℝ)^6195 := by
    have hnat : (538717699 : ℕ)^8243*10000000000000^6195 ≤ 4390886151749^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538717699 1000000000 4390886151749 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68423889/312500000 : ℝ)^8243 ≤ (2650434823953/20000000000000 : ℝ)^6195 := by
    have hnat : (68423889 : ℕ)^8243*20000000000000^6195 ≤ 2650434823953^6195*312500000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68423889 312500000 2650434823953 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322055757/2500000000 : ℝ), (538717699/1000000000 : ℝ), (-68423889/312500000 : ℝ)] ![(42838964356919/100000000000000 : ℝ), (4390886151749/10000000000000 : ℝ), (2650434823953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322055757/2500000000 : ℝ)|^8243 ≤ (42838964356919/100000000000000 : ℝ)^6195
        have hw : |(1322055757/2500000000 : ℝ)|=(1322055757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538717699/1000000000 : ℝ)|^8243 ≤ (4390886151749/10000000000000 : ℝ)^6195
        have hw : |(538717699/1000000000 : ℝ)|=(538717699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68423889/312500000 : ℝ)|^8243 ≤ (2650434823953/20000000000000 : ℝ)^6195
        have hw : |(-68423889/312500000 : ℝ)|=(68423889/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_11 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4507447563/10000000000 : ℝ)*x 0 + (2157504461/5000000000 : ℝ)*x 1 + (4315009747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507447563/10000000000 : ℝ)^8243 ≤ (6927139049653/20000000000000 : ℝ)^6195 := by
    have hnat : (4507447563 : ℕ)^8243*20000000000000^6195 ≤ 6927139049653^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507447563 10000000000 6927139049653 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157504461/5000000000 : ℝ)^8243 ≤ (32682148209487/100000000000000 : ℝ)^6195 := by
    have hnat : (2157504461 : ℕ)^8243*100000000000000^6195 ≤ 32682148209487^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157504461 5000000000 32682148209487 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4315009747/10000000000 : ℝ)^8243 ≤ (32682156523809/100000000000000 : ℝ)^6195 := by
    have hnat : (4315009747 : ℕ)^8243*100000000000000^6195 ≤ 32682156523809^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315009747 10000000000 32682156523809 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507447563/10000000000 : ℝ), (2157504461/5000000000 : ℝ), (4315009747/10000000000 : ℝ)] ![(6927139049653/20000000000000 : ℝ), (32682148209487/100000000000000 : ℝ), (32682156523809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507447563/10000000000 : ℝ)|^8243 ≤ (6927139049653/20000000000000 : ℝ)^6195
        have hw : |(4507447563/10000000000 : ℝ)|=(4507447563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157504461/5000000000 : ℝ)|^8243 ≤ (32682148209487/100000000000000 : ℝ)^6195
        have hw : |(2157504461/5000000000 : ℝ)|=(2157504461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4315009747/10000000000 : ℝ)|^8243 ≤ (32682156523809/100000000000000 : ℝ)^6195
        have hw : |(4315009747/10000000000 : ℝ)|=(4315009747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_12 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534148379/2500000000 : ℝ)*x 0 + (680314489/1250000000 : ℝ)*x 1 + (5271858611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534148379/2500000000 : ℝ)^8243 ≤ (1282729897943/10000000000000 : ℝ)^6195 := by
    have hnat : (534148379 : ℕ)^8243*10000000000000^6195 ≤ 1282729897943^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534148379 2500000000 1282729897943 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680314489/1250000000 : ℝ)^8243 ≤ (4451003626111/10000000000000 : ℝ)^6195 := by
    have hnat : (680314489 : ℕ)^8243*10000000000000^6195 ≤ 4451003626111^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680314489 1250000000 4451003626111 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271858611/10000000000 : ℝ)^8243 ≤ (42662664738271/100000000000000 : ℝ)^6195 := by
    have hnat : (5271858611 : ℕ)^8243*100000000000000^6195 ≤ 42662664738271^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271858611 10000000000 42662664738271 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534148379/2500000000 : ℝ), (680314489/1250000000 : ℝ), (5271858611/10000000000 : ℝ)] ![(1282729897943/10000000000000 : ℝ), (4451003626111/10000000000000 : ℝ), (42662664738271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534148379/2500000000 : ℝ)|^8243 ≤ (1282729897943/10000000000000 : ℝ)^6195
        have hw : |(-534148379/2500000000 : ℝ)|=(534148379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680314489/1250000000 : ℝ)|^8243 ≤ (4451003626111/10000000000000 : ℝ)^6195
        have hw : |(680314489/1250000000 : ℝ)|=(680314489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271858611/10000000000 : ℝ)|^8243 ≤ (42662664738271/100000000000000 : ℝ)^6195
        have hw : |(5271858611/10000000000 : ℝ)|=(5271858611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_13 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369866971/10000000000 : ℝ)*x 0 + (-34915647/156250000 : ℝ)*x 1 + (1317964793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369866971/10000000000 : ℝ)^8243 ≤ (8744246364231/20000000000000 : ℝ)^6195 := by
    have hnat : (5369866971 : ℕ)^8243*20000000000000^6195 ≤ 8744246364231^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369866971 10000000000 8744246364231 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34915647/156250000 : ℝ)^8243 ≤ (13616097390751/100000000000000 : ℝ)^6195 := by
    have hnat : (34915647 : ℕ)^8243*100000000000000^6195 ≤ 13616097390751^6195*156250000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34915647 156250000 13616097390751 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317964793/2500000000 : ℝ)^8243 ≤ (2666416923689/6250000000000 : ℝ)^6195 := by
    have hnat : (1317964793 : ℕ)^8243*6250000000000^6195 ≤ 2666416923689^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317964793 2500000000 2666416923689 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369866971/10000000000 : ℝ), (-34915647/156250000 : ℝ), (1317964793/2500000000 : ℝ)] ![(8744246364231/20000000000000 : ℝ), (13616097390751/100000000000000 : ℝ), (2666416923689/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369866971/10000000000 : ℝ)|^8243 ≤ (8744246364231/20000000000000 : ℝ)^6195
        have hw : |(5369866971/10000000000 : ℝ)|=(5369866971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34915647/156250000 : ℝ)|^8243 ≤ (13616097390751/100000000000000 : ℝ)^6195
        have hw : |(-34915647/156250000 : ℝ)|=(34915647/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317964793/2500000000 : ℝ)|^8243 ≤ (2666416923689/6250000000000 : ℝ)^6195
        have hw : |(1317964793/2500000000 : ℝ)|=(1317964793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_14 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214794669/400000000 : ℝ)*x 0 + (263592957/500000000 : ℝ)*x 1 + (-1117300889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214794669/400000000 : ℝ)^8243 ≤ (43721229156089/100000000000000 : ℝ)^6195 := by
    have hnat : (214794669 : ℕ)^8243*100000000000000^6195 ≤ 43721229156089^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214794669 400000000 43721229156089 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263592957/500000000 : ℝ)^8243 ≤ (21331335217227/50000000000000 : ℝ)^6195 := by
    have hnat : (263592957 : ℕ)^8243*50000000000000^6195 ≤ 21331335217227^6195*500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263592957 500000000 21331335217227 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117300889/5000000000 : ℝ)^8243 ≤ (13616100390593/100000000000000 : ℝ)^6195 := by
    have hnat : (1117300889 : ℕ)^8243*100000000000000^6195 ≤ 13616100390593^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117300889 5000000000 13616100390593 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214794669/400000000 : ℝ), (263592957/500000000 : ℝ), (-1117300889/5000000000 : ℝ)] ![(43721229156089/100000000000000 : ℝ), (21331335217227/50000000000000 : ℝ), (13616100390593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214794669/400000000 : ℝ)|^8243 ≤ (43721229156089/100000000000000 : ℝ)^6195
        have hw : |(214794669/400000000 : ℝ)|=(214794669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263592957/500000000 : ℝ)|^8243 ≤ (21331335217227/50000000000000 : ℝ)^6195
        have hw : |(263592957/500000000 : ℝ)|=(263592957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117300889/5000000000 : ℝ)|^8243 ≤ (13616100390593/100000000000000 : ℝ)^6195
        have hw : |(-1117300889/5000000000 : ℝ)|=(1117300889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_box_15 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265681283/625000000 : ℝ)*x 0 + (4443280377/10000000000 : ℝ)*x 1 + (888655961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265681283/625000000 : ℝ)^8243 ≤ (32037657935673/100000000000000 : ℝ)^6195 := by
    have hnat : (265681283 : ℕ)^8243*100000000000000^6195 ≤ 32037657935673^6195*625000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265681283 625000000 32037657935673 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4443280377/10000000000 : ℝ)^8243 ≤ (16990586967947/50000000000000 : ℝ)^6195 := by
    have hnat : (4443280377 : ℕ)^8243*50000000000000^6195 ≤ 16990586967947^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443280377 10000000000 16990586967947 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888655961/2000000000 : ℝ)^8243 ≤ (33981168115201/100000000000000 : ℝ)^6195 := by
    have hnat : (888655961 : ℕ)^8243*100000000000000^6195 ≤ 33981168115201^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888655961 2000000000 33981168115201 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265681283/625000000 : ℝ), (4443280377/10000000000 : ℝ), (888655961/2000000000 : ℝ)] ![(32037657935673/100000000000000 : ℝ), (16990586967947/50000000000000 : ℝ), (33981168115201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265681283/625000000 : ℝ)|^8243 ≤ (32037657935673/100000000000000 : ℝ)^6195
        have hw : |(265681283/625000000 : ℝ)|=(265681283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4443280377/10000000000 : ℝ)|^8243 ≤ (16990586967947/50000000000000 : ℝ)^6195
        have hw : |(4443280377/10000000000 : ℝ)|=(4443280377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888655961/2000000000 : ℝ)|^8243 ≤ (33981168115201/100000000000000 : ℝ)^6195
        have hw : |(888655961/2000000000 : ℝ)|=(888655961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59229/100000 : ℝ) ∧ (39761/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20729/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1749/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1749/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1749/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1749/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1749/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1749/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1123/10000 : ℝ) ^ (4121/1024 : ℝ) ≤ (942355900936157/6250000000000000000 : ℝ) := by
    have hpowers : (1123/10000 : ℝ)^4121 ≤ (942355900936157/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1123 : ℕ)^4121*6250000000000000000^1024 ≤ 942355900936157^1024*10000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1123 10000 942355900936157 6250000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1123/10000 : ℝ)) (X := (942355900936157/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1749/12500 : ℝ) ^ (4121/1024 : ℝ) ≤ (36531427402494787/100000000000000000000 : ℝ) := by
    have hpowers : (1749/12500 : ℝ)^4121 ≤ (36531427402494787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1749 : ℕ)^4121*100000000000000000000^1024 ≤ 36531427402494787^1024*12500^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1749 12500 36531427402494787 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1749/12500 : ℝ)) (X := (36531427402494787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125942355900936157/3125000000000000000 : ℝ) ≤ (10000749226397047/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (3125942355900936157/3125000000000000000 : ℝ)^1024 ≤ (10000749226397047/10000000000000000 : ℝ)^4121 := by
      have hnat : (3125942355900936157 : ℕ)^1024*10000000000000000^4121 ≤ 10000749226397047^4121*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125942355900936157 3125000000000000000 10000749226397047 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000749226397047/10000000000000000 : ℝ)) (X := (3125942355900936157/3125000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051609121817473299/100000000000000000000 : ℝ) ≤ (10001282152276149/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (100051609121817473299/100000000000000000000 : ℝ)^1024 ≤ (10001282152276149/10000000000000000 : ℝ)^4121 := by
      have hnat : (100051609121817473299 : ℕ)^1024*10000000000000000^4121 ≤ 10001282152276149^4121*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051609121817473299 100000000000000000000 10001282152276149 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001282152276149/10000000000000000 : ℝ)) (X := (100051609121817473299/100000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036531427402494787/50000000000000000000 : ℝ) ≤ (10001815078155251/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50036531427402494787/50000000000000000000 : ℝ)^1024 ≤ (10001815078155251/10000000000000000 : ℝ)^4121 := by
      have hnat : (50036531427402494787 : ℕ)^1024*10000000000000000^4121 ≤ 10001815078155251^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036531427402494787 50000000000000000000 10001815078155251 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001815078155251/10000000000000000 : ℝ)) (X := (50036531427402494787/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(942355900936157/6250000000000000000 : ℝ) ≤ ((13805049924032006447/13810000000000000000 : ℝ)+2*(266462939551/138100000000000 : ℝ)*(1123/10000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (13805049924032006447/13810000000000000000 : ℝ)+2*(266462939551/138100000000000 : ℝ)*(1123/10000 : ℝ)=(10000749226397047/10000000000000000 : ℝ) by norm_num, show 1+2*(942355900936157/6250000000000000000 : ℝ)=(3125942355900936157/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36531427402494787/100000000000000000000 : ℝ)+(942355900936157/6250000000000000000 : ℝ) ≤ ((13805049924032006447/13810000000000000000 : ℝ)+(266462939551/138100000000000 : ℝ)*((1749/12500 : ℝ)+(1123/10000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (13805049924032006447/13810000000000000000 : ℝ)+(266462939551/138100000000000 : ℝ)*((1749/12500 : ℝ)+(1123/10000 : ℝ))=(10001282152276149/10000000000000000 : ℝ) by norm_num, show 1+(36531427402494787/100000000000000000000 : ℝ)+(942355900936157/6250000000000000000 : ℝ)=(100051609121817473299/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36531427402494787/100000000000000000000 : ℝ) ≤ ((13805049924032006447/13810000000000000000 : ℝ)+2*(266462939551/138100000000000 : ℝ)*(1749/12500 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (13805049924032006447/13810000000000000000 : ℝ)+2*(266462939551/138100000000000 : ℝ)*(1749/12500 : ℝ)=(10001815078155251/10000000000000000 : ℝ) by norm_num, show 1+2*(36531427402494787/100000000000000000000 : ℝ)=(50036531427402494787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13805049924032006447/13810000000000000000 : ℝ)*(X 1 0+X 2 0)+(266462939551/138100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (13805049924032006447/13810000000000000000 : ℝ)) (alpha := (266462939551/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13805049924032006447/13810000000000000000 : ℝ)*(X 0 1+X 2 1)+(266462939551/138100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (13805049924032006447/13810000000000000000 : ℝ)) (alpha := (266462939551/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13805049924032006447/13810000000000000000 : ℝ)*(X 0 2+X 1 2)+(266462939551/138100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (13805049924032006447/13810000000000000000 : ℝ)) (alpha := (266462939551/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416332729/2000000000 : ℝ)*X 0 0+(5377580737/10000000000 : ℝ)*X 0 1+(5377579417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295021451/10000000000 : ℝ)*X 1 0+(-2193382251/10000000000 : ℝ)*X 1 1+(5377580033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((165469389/312500000 : ℝ)*X 2 0+(537758029/1000000000 : ℝ)*X 2 1+(-137086453/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((35049729/78125000 : ℝ)*X 0 0+(4325691953/10000000000 : ℝ)*X 0 1+(2162844987/5000000000 : ℝ)*X 0 2+(35049729/78125000 : ℝ)*X 1 0+(4325691953/10000000000 : ℝ)*X 1 1+(2162844987/5000000000 : ℝ)*X 1 2+(35049729/78125000 : ℝ)*X 2 0+(4325691953/10000000000 : ℝ)*X 2 1+(2162844987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1171535331/5000000000 : ℝ)*X 0 0+(5279850731/10000000000 : ℝ)*X 0 1+(5279850659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072842273/2000000000 : ℝ)*X 1 0+(-2231540217/10000000000 : ℝ)*X 1 1+(5279850743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682105881/5000000000 : ℝ)*X 2 0+(5279850553/10000000000 : ℝ)*X 2 1+(-2231539939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268912969/10000000000 : ℝ)*X 0 0+(4434395361/10000000000 : ℝ)*X 0 1+(1108598933/2500000000 : ℝ)*X 0 2+(4268912969/10000000000 : ℝ)*X 1 0+(4434395361/10000000000 : ℝ)*X 1 1+(1108598933/2500000000 : ℝ)*X 1 2+(4268912969/10000000000 : ℝ)*X 2 0+(4434395361/10000000000 : ℝ)*X 2 1+(1108598933/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2288520009/10000000000 : ℝ)*X 0 0+(521356711/1000000000 : ℝ)*X 0 1+(5387177943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288223181/10000000000 : ℝ)*X 1 0+(-2189563049/10000000000 : ℝ)*X 1 1+(1346794469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322055757/2500000000 : ℝ)*X 2 0+(538717699/1000000000 : ℝ)*X 2 1+(-68423889/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4507447563/10000000000 : ℝ)*X 0 0+(2157504461/5000000000 : ℝ)*X 0 1+(4315009747/10000000000 : ℝ)*X 0 2+(4507447563/10000000000 : ℝ)*X 1 0+(2157504461/5000000000 : ℝ)*X 1 1+(4315009747/10000000000 : ℝ)*X 1 2+(4507447563/10000000000 : ℝ)*X 2 0+(2157504461/5000000000 : ℝ)*X 2 1+(4315009747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-534148379/2500000000 : ℝ)*X 0 0+(680314489/1250000000 : ℝ)*X 0 1+(5271858611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369866971/10000000000 : ℝ)*X 1 0+(-34915647/156250000 : ℝ)*X 1 1+(1317964793/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((214794669/400000000 : ℝ)*X 2 0+(263592957/500000000 : ℝ)*X 2 1+(-1117300889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((265681283/625000000 : ℝ)*X 0 0+(4443280377/10000000000 : ℝ)*X 0 1+(888655961/2000000000 : ℝ)*X 0 2+(265681283/625000000 : ℝ)*X 1 0+(4443280377/10000000000 : ℝ)*X 1 1+(888655961/2000000000 : ℝ)*X 1 2+(265681283/625000000 : ℝ)*X 2 0+(4443280377/10000000000 : ℝ)*X 2 1+(888655961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-4296373219286685309944150091/6905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195307433/100000000000000 : ℝ)*(upper0) + (348887/100000000000000 : ℝ)*(lower1) + (28072239/12500000000000 : ℝ)*(lower2) + (12451153/50000000000000 : ℝ)*(lower3) + (3015377/50000000000000 : ℝ)*(upper5) + (3843251356699947/100000000000000 : ℝ)*(major0) + (3843251356699947/100000000000000 : ℝ)*(major1) + (3843251356699947/100000000000000 : ℝ)*(major2) + (2552428983440433/50000000000000 : ℝ)*(sp4) + (2552386792596703/50000000000000 : ℝ)*(sp5) + (5104734821940429/100000000000000 : ℝ)*(sp6) + (2602385143426021/100000000000000 : ℝ)*(sp7) + (84381687461/100000000000000 : ℝ)*(sp13) + (123144940437/100000000000000 : ℝ)*(sp14) + (2602385143426021/100000000000000 : ℝ)*(f.failure) + (2552428983440433/50000000000000 : ℝ)*(f.sum) + (297377436303/1726250000000000000000000000 : ℝ)*base65 + (11659637166441258309/1381000000000000000000000000000000 : ℝ)*base67 + (13337784949182258309/1381000000000000000000000000000000 : ℝ)*base69 + (13364461977441741691/1381000000000000000000000000000000 : ℝ)*base72 + (191086023466971/3452500000000000000000000000 : ℝ)*base73 + (11594032616353741691/1381000000000000000000000000000000 : ℝ)*base76 + (1489760717103741691/1381000000000000000000000000000000 : ℝ)*base78 + (19941855476090258309/1381000000000000000000000000000000 : ℝ)*base79 + (106427008791739/3452500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4525761/5000000000000000000000 : ℝ)*base89 + (4525761/5000000000000000000000 : ℝ)*base91 + (4525761/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59229/100000 : ℝ) ≤ (204496570724881320765753767237769/345250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53874759/50000000000000 : ℝ)*(lower0) + (6707607/20000000000000 : ℝ)*(upper1) + (273456483/100000000000000 : ℝ)*(upper2) + (316762887/50000000000000 : ℝ)*(upper3) + (4971829/1250000000000 : ℝ)*(lower5) + (3905899349225709/100000000000000 : ℝ)*(major0) + (3905899349225709/100000000000000 : ℝ)*(major1) + (3905899349225709/100000000000000 : ℝ)*(major2) + (5147248833238579/100000000000000 : ℝ)*(sp0) + (2573477030789801/50000000000000 : ℝ)*(sp1) + (5147242702578387/100000000000000 : ℝ)*(sp2) + (1322403024775141/50000000000000 : ℝ)*(sp3) + (191583131/3125000000000 : ℝ)*(sp6) + (294771658977/100000000000000 : ℝ)*(sp9) + (1322403024775141/50000000000000 : ℝ)*(f.failure) + (5147248833238579/100000000000000 : ℝ)*(f.sum) + (24137719560543/3452500000000000000000000000 : ℝ)*base66 + (11495477065876954077/1381000000000000000000000000000000 : ℝ)*base68 + (10693761879478954077/1381000000000000000000000000000000 : ℝ)*base70 + (670194877250954077/1381000000000000000000000000000000 : ℝ)*base72 + (750924136381/431562500000000000000000000 : ℝ)*base74 + (3769084390253954077/1381000000000000000000000000000000 : ℝ)*base76 + (15456903455171954077/1381000000000000000000000000000000 : ℝ)*base78 + (11509461665900045923/1381000000000000000000000000000000 : ℝ)*base79 + (21676727612039/6905000000000000000000000000 : ℝ)*base81 + (152319/2500000000000000000000 : ℝ)*base90 + (152319/2500000000000000000000 : ℝ)*base92 + (152319/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39761/50000 : ℝ) ≤ (2745576214803975186835373427/3452500000000000000000000000 : ℝ) := by norm_num
    linear_combination (876406989/100000000000000 : ℝ)*(upper0) + (58637707/100000000000000 : ℝ)*(lower1) + (88126463/100000000000000 : ℝ)*(upper2) + (96327257/100000000000000 : ℝ)*(lower3) + (199106877/12500000000000 : ℝ)*(lower5) + (136691732600929/3125000000000 : ℝ)*(major0) + (136691732600929/3125000000000 : ℝ)*(major1) + (136691732600929/3125000000000 : ℝ)*(major2) + (939497679/100000000000000 : ℝ)*(sp0) + (95733694379/100000000000000 : ℝ)*(sp3) + (1439974640792741/25000000000000 : ℝ)*(sp8) + (2879949751334321/50000000000000 : ℝ)*(sp9) + (2879949751334321/50000000000000 : ℝ)*(sp10) + (592353510487923/20000000000000 : ℝ)*(sp11) + (1480931643066997/50000000000000 : ℝ)*(f.failure) + (2879949751334321/50000000000000 : ℝ)*(f.sum) + (2697053135009/3452500000000000000000000000 : ℝ)*base65 + (934120730502160737/43156250000000000000000000000000 : ℝ)*base68 + (869265755305776763/43156250000000000000000000000000 : ℝ)*base69 + (265989890131745513/43156250000000000000000000000000 : ℝ)*base71 + (50020430703767/6905000000000000000000000000 : ℝ)*base74 + (29801677071004487/43156250000000000000000000000000 : ℝ)*base76 + (3095058072558013/43156250000000000000000000000000 : ℝ)*base77 + (308913725051441987/43156250000000000000000000000000 : ℝ)*base80 + (46899896699047/6905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (15475823/2500000000000000000000 : ℝ)*base90 + (15475823/2500000000000000000000 : ℝ)*base92 + (15475823/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20729/25000 : ℝ) ≤ (-1431289988771404298240140029783/1726250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77304099/100000000000000 : ℝ)*(lower0) + (316188579/100000000000000 : ℝ)*(upper3) + (133183027/100000000000000 : ℝ)*(lower4) + (22043279209363/500000000000 : ℝ)*(major0) + (22043279209363/500000000000 : ℝ)*(major1) + (22043279209363/500000000000 : ℝ)*(major2) + (2527356717/100000000000000 : ℝ)*(sp0) + (775575393/4000000000000 : ℝ)*(sp5) + (81889299749/100000000000000 : ℝ)*(sp7) + (1142021/1000000000000 : ℝ)*(sp8) + (5859708669632521/100000000000000 : ℝ)*(sp12) + (5859691921806513/100000000000000 : ℝ)*(sp13) + (2929855655595669/50000000000000 : ℝ)*(sp14) + (1492578116729841/50000000000000 : ℝ)*(sp15) + (373154765344929/12500000000000 : ℝ)*(f.failure) + (2929855655595669/50000000000000 : ℝ)*(f.sum) + (1626157064241/345250000000000000000000000 : ℝ)*base65 + (59080595750043261/6905000000000000000000000000000 : ℝ)*base67 + (35922152304373261/6905000000000000000000000000000 : ℝ)*base69 + (57329591041938261/6905000000000000000000000000000 : ℝ)*base71 + (2267318296613/690500000000000000000000000 : ℝ)*base73 + (22126655628518261/6905000000000000000000000000000 : ℝ)*base75 + (2050024140871739/6905000000000000000000000000000 : ℝ)*base78 + (104175329632248261/6905000000000000000000000000000 : ℝ)*base79 + (2316587446443/690500000000000000000000000 : ℝ)*base81 + (3061811/625000000000000000000 : ℝ)*base90 + (3061811/625000000000000000000 : ℝ)*base92 + (3061811/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1050_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59229/100000 : ℝ) else (39761/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20729/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1050_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1050_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59229/100000 : ℝ) else (39761/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20729/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1050_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1050_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59229/100000 : ℝ) else (39761/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20729/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

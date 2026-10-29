-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:30.790994+00:00
-- url     : https://prove2.me/submissions/04ad8a43-f49d-41fd-aab8-f52a4634f658

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
theorem support_rectangle_w1532_s3_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838477127/10000000000 : ℝ)*x 0 + (5433246771/10000000000 : ℝ)*x 1 + (5216241629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838477127/10000000000 : ℝ)^4561 ≤ (1125928682273/10000000000000 : ℝ)^3537 := by
    have hnat : (1838477127 : ℕ)^4561*10000000000000^3537 ≤ 1125928682273^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838477127 10000000000 1125928682273 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433246771/10000000000 : ℝ)^4561 ≤ (45536144008083/100000000000000 : ℝ)^3537 := by
    have hnat : (5433246771 : ℕ)^4561*100000000000000^3537 ≤ 45536144008083^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433246771 10000000000 45536144008083 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216241629/10000000000 : ℝ)^4561 ≤ (4320456915293/10000000000000 : ℝ)^3537 := by
    have hnat : (5216241629 : ℕ)^4561*10000000000000^3537 ≤ 4320456915293^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216241629 10000000000 4320456915293 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838477127/10000000000 : ℝ), (5433246771/10000000000 : ℝ), (5216241629/10000000000 : ℝ)] ![(1125928682273/10000000000000 : ℝ), (45536144008083/100000000000000 : ℝ), (4320456915293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838477127/10000000000 : ℝ)|^4561 ≤ (1125928682273/10000000000000 : ℝ)^3537
        have hw : |(-1838477127/10000000000 : ℝ)|=(1838477127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433246771/10000000000 : ℝ)|^4561 ≤ (45536144008083/100000000000000 : ℝ)^3537
        have hw : |(5433246771/10000000000 : ℝ)|=(5433246771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216241629/10000000000 : ℝ)|^4561 ≤ (4320456915293/10000000000000 : ℝ)^3537
        have hw : |(5216241629/10000000000 : ℝ)|=(5216241629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351140699/10000000000 : ℝ)*x 0 + (-77985333/400000000 : ℝ)*x 1 + (2608120761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351140699/10000000000 : ℝ)^4561 ≤ (2790671105961/6250000000000 : ℝ)^3537 := by
    have hnat : (5351140699 : ℕ)^4561*6250000000000^3537 ≤ 2790671105961^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351140699 10000000000 2790671105961 6250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77985333/400000000 : ℝ)^4561 ≤ (6072347141361/50000000000000 : ℝ)^3537 := by
    have hnat : (77985333 : ℕ)^4561*50000000000000^3537 ≤ 6072347141361^3537*400000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77985333 400000000 6072347141361 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608120761/5000000000 : ℝ)^4561 ≤ (43204568010103/100000000000000 : ℝ)^3537 := by
    have hnat : (2608120761 : ℕ)^4561*100000000000000^3537 ≤ 43204568010103^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608120761 5000000000 43204568010103 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351140699/10000000000 : ℝ), (-77985333/400000000 : ℝ), (2608120761/5000000000 : ℝ)] ![(2790671105961/6250000000000 : ℝ), (6072347141361/50000000000000 : ℝ), (43204568010103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351140699/10000000000 : ℝ)|^4561 ≤ (2790671105961/6250000000000 : ℝ)^3537
        have hw : |(5351140699/10000000000 : ℝ)|=(5351140699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77985333/400000000 : ℝ)|^4561 ≤ (6072347141361/50000000000000 : ℝ)^3537
        have hw : |(-77985333/400000000 : ℝ)|=(77985333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608120761/5000000000 : ℝ)|^4561 ≤ (43204568010103/100000000000000 : ℝ)^3537
        have hw : |(2608120761/5000000000 : ℝ)|=(2608120761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668892609/1250000000 : ℝ)*x 0 + (5216241247/10000000000 : ℝ)*x 1 + (-1949633459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668892609/1250000000 : ℝ)^4561 ≤ (8930147911367/20000000000000 : ℝ)^3537 := by
    have hnat : (668892609 : ℕ)^4561*20000000000000^3537 ≤ 8930147911367^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668892609 1250000000 8930147911367 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216241247/10000000000 : ℝ)^4561 ≤ (43204565072929/100000000000000 : ℝ)^3537 := by
    have hnat : (5216241247 : ℕ)^4561*100000000000000^3537 ≤ 43204565072929^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216241247 10000000000 43204565072929 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949633459/10000000000 : ℝ)^4561 ≤ (12144695359097/100000000000000 : ℝ)^3537 := by
    have hnat : (1949633459 : ℕ)^4561*100000000000000^3537 ≤ 12144695359097^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949633459 10000000000 12144695359097 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668892609/1250000000 : ℝ), (5216241247/10000000000 : ℝ), (-1949633459/10000000000 : ℝ)] ![(8930147911367/20000000000000 : ℝ), (43204565072929/100000000000000 : ℝ), (12144695359097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668892609/1250000000 : ℝ)|^4561 ≤ (8930147911367/20000000000000 : ℝ)^3537
        have hw : |(668892609/1250000000 : ℝ)|=(668892609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216241247/10000000000 : ℝ)|^4561 ≤ (43204565072929/100000000000000 : ℝ)^3537
        have hw : |(5216241247/10000000000 : ℝ)|=(5216241247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949633459/10000000000 : ℝ)|^4561 ≤ (12144695359097/100000000000000 : ℝ)^3537
        have hw : |(-1949633459/10000000000 : ℝ)|=(1949633459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260301453/10000000000 : ℝ)*x 0 + (4016892463/10000000000 : ℝ)*x 1 + (1128978377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260301453/10000000000 : ℝ)^4561 ≤ (33278157461893/100000000000000 : ℝ)^3537 := by
    have hnat : (4260301453 : ℕ)^4561*100000000000000^3537 ≤ 33278157461893^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260301453 10000000000 33278157461893 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016892463/10000000000 : ℝ)^4561 ≤ (6169388275443/20000000000000 : ℝ)^3537 := by
    have hnat : (4016892463 : ℕ)^4561*20000000000000^3537 ≤ 6169388275443^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016892463 10000000000 6169388275443 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128978377/2500000000 : ℝ)^4561 ≤ (35874901143553/100000000000000 : ℝ)^3537 := by
    have hnat : (1128978377 : ℕ)^4561*100000000000000^3537 ≤ 35874901143553^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128978377 2500000000 35874901143553 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260301453/10000000000 : ℝ), (4016892463/10000000000 : ℝ), (1128978377/2500000000 : ℝ)] ![(33278157461893/100000000000000 : ℝ), (6169388275443/20000000000000 : ℝ), (35874901143553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260301453/10000000000 : ℝ)|^4561 ≤ (33278157461893/100000000000000 : ℝ)^3537
        have hw : |(4260301453/10000000000 : ℝ)|=(4260301453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016892463/10000000000 : ℝ)|^4561 ≤ (6169388275443/20000000000000 : ℝ)^3537
        have hw : |(4016892463/10000000000 : ℝ)|=(4016892463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128978377/2500000000 : ℝ)|^4561 ≤ (35874901143553/100000000000000 : ℝ)^3537
        have hw : |(1128978377/2500000000 : ℝ)|=(1128978377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367701529/2000000000 : ℝ)*x 0 + (5217388821/10000000000 : ℝ)*x 1 + (1086418133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367701529/2000000000 : ℝ)^4561 ≤ (11259527832571/100000000000000 : ℝ)^3537 := by
    have hnat : (367701529 : ℕ)^4561*100000000000000^3537 ≤ 11259527832571^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367701529 2000000000 11259527832571 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217388821/10000000000 : ℝ)^4561 ≤ (8643364455931/20000000000000 : ℝ)^3537 := by
    have hnat : (5217388821 : ℕ)^4561*20000000000000^3537 ≤ 8643364455931^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217388821 10000000000 8643364455931 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086418133/2000000000 : ℝ)^4561 ≤ (45523649875477/100000000000000 : ℝ)^3537 := by
    have hnat : (1086418133 : ℕ)^4561*100000000000000^3537 ≤ 45523649875477^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086418133 2000000000 45523649875477 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367701529/2000000000 : ℝ), (5217388821/10000000000 : ℝ), (1086418133/2000000000 : ℝ)] ![(11259527832571/100000000000000 : ℝ), (8643364455931/20000000000000 : ℝ), (45523649875477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367701529/2000000000 : ℝ)|^4561 ≤ (11259527832571/100000000000000 : ℝ)^3537
        have hw : |(-367701529/2000000000 : ℝ)|=(367701529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217388821/10000000000 : ℝ)|^4561 ≤ (8643364455931/20000000000000 : ℝ)^3537
        have hw : |(5217388821/10000000000 : ℝ)|=(5217388821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086418133/2000000000 : ℝ)|^4561 ≤ (45523649875477/100000000000000 : ℝ)^3537
        have hw : |(1086418133/2000000000 : ℝ)|=(1086418133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647003631/5000000000 : ℝ)*x 0 + (-1733784439/10000000000 : ℝ)*x 1 + (5432090659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647003631/5000000000 : ℝ)^4561 ≤ (2752308844173/6250000000000 : ℝ)^3537 := by
    have hnat : (2647003631 : ℕ)^4561*6250000000000^3537 ≤ 2752308844173^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647003631 5000000000 2752308844173 6250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1733784439/10000000000 : ℝ)^4561 ≤ (10439408664589/100000000000000 : ℝ)^3537 := by
    have hnat : (1733784439 : ℕ)^4561*100000000000000^3537 ≤ 10439408664589^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733784439 10000000000 10439408664589 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432090659/10000000000 : ℝ)^4561 ≤ (45523649810637/100000000000000 : ℝ)^3537 := by
    have hnat : (5432090659 : ℕ)^4561*100000000000000^3537 ≤ 45523649810637^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432090659 10000000000 45523649810637 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647003631/5000000000 : ℝ), (-1733784439/10000000000 : ℝ), (5432090659/10000000000 : ℝ)] ![(2752308844173/6250000000000 : ℝ), (10439408664589/100000000000000 : ℝ), (45523649810637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647003631/5000000000 : ℝ)|^4561 ≤ (2752308844173/6250000000000 : ℝ)^3537
        have hw : |(2647003631/5000000000 : ℝ)|=(2647003631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1733784439/10000000000 : ℝ)|^4561 ≤ (10439408664589/100000000000000 : ℝ)^3537
        have hw : |(-1733784439/10000000000 : ℝ)|=(1733784439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432090659/10000000000 : ℝ)|^4561 ≤ (45523649810637/100000000000000 : ℝ)^3537
        have hw : |(5432090659/10000000000 : ℝ)|=(5432090659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294007661/10000000000 : ℝ)*x 0 + (5432090509/10000000000 : ℝ)*x 1 + (-866892049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294007661/10000000000 : ℝ)^4561 ≤ (22018472893319/50000000000000 : ℝ)^3537 := by
    have hnat : (5294007661 : ℕ)^4561*50000000000000^3537 ≤ 22018472893319^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294007661 10000000000 22018472893319 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432090509/10000000000 : ℝ)^4561 ≤ (5690456023703/12500000000000 : ℝ)^3537 := by
    have hnat : (5432090509 : ℕ)^4561*12500000000000^3537 ≤ 5690456023703^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432090509 10000000000 5690456023703 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866892049/5000000000 : ℝ)^4561 ≤ (10439406016941/100000000000000 : ℝ)^3537 := by
    have hnat : (866892049 : ℕ)^4561*100000000000000^3537 ≤ 10439406016941^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866892049 5000000000 10439406016941 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294007661/10000000000 : ℝ), (5432090509/10000000000 : ℝ), (-866892049/5000000000 : ℝ)] ![(22018472893319/50000000000000 : ℝ), (5690456023703/12500000000000 : ℝ), (10439406016941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294007661/10000000000 : ℝ)|^4561 ≤ (22018472893319/50000000000000 : ℝ)^3537
        have hw : |(5294007661/10000000000 : ℝ)|=(5294007661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432090509/10000000000 : ℝ)|^4561 ≤ (5690456023703/12500000000000 : ℝ)^3537
        have hw : |(5432090509/10000000000 : ℝ)|=(5432090509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-866892049/5000000000 : ℝ)|^4561 ≤ (10439406016941/100000000000000 : ℝ)^3537
        have hw : |(-866892049/5000000000 : ℝ)|=(866892049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s3_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065092699/2500000000 : ℝ)*x 0 + (2256637523/5000000000 : ℝ)*x 1 + (4019550887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065092699/2500000000 : ℝ)^4561 ≤ (33278855931647/100000000000000 : ℝ)^3537 := by
    have hnat : (1065092699 : ℕ)^4561*100000000000000^3537 ≤ 33278855931647^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065092699 2500000000 33278855931647 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256637523/5000000000 : ℝ)^4561 ≤ (448098437393/1250000000000 : ℝ)^3537 := by
    have hnat : (2256637523 : ℕ)^4561*1250000000000^3537 ≤ 448098437393^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256637523 5000000000 448098437393 1250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019550887/10000000000 : ℝ)^4561 ≤ (7718317266893/25000000000000 : ℝ)^3537 := by
    have hnat : (4019550887 : ℕ)^4561*25000000000000^3537 ≤ 7718317266893^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019550887 10000000000 7718317266893 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065092699/2500000000 : ℝ), (2256637523/5000000000 : ℝ), (4019550887/10000000000 : ℝ)] ![(33278855931647/100000000000000 : ℝ), (448098437393/1250000000000 : ℝ), (7718317266893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065092699/2500000000 : ℝ)|^4561 ≤ (33278855931647/100000000000000 : ℝ)^3537
        have hw : |(1065092699/2500000000 : ℝ)|=(1065092699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256637523/5000000000 : ℝ)|^4561 ≤ (448098437393/1250000000000 : ℝ)^3537
        have hw : |(2256637523/5000000000 : ℝ)|=(2256637523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4019550887/10000000000 : ℝ)|^4561 ≤ (7718317266893/25000000000000 : ℝ)^3537
        have hw : |(4019550887/10000000000 : ℝ)|=(4019550887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (637/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10941/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7769/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (637/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (637/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (637/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (637/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (637/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (637/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2117/20000 : ℝ) ^ (4559/1024 : ℝ) ≤ (2273782664645513/50000000000000000000 : ℝ) := by
    have hpowers : (2117/20000 : ℝ)^4559 ≤ (2273782664645513/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2117 : ℕ)^4559*50000000000000000000^1024 ≤ 2273782664645513^1024*20000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2117 20000 2273782664645513 50000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2117/20000 : ℝ)) (X := (2273782664645513/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (637/4000 : ℝ) ^ (4559/1024 : ℝ) ≤ (2802458757697129/10000000000000000000 : ℝ) := by
    have hpowers : (637/4000 : ℝ)^4559 ≤ (2802458757697129/10000000000000000000 : ℝ)^1024 := by
      have hnat : (637 : ℕ)^4559*10000000000000000000^1024 ≤ 2802458757697129^1024*4000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        637 4000 2802458757697129 10000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (637/4000 : ℝ)) (X := (2802458757697129/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002273782664645513/25000000000000000000 : ℝ) ≤ (1250025534890899/1250000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (25002273782664645513/25000000000000000000 : ℝ)^1024 ≤ (1250025534890899/1250000000000000 : ℝ)^4559 := by
      have hnat : (25002273782664645513 : ℕ)^1024*1250000000000000^4559 ≤ 1250025534890899^4559*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002273782664645513 25000000000000000000 1250025534890899 1250000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025534890899/1250000000000000 : ℝ)) (X := (25002273782664645513/25000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008143038226565579/25000000000000000000 : ℝ) ≤ (10000731512907271/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (25008143038226565579/25000000000000000000 : ℝ)^1024 ≤ (10000731512907271/10000000000000000 : ℝ)^4559 := by
      have hnat : (25008143038226565579 : ℕ)^1024*10000000000000000^4559 ≤ 10000731512907271^4559*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008143038226565579 25000000000000000000 10000731512907271 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000731512907271/10000000000000000 : ℝ)) (X := (25008143038226565579/25000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002802458757697129/5000000000000000000 : ℝ) ≤ (200025174933747/200000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (5002802458757697129/5000000000000000000 : ℝ)^1024 ≤ (200025174933747/200000000000000 : ℝ)^4559 := by
      have hnat : (5002802458757697129 : ℕ)^1024*200000000000000^4559 ≤ 200025174933747^4559*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002802458757697129 5000000000000000000 200025174933747 200000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200025174933747/200000000000000 : ℝ)) (X := (5002802458757697129/5000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2273782664645513/50000000000000000000 : ℝ) ≤ ((1067798586228298657/1068000000000000000 : ℝ)+2*(527233780079/534000000000000 : ℝ)*(2117/20000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (1067798586228298657/1068000000000000000 : ℝ)+2*(527233780079/534000000000000 : ℝ)*(2117/20000 : ℝ)=(1250025534890899/1250000000000000 : ℝ) by norm_num, show 1+2*(2273782664645513/50000000000000000000 : ℝ)=(25002273782664645513/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2802458757697129/10000000000000000000 : ℝ)+(2273782664645513/50000000000000000000 : ℝ) ≤ ((1067798586228298657/1068000000000000000 : ℝ)+(527233780079/534000000000000 : ℝ)*((637/4000 : ℝ)+(2117/20000 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (1067798586228298657/1068000000000000000 : ℝ)+(527233780079/534000000000000 : ℝ)*((637/4000 : ℝ)+(2117/20000 : ℝ))=(10000731512907271/10000000000000000 : ℝ) by norm_num, show 1+(2802458757697129/10000000000000000000 : ℝ)+(2273782664645513/50000000000000000000 : ℝ)=(25008143038226565579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2802458757697129/10000000000000000000 : ℝ) ≤ ((1067798586228298657/1068000000000000000 : ℝ)+2*(527233780079/534000000000000 : ℝ)*(637/4000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (1067798586228298657/1068000000000000000 : ℝ)+2*(527233780079/534000000000000 : ℝ)*(637/4000 : ℝ)=(200025174933747/200000000000000 : ℝ) by norm_num, show 1+2*(2802458757697129/10000000000000000000 : ℝ)=(5002802458757697129/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1067798586228298657/1068000000000000000 : ℝ)*(X 1 0+X 2 0)+(527233780079/534000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (637/4000 : ℝ)) (c := (1067798586228298657/1068000000000000000 : ℝ)) (alpha := (527233780079/534000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1067798586228298657/1068000000000000000 : ℝ)*(X 0 1+X 2 1)+(527233780079/534000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (637/4000 : ℝ)) (c := (1067798586228298657/1068000000000000000 : ℝ)) (alpha := (527233780079/534000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1067798586228298657/1068000000000000000 : ℝ)*(X 0 2+X 1 2)+(527233780079/534000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (637/4000 : ℝ)) (c := (1067798586228298657/1068000000000000000 : ℝ)) (alpha := (527233780079/534000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1838477127/10000000000 : ℝ)*X 0 0+(5433246771/10000000000 : ℝ)*X 0 1+(5216241629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351140699/10000000000 : ℝ)*X 1 0+(-77985333/400000000 : ℝ)*X 1 1+(2608120761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668892609/1250000000 : ℝ)*X 2 0+(5216241247/10000000000 : ℝ)*X 2 1+(-1949633459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260301453/10000000000 : ℝ)*X 0 0+(4016892463/10000000000 : ℝ)*X 0 1+(1128978377/2500000000 : ℝ)*X 0 2+(4260301453/10000000000 : ℝ)*X 1 0+(4016892463/10000000000 : ℝ)*X 1 1+(1128978377/2500000000 : ℝ)*X 1 2+(4260301453/10000000000 : ℝ)*X 2 0+(4016892463/10000000000 : ℝ)*X 2 1+(1128978377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367701529/2000000000 : ℝ)*X 0 0+(5217388821/10000000000 : ℝ)*X 0 1+(1086418133/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647003631/5000000000 : ℝ)*X 1 0+(-1733784439/10000000000 : ℝ)*X 1 1+(5432090659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294007661/10000000000 : ℝ)*X 2 0+(5432090509/10000000000 : ℝ)*X 2 1+(-866892049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065092699/2500000000 : ℝ)*X 0 0+(2256637523/5000000000 : ℝ)*X 0 1+(4019550887/10000000000 : ℝ)*X 0 2+(1065092699/2500000000 : ℝ)*X 1 0+(2256637523/5000000000 : ℝ)*X 1 1+(4019550887/10000000000 : ℝ)*X 1 2+(1065092699/2500000000 : ℝ)*X 2 0+(2256637523/5000000000 : ℝ)*X 2 1+(4019550887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4637667911762073987308123/890000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350346001/100000000000000 : ℝ)*(base19) + (60179921/10000000000000 : ℝ)*(base23) + (13404439/25000000000000 : ℝ)*(lower2) + (14847501/50000000000000 : ℝ)*(upper3) + (6778259/6250000000000 : ℝ)*(lower4) + (165303129997513/5000000000000 : ℝ)*(major0) + (165303129997513/5000000000000 : ℝ)*(major1) + (165303129997513/5000000000000 : ℝ)*(major2) + (4608190868689867/100000000000000 : ℝ)*(sp0) + (2304097311402017/50000000000000 : ℝ)*(sp1) + (184327774854033/4000000000000 : ℝ)*(sp2) + (80157063561937/4000000000000 : ℝ)*(sp3) + (513057521/12500000000000 : ℝ)*(sp4) + (27712053/800000000000 : ℝ)*(sp7) + (40078601061101/2000000000000 : ℝ)*(f.failure) + (2304097486575017/50000000000000 : ℝ)*(f.sum) + (8661198821267/1335000000000000000000000000 : ℝ)*base65 + (27209864681105959/5340000000000000000000000000000 : ℝ)*base68 + (38078924326625959/5340000000000000000000000000000 : ℝ)*base70 + (21102575465645959/5340000000000000000000000000000 : ℝ)*base72 + (1612780432201/667500000000000000000000000 : ℝ)*base73 + (37154541944525959/5340000000000000000000000000000 : ℝ)*base76 + (51378451111205959/5340000000000000000000000000000 : ℝ)*base78 + (63689152943705959/5340000000000000000000000000000 : ℝ)*base80 + (891752852473/1335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (167571/100000000000000000000 : ℝ)*base89 + (167571/100000000000000000000 : ℝ)*base91 + (167571/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4419598038932767351276209/1112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29718791/12500000000000 : ℝ)*(base19) + (362605733/50000000000000 : ℝ)*(base23) + (13367139/100000000000000 : ℝ)*(upper2) + (47018047/50000000000000 : ℝ)*(upper3) + (33730983/100000000000000 : ℝ)*(upper5) + (208845203717263/6250000000000 : ℝ)*(major0) + (208845203717263/6250000000000 : ℝ)*(major1) + (208845203717263/6250000000000 : ℝ)*(major2) + (545358993/100000000000000 : ℝ)*(sp1) + (2711726853/25000000000000 : ℝ)*(sp2) + (4657622281509243/100000000000000 : ℝ)*(sp4) + (2328810749199961/50000000000000 : ℝ)*(sp5) + (931522141878073/20000000000000 : ℝ)*(sp6) + (2025424105020753/100000000000000 : ℝ)*(sp7) + (2025424105020753/100000000000000 : ℝ)*(f.failure) + (4657622281509243/100000000000000 : ℝ)*(f.sum) + (8185061306333/6675000000000000000000000000 : ℝ)*base65 + (11137935633005209/6675000000000000000000000000000 : ℝ)*base68 + (50621351330619791/6675000000000000000000000000000 : ℝ)*base69 + (16894281439344791/6675000000000000000000000000000 : ℝ)*base71 + (26270671269517/6675000000000000000000000000 : ℝ)*base74 + (34509774676044791/6675000000000000000000000000000 : ℝ)*base75 + (770037112805209/6675000000000000000000000000000 : ℝ)*base78 + (26772085759944791/6675000000000000000000000000000 : ℝ)*base79 + (8242617294833/6675000000000000000000000000 : ℝ)*base81 + (41008337/5000000000000000000000 : ℝ)*base90 + (41008337/5000000000000000000000 : ℝ)*base92 + (41008337/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1532_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (637/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10941/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1532_s4_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-919413387/5000000000 : ℝ)*x 0 + (5430936557/10000000000 : ℝ)*x 1 + (2609160233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (919413387/5000000000 : ℝ)^4561 ≤ (1407756019977/12500000000000 : ℝ)^3537 := by
    have hnat : (919413387 : ℕ)^4561*12500000000000^3537 ≤ 1407756019977^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919413387 5000000000 1407756019977 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430936557/10000000000 : ℝ)^4561 ≤ (22755589051623/50000000000000 : ℝ)^3537 := by
    have hnat : (5430936557 : ℕ)^4561*50000000000000^3537 ≤ 22755589051623^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430936557 10000000000 22755589051623 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609160233/5000000000 : ℝ)^4561 ≤ (21613386864331/50000000000000 : ℝ)^3537 := by
    have hnat : (2609160233 : ℕ)^4561*50000000000000^3537 ≤ 21613386864331^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609160233 5000000000 21613386864331 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-919413387/5000000000 : ℝ), (5430936557/10000000000 : ℝ), (2609160233/5000000000 : ℝ)] ![(1407756019977/12500000000000 : ℝ), (22755589051623/50000000000000 : ℝ), (21613386864331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-919413387/5000000000 : ℝ)|^4561 ≤ (1407756019977/12500000000000 : ℝ)^3537
        have hw : |(-919413387/5000000000 : ℝ)|=(919413387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430936557/10000000000 : ℝ)|^4561 ≤ (22755589051623/50000000000000 : ℝ)^3537
        have hw : |(5430936557/10000000000 : ℝ)|=(5430936557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609160233/5000000000 : ℝ)|^4561 ≤ (21613386864331/50000000000000 : ℝ)^3537
        have hw : |(2609160233/5000000000 : ℝ)|=(2609160233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350533521/10000000000 : ℝ)*x 0 + (-486920481/2500000000 : ℝ)*x 1 + (326145029/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350533521/10000000000 : ℝ)^4561 ≤ (44644204642481/100000000000000 : ℝ)^3537 := by
    have hnat : (5350533521 : ℕ)^4561*100000000000000^3537 ≤ 44644204642481^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350533521 10000000000 44644204642481 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486920481/2500000000 : ℝ)^4561 ≤ (12129021639767/100000000000000 : ℝ)^3537 := by
    have hnat : (486920481 : ℕ)^4561*100000000000000^3537 ≤ 12129021639767^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486920481 2500000000 12129021639767 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326145029/625000000 : ℝ)^4561 ≤ (43226773707299/100000000000000 : ℝ)^3537 := by
    have hnat : (326145029 : ℕ)^4561*100000000000000^3537 ≤ 43226773707299^3537*625000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326145029 625000000 43226773707299 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350533521/10000000000 : ℝ), (-486920481/2500000000 : ℝ), (326145029/625000000 : ℝ)] ![(44644204642481/100000000000000 : ℝ), (12129021639767/100000000000000 : ℝ), (43226773707299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350533521/10000000000 : ℝ)|^4561 ≤ (44644204642481/100000000000000 : ℝ)^3537
        have hw : |(5350533521/10000000000 : ℝ)|=(5350533521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486920481/2500000000 : ℝ)|^4561 ≤ (12129021639767/100000000000000 : ℝ)^3537
        have hw : |(-486920481/2500000000 : ℝ)|=(486920481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326145029/625000000 : ℝ)|^4561 ≤ (43226773707299/100000000000000 : ℝ)^3537
        have hw : |(326145029/625000000 : ℝ)|=(326145029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350533537/10000000000 : ℝ)*x 0 + (2609160231/5000000000 : ℝ)*x 1 + (-389536381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350533537/10000000000 : ℝ)^4561 ≤ (44644204814633/100000000000000 : ℝ)^3537 := by
    have hnat : (5350533537 : ℕ)^4561*100000000000000^3537 ≤ 44644204814633^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350533537 10000000000 44644204814633 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609160231/5000000000 : ℝ)^4561 ≤ (8645354737187/20000000000000 : ℝ)^3537 := by
    have hnat : (2609160231 : ℕ)^4561*20000000000000^3537 ≤ 8645354737187^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609160231 5000000000 8645354737187 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389536381/2000000000 : ℝ)^4561 ≤ (12129021487191/100000000000000 : ℝ)^3537 := by
    have hnat : (389536381 : ℕ)^4561*100000000000000^3537 ≤ 12129021487191^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389536381 2000000000 12129021487191 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350533537/10000000000 : ℝ), (2609160231/5000000000 : ℝ), (-389536381/2000000000 : ℝ)] ![(44644204814633/100000000000000 : ℝ), (8645354737187/20000000000000 : ℝ), (12129021487191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350533537/10000000000 : ℝ)|^4561 ≤ (44644204814633/100000000000000 : ℝ)^3537
        have hw : |(5350533537/10000000000 : ℝ)|=(5350533537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609160231/5000000000 : ℝ)|^4561 ≤ (8645354737187/20000000000000 : ℝ)^3537
        have hw : |(2609160231/5000000000 : ℝ)|=(2609160231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389536381/2000000000 : ℝ)|^4561 ≤ (12129021487191/100000000000000 : ℝ)^3537
        have hw : |(-389536381/2000000000 : ℝ)|=(389536381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130260373/5000000000 : ℝ)*x 0 + (62842411/156250000 : ℝ)*x 1 + (4510841733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130260373/5000000000 : ℝ)^4561 ≤ (33280366341061/100000000000000 : ℝ)^3537 := by
    have hnat : (2130260373 : ℕ)^4561*100000000000000^3537 ≤ 33280366341061^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130260373 5000000000 33280366341061 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62842411/156250000 : ℝ)^4561 ≤ (15448339695447/50000000000000 : ℝ)^3537 := by
    have hnat : (62842411 : ℕ)^4561*50000000000000^3537 ≤ 15448339695447^3537*156250000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62842411 156250000 15448339695447 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510841733/10000000000 : ℝ)^4561 ≤ (35822954264623/100000000000000 : ℝ)^3537 := by
    have hnat : (4510841733 : ℕ)^4561*100000000000000^3537 ≤ 35822954264623^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510841733 10000000000 35822954264623 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130260373/5000000000 : ℝ), (62842411/156250000 : ℝ), (4510841733/10000000000 : ℝ)] ![(33280366341061/100000000000000 : ℝ), (15448339695447/50000000000000 : ℝ), (35822954264623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130260373/5000000000 : ℝ)|^4561 ≤ (33280366341061/100000000000000 : ℝ)^3537
        have hw : |(2130260373/5000000000 : ℝ)|=(2130260373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62842411/156250000 : ℝ)|^4561 ≤ (15448339695447/50000000000000 : ℝ)^3537
        have hw : |(62842411/156250000 : ℝ)|=(62842411/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510841733/10000000000 : ℝ)|^4561 ≤ (35822954264623/100000000000000 : ℝ)^3537
        have hw : |(4510841733/10000000000 : ℝ)|=(4510841733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838855153/10000000000 : ℝ)*x 0 + (5219422153/10000000000 : ℝ)*x 1 + (2714913363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838855153/10000000000 : ℝ)^4561 ≤ (11262272289631/100000000000000 : ℝ)^3537 := by
    have hnat : (1838855153 : ℕ)^4561*100000000000000^3537 ≤ 11262272289631^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838855153 10000000000 11262272289631 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219422153/10000000000 : ℝ)^4561 ≤ (10809635540049/25000000000000 : ℝ)^3537 := by
    have hnat : (5219422153 : ℕ)^4561*25000000000000^3537 ≤ 10809635540049^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219422153 10000000000 10809635540049 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714913363/5000000000 : ℝ)^4561 ≤ (45499185530421/100000000000000 : ℝ)^3537 := by
    have hnat : (2714913363 : ℕ)^4561*100000000000000^3537 ≤ 45499185530421^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714913363 5000000000 45499185530421 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838855153/10000000000 : ℝ), (5219422153/10000000000 : ℝ), (2714913363/5000000000 : ℝ)] ![(11262272289631/100000000000000 : ℝ), (10809635540049/25000000000000 : ℝ), (45499185530421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838855153/10000000000 : ℝ)|^4561 ≤ (11262272289631/100000000000000 : ℝ)^3537
        have hw : |(-1838855153/10000000000 : ℝ)|=(1838855153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219422153/10000000000 : ℝ)|^4561 ≤ (10809635540049/25000000000000 : ℝ)^3537
        have hw : |(5219422153/10000000000 : ℝ)|=(5219422153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714913363/5000000000 : ℝ)|^4561 ≤ (45499185530421/100000000000000 : ℝ)^3537
        have hw : |(2714913363/5000000000 : ℝ)|=(2714913363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058911349/2000000000 : ℝ)*x 0 + (-1736175671/10000000000 : ℝ)*x 1 + (5429826733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058911349/2000000000 : ℝ)^4561 ≤ (4404283561917/10000000000000 : ℝ)^3537 := by
    have hnat : (1058911349 : ℕ)^4561*10000000000000^3537 ≤ 4404283561917^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058911349 2000000000 4404283561917 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1736175671/10000000000 : ℝ)^4561 ≤ (10457978762471/100000000000000 : ℝ)^3537 := by
    have hnat : (1736175671 : ℕ)^4561*100000000000000^3537 ≤ 10457978762471^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736175671 10000000000 10457978762471 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429826733/10000000000 : ℝ)^4561 ≤ (2274959280303/5000000000000 : ℝ)^3537 := by
    have hnat : (5429826733 : ℕ)^4561*5000000000000^3537 ≤ 2274959280303^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429826733 10000000000 2274959280303 5000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058911349/2000000000 : ℝ), (-1736175671/10000000000 : ℝ), (5429826733/10000000000 : ℝ)] ![(4404283561917/10000000000000 : ℝ), (10457978762471/100000000000000 : ℝ), (2274959280303/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058911349/2000000000 : ℝ)|^4561 ≤ (4404283561917/10000000000000 : ℝ)^3537
        have hw : |(1058911349/2000000000 : ℝ)|=(1058911349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1736175671/10000000000 : ℝ)|^4561 ≤ (10457978762471/100000000000000 : ℝ)^3537
        have hw : |(-1736175671/10000000000 : ℝ)|=(1736175671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429826733/10000000000 : ℝ)|^4561 ≤ (2274959280303/5000000000000 : ℝ)^3537
        have hw : |(5429826733/10000000000 : ℝ)|=(5429826733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21178227/40000000 : ℝ)*x 0 + (5429826743/10000000000 : ℝ)*x 1 + (-34723513/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21178227/40000000 : ℝ)^4561 ≤ (11010708918201/25000000000000 : ℝ)^3537 := by
    have hnat : (21178227 : ℕ)^4561*25000000000000^3537 ≤ 11010708918201^3537*40000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21178227 40000000 11010708918201 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429826743/10000000000 : ℝ)^4561 ≤ (22749592857057/50000000000000 : ℝ)^3537 := by
    have hnat : (5429826743 : ℕ)^4561*50000000000000^3537 ≤ 22749592857057^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429826743 10000000000 22749592857057 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34723513/200000000 : ℝ)^4561 ≤ (5228989299677/50000000000000 : ℝ)^3537 := by
    have hnat : (34723513 : ℕ)^4561*50000000000000^3537 ≤ 5228989299677^3537*200000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34723513 200000000 5228989299677 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21178227/40000000 : ℝ), (5429826743/10000000000 : ℝ), (-34723513/200000000 : ℝ)] ![(11010708918201/25000000000000 : ℝ), (22749592857057/50000000000000 : ℝ), (5228989299677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21178227/40000000 : ℝ)|^4561 ≤ (11010708918201/25000000000000 : ℝ)^3537
        have hw : |(21178227/40000000 : ℝ)|=(21178227/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429826743/10000000000 : ℝ)|^4561 ≤ (22749592857057/50000000000000 : ℝ)^3537
        have hw : |(5429826743/10000000000 : ℝ)|=(5429826743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34723513/200000000 : ℝ)|^4561 ≤ (5228989299677/50000000000000 : ℝ)^3537
        have hw : |(-34723513/200000000 : ℝ)|=(34723513/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s4_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260586033/10000000000 : ℝ)*x 0 + (281769273/625000000 : ℝ)*x 1 + (503058299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260586033/10000000000 : ℝ)^4561 ≤ (33281023965739/100000000000000 : ℝ)^3537 := by
    have hnat : (4260586033 : ℕ)^4561*100000000000000^3537 ≤ 33281023965739^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260586033 10000000000 33281023965739 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281769273/625000000 : ℝ)^4561 ≤ (178985064961/500000000000 : ℝ)^3537 := by
    have hnat : (281769273 : ℕ)^4561*500000000000^3537 ≤ 178985064961^3537*625000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281769273 625000000 178985064961 500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503058299/1250000000 : ℝ)^4561 ≤ (30921963027241/100000000000000 : ℝ)^3537 := by
    have hnat : (503058299 : ℕ)^4561*100000000000000^3537 ≤ 30921963027241^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503058299 1250000000 30921963027241 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260586033/10000000000 : ℝ), (281769273/625000000 : ℝ), (503058299/1250000000 : ℝ)] ![(33281023965739/100000000000000 : ℝ), (178985064961/500000000000 : ℝ), (30921963027241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260586033/10000000000 : ℝ)|^4561 ≤ (33281023965739/100000000000000 : ℝ)^3537
        have hw : |(4260586033/10000000000 : ℝ)|=(4260586033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281769273/625000000 : ℝ)|^4561 ≤ (178985064961/500000000000 : ℝ)^3537
        have hw : |(281769273/625000000 : ℝ)|=(281769273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503058299/1250000000 : ℝ)|^4561 ≤ (30921963027241/100000000000000 : ℝ)^3537
        have hw : |(503058299/1250000000 : ℝ)|=(503058299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2197/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10941/100000 : ℝ) ^ (4559/1024 : ℝ) ≤ (5269133526839191/100000000000000000000 : ℝ) := by
    have hpowers : (10941/100000 : ℝ)^4559 ≤ (5269133526839191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10941 : ℕ)^4559*100000000000000000000^1024 ≤ 5269133526839191^1024*100000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10941 100000 5269133526839191 100000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10941/100000 : ℝ)) (X := (5269133526839191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7769/50000 : ℝ) ^ (4559/1024 : ℝ) ≤ (12558594515827099/50000000000000000000 : ℝ) := by
    have hpowers : (7769/50000 : ℝ)^4559 ≤ (12558594515827099/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7769 : ℕ)^4559*50000000000000000000^1024 ≤ 12558594515827099^1024*50000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7769 50000 12558594515827099 50000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7769/50000 : ℝ)) (X := (12558594515827099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005269133526839191/50000000000000000000 : ℝ) ≤ (312507396595061/312500000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (50005269133526839191/50000000000000000000 : ℝ)^1024 ≤ (312507396595061/312500000000000 : ℝ)^4559 := by
      have hnat : (50005269133526839191 : ℕ)^1024*312500000000000^4559 ≤ 312507396595061^4559*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005269133526839191 50000000000000000000 312507396595061 312500000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312507396595061/312500000000000 : ℝ)) (X := (50005269133526839191/50000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030386322558493389/100000000000000000000 : ℝ) ≤ (10000682428807863/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (100030386322558493389/100000000000000000000 : ℝ)^1024 ≤ (10000682428807863/10000000000000000 : ℝ)^4559 := by
      have hnat : (100030386322558493389 : ℕ)^1024*10000000000000000^4559 ≤ 10000682428807863^4559*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030386322558493389 100000000000000000000 10000682428807863 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682428807863/10000000000000000 : ℝ)) (X := (100030386322558493389/100000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012558594515827099/25000000000000000000 : ℝ) ≤ (5000564083286887/5000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (25012558594515827099/25000000000000000000 : ℝ)^1024 ≤ (5000564083286887/5000000000000000 : ℝ)^4559 := by
      have hnat : (25012558594515827099 : ℕ)^1024*5000000000000000^4559 ≤ 5000564083286887^4559*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012558594515827099 25000000000000000000 5000564083286887 5000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000564083286887/5000000000000000 : ℝ)) (X := (25012558594515827099/25000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5269133526839191/100000000000000000000 : ℝ) ≤ ((22980667217463094421/22985000000000000000 : ℝ)+2*(445737765911/459700000000000 : ℝ)*(10941/100000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (22980667217463094421/22985000000000000000 : ℝ)+2*(445737765911/459700000000000 : ℝ)*(10941/100000 : ℝ)=(312507396595061/312500000000000 : ℝ) by norm_num, show 1+2*(5269133526839191/100000000000000000000 : ℝ)=(50005269133526839191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12558594515827099/50000000000000000000 : ℝ)+(5269133526839191/100000000000000000000 : ℝ) ≤ ((22980667217463094421/22985000000000000000 : ℝ)+(445737765911/459700000000000 : ℝ)*((7769/50000 : ℝ)+(10941/100000 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (22980667217463094421/22985000000000000000 : ℝ)+(445737765911/459700000000000 : ℝ)*((7769/50000 : ℝ)+(10941/100000 : ℝ))=(10000682428807863/10000000000000000 : ℝ) by norm_num, show 1+(12558594515827099/50000000000000000000 : ℝ)+(5269133526839191/100000000000000000000 : ℝ)=(100030386322558493389/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12558594515827099/50000000000000000000 : ℝ) ≤ ((22980667217463094421/22985000000000000000 : ℝ)+2*(445737765911/459700000000000 : ℝ)*(7769/50000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (22980667217463094421/22985000000000000000 : ℝ)+2*(445737765911/459700000000000 : ℝ)*(7769/50000 : ℝ)=(5000564083286887/5000000000000000 : ℝ) by norm_num, show 1+2*(12558594515827099/50000000000000000000 : ℝ)=(25012558594515827099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22980667217463094421/22985000000000000000 : ℝ)*(X 1 0+X 2 0)+(445737765911/459700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (10941/100000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (22980667217463094421/22985000000000000000 : ℝ)) (alpha := (445737765911/459700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22980667217463094421/22985000000000000000 : ℝ)*(X 0 1+X 2 1)+(445737765911/459700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (10941/100000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (22980667217463094421/22985000000000000000 : ℝ)) (alpha := (445737765911/459700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22980667217463094421/22985000000000000000 : ℝ)*(X 0 2+X 1 2)+(445737765911/459700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (10941/100000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (22980667217463094421/22985000000000000000 : ℝ)) (alpha := (445737765911/459700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-919413387/5000000000 : ℝ)*X 0 0+(5430936557/10000000000 : ℝ)*X 0 1+(2609160233/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350533521/10000000000 : ℝ)*X 1 0+(-486920481/2500000000 : ℝ)*X 1 1+(326145029/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350533537/10000000000 : ℝ)*X 2 0+(2609160231/5000000000 : ℝ)*X 2 1+(-389536381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130260373/5000000000 : ℝ)*X 0 0+(62842411/156250000 : ℝ)*X 0 1+(4510841733/10000000000 : ℝ)*X 0 2+(2130260373/5000000000 : ℝ)*X 1 0+(62842411/156250000 : ℝ)*X 1 1+(4510841733/10000000000 : ℝ)*X 1 2+(2130260373/5000000000 : ℝ)*X 2 0+(62842411/156250000 : ℝ)*X 2 1+(4510841733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1838855153/10000000000 : ℝ)*X 0 0+(5219422153/10000000000 : ℝ)*X 0 1+(2714913363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058911349/2000000000 : ℝ)*X 1 0+(-1736175671/10000000000 : ℝ)*X 1 1+(5429826733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21178227/40000000 : ℝ)*X 2 0+(5429826743/10000000000 : ℝ)*X 2 1+(-34723513/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260586033/10000000000 : ℝ)*X 0 0+(281769273/625000000 : ℝ)*X 0 1+(503058299/1250000000 : ℝ)*X 0 2+(4260586033/10000000000 : ℝ)*X 1 0+(281769273/625000000 : ℝ)*X 1 1+(503058299/1250000000 : ℝ)*X 1 2+(4260586033/10000000000 : ℝ)*X 2 0+(281769273/625000000 : ℝ)*X 2 1+(503058299/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1398841970504035463294527167/143656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1695495527/100000000000000 : ℝ)*(base19) + (1604896463/100000000000000 : ℝ)*(base23) + (28000359/50000000000000 : ℝ)*(lower2) + (57521051/25000000000000 : ℝ)*(upper3) + (174621839/100000000000000 : ℝ)*(upper5) + (843585689428109/25000000000000 : ℝ)*(major0) + (843585689428109/25000000000000 : ℝ)*(major1) + (843585689428109/25000000000000 : ℝ)*(major2) + (2351670266746491/50000000000000 : ℝ)*(sp0) + (4703366246488683/100000000000000 : ℝ)*(sp1) + (4703366337087747/100000000000000 : ℝ)*(sp2) + (1022652368320403/50000000000000 : ℝ)*(sp3) + (6852122807/25000000000000 : ℝ)*(sp4) + (12512219013/100000000000000 : ℝ)*(sp7) + (2045317248859819/100000000000000 : ℝ)*(f.failure) + (470336794198421/10000000000000 : ℝ)*(f.sum) + (46563196618509/22985000000000000000000000000 : ℝ)*base66 + (5630600261876820111/574625000000000000000000000000000 : ℝ)*base68 + (1181354797911179889/574625000000000000000000000000000 : ℝ)*base69 + (1489762227946070111/574625000000000000000000000000000 : ℝ)*base72 + (15693074692883/2873125000000000000000000000 : ℝ)*base74 + (8630010678574320111/574625000000000000000000000000000 : ℝ)*base76 + (7406462262535070111/574625000000000000000000000000000 : ℝ)*base78 + (8551684760730820111/574625000000000000000000000000000 : ℝ)*base80 + (79023600060081/22985000000000000000000000000 : ℝ)*base81 + (22465749/5000000000000000000000 : ℝ)*base89 + (22465749/5000000000000000000000 : ℝ)*base91 + (22465749/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1730192767029749240357989779/287312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (944619121/100000000000000 : ℝ)*(base19) + (521659659/50000000000000 : ℝ)*(base23) + (132426289/100000000000000 : ℝ)*(upper3) + (310541/800000000000 : ℝ)*(lower4) + (14943863/12500000000000 : ℝ)*(upper5) + (1704884520120767/50000000000000 : ℝ)*(major0) + (1704884520120767/50000000000000 : ℝ)*(major1) + (1704884520120767/50000000000000 : ℝ)*(major2) + (7153639949/50000000000000 : ℝ)*(sp1) + (2035462517/12500000000000 : ℝ)*(sp2) + (59409342701593/1250000000000 : ℝ)*(sp4) + (237636608211421/5000000000000 : ℝ)*(sp5) + (950546017821597/20000000000000 : ℝ)*(sp6) + (516697615905661/25000000000000 : ℝ)*(sp7) + (516697615905661/25000000000000 : ℝ)*(f.failure) + (59409342701593/1250000000000 : ℝ)*(f.sum) + (80042268802727/11492500000000000000000000000 : ℝ)*base65 + (104571544185209093/1149250000000000000000000000000000 : ℝ)*base68 + (2353698827346790907/1149250000000000000000000000000000 : ℝ)*base69 + (9640353969388290907/1149250000000000000000000000000000 : ℝ)*base71 + (33551446079387/11492500000000000000000000000 : ℝ)*base73 + (2342639488865790907/1149250000000000000000000000000000 : ℝ)*base75 + (9445032008806290907/1149250000000000000000000000000000 : ℝ)*base77 + (3433225219290040907/1149250000000000000000000000000000 : ℝ)*base79 + (34406225368811/5746250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13204669/1250000000000000000000 : ℝ)*base90 + (13204669/1250000000000000000000 : ℝ)*base92 + (13204669/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1532_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1532_s5_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-229858339/1250000000 : ℝ)*x 0 + (5430673023/10000000000 : ℝ)*x 1 + (1304639383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229858339/1250000000 : ℝ)^4561 ≤ (5631181789917/50000000000000 : ℝ)^3537 := by
    have hnat : (229858339 : ℕ)^4561*50000000000000^3537 ≤ 5631181789917^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229858339 1250000000 5631181789917 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430673023/10000000000 : ℝ)^4561 ≤ (45508330352567/100000000000000 : ℝ)^3537 := by
    have hnat : (5430673023 : ℕ)^4561*100000000000000^3537 ≤ 45508330352567^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430673023 10000000000 45508330352567 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304639383/2500000000 : ℝ)^4561 ≤ (21614653026173/50000000000000 : ℝ)^3537 := by
    have hnat : (1304639383 : ℕ)^4561*50000000000000^3537 ≤ 21614653026173^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304639383 2500000000 21614653026173 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-229858339/1250000000 : ℝ), (5430673023/10000000000 : ℝ), (1304639383/2500000000 : ℝ)] ![(5631181789917/50000000000000 : ℝ), (45508330352567/100000000000000 : ℝ), (21614653026173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-229858339/1250000000 : ℝ)|^4561 ≤ (5631181789917/50000000000000 : ℝ)^3537
        have hw : |(-229858339/1250000000 : ℝ)|=(229858339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430673023/10000000000 : ℝ)|^4561 ≤ (45508330352567/100000000000000 : ℝ)^3537
        have hw : |(5430673023/10000000000 : ℝ)|=(5430673023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304639383/2500000000 : ℝ)|^4561 ≤ (21614653026173/50000000000000 : ℝ)^3537
        have hw : |(1304639383/2500000000 : ℝ)|=(1304639383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350463121/10000000000 : ℝ)*x 0 + (-973730091/5000000000 : ℝ)*x 1 + (521855807/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350463121/10000000000 : ℝ)^4561 ≤ (44643447173513/100000000000000 : ℝ)^3537 := by
    have hnat : (5350463121 : ℕ)^4561*100000000000000^3537 ≤ 44643447173513^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350463121 10000000000 44643447173513 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973730091/5000000000 : ℝ)^4561 ≤ (2425448202063/20000000000000 : ℝ)^3537 := by
    have hnat : (973730091 : ℕ)^4561*20000000000000^3537 ≤ 2425448202063^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973730091 5000000000 2425448202063 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521855807/1000000000 : ℝ)^4561 ≤ (8645862359853/20000000000000 : ℝ)^3537 := by
    have hnat : (521855807 : ℕ)^4561*20000000000000^3537 ≤ 8645862359853^3537*1000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521855807 1000000000 8645862359853 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350463121/10000000000 : ℝ), (-973730091/5000000000 : ℝ), (521855807/1000000000 : ℝ)] ![(44643447173513/100000000000000 : ℝ), (2425448202063/20000000000000 : ℝ), (8645862359853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350463121/10000000000 : ℝ)|^4561 ≤ (44643447173513/100000000000000 : ℝ)^3537
        have hw : |(5350463121/10000000000 : ℝ)|=(5350463121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973730091/5000000000 : ℝ)|^4561 ≤ (2425448202063/20000000000000 : ℝ)^3537
        have hw : |(-973730091/5000000000 : ℝ)|=(973730091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521855807/1000000000 : ℝ)|^4561 ≤ (8645862359853/20000000000000 : ℝ)^3537
        have hw : |(521855807/1000000000 : ℝ)|=(521855807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675231613/5000000000 : ℝ)*x 0 + (130463963/250000000 : ℝ)*x 1 + (-973729721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675231613/5000000000 : ℝ)^4561 ≤ (22321724151629/50000000000000 : ℝ)^3537 := by
    have hnat : (2675231613 : ℕ)^4561*50000000000000^3537 ≤ 22321724151629^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675231613 5000000000 22321724151629 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130463963/250000000 : ℝ)^4561 ≤ (5403664575771/12500000000000 : ℝ)^3537 := by
    have hnat : (130463963 : ℕ)^4561*12500000000000^3537 ≤ 5403664575771^3537*250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130463963 250000000 5403664575771 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973729721/5000000000 : ℝ)^4561 ≤ (3031808767019/25000000000000 : ℝ)^3537 := by
    have hnat : (973729721 : ℕ)^4561*25000000000000^3537 ≤ 3031808767019^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973729721 5000000000 3031808767019 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675231613/5000000000 : ℝ), (130463963/250000000 : ℝ), (-973729721/5000000000 : ℝ)] ![(22321724151629/50000000000000 : ℝ), (5403664575771/12500000000000 : ℝ), (3031808767019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675231613/5000000000 : ℝ)|^4561 ≤ (22321724151629/50000000000000 : ℝ)^3537
        have hw : |(2675231613/5000000000 : ℝ)|=(2675231613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130463963/250000000 : ℝ)|^4561 ≤ (5403664575771/12500000000000 : ℝ)^3537
        have hw : |(130463963/250000000 : ℝ)|=(130463963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973729721/5000000000 : ℝ)|^4561 ≤ (3031808767019/25000000000000 : ℝ)^3537
        have hw : |(-973729721/5000000000 : ℝ)|=(973729721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260545179/10000000000 : ℝ)*x 0 + (4022487599/10000000000 : ℝ)*x 1 + (4510263111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260545179/10000000000 : ℝ)^4561 ≤ (33280612450109/100000000000000 : ℝ)^3537 := by
    have hnat : (4260545179 : ℕ)^4561*100000000000000^3537 ≤ 33280612450109^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260545179 10000000000 33280612450109 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022487599/10000000000 : ℝ)^4561 ≤ (3862794830331/12500000000000 : ℝ)^3537 := by
    have hnat : (4022487599 : ℕ)^4561*12500000000000^3537 ≤ 3862794830331^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022487599 10000000000 3862794830331 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510263111/10000000000 : ℝ)^4561 ≤ (17908514445779/50000000000000 : ℝ)^3537 := by
    have hnat : (4510263111 : ℕ)^4561*50000000000000^3537 ≤ 17908514445779^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510263111 10000000000 17908514445779 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260545179/10000000000 : ℝ), (4022487599/10000000000 : ℝ), (4510263111/10000000000 : ℝ)] ![(33280612450109/100000000000000 : ℝ), (3862794830331/12500000000000 : ℝ), (17908514445779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260545179/10000000000 : ℝ)|^4561 ≤ (33280612450109/100000000000000 : ℝ)^3537
        have hw : |(4260545179/10000000000 : ℝ)|=(4260545179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022487599/10000000000 : ℝ)|^4561 ≤ (3862794830331/12500000000000 : ℝ)^3537
        have hw : |(4022487599/10000000000 : ℝ)|=(4022487599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510263111/10000000000 : ℝ)|^4561 ≤ (17908514445779/50000000000000 : ℝ)^3537
        have hw : |(4510263111/10000000000 : ℝ)|=(4510263111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838895319/10000000000 : ℝ)*x 0 + (1043930831/2000000000 : ℝ)*x 1 + (5429568003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838895319/10000000000 : ℝ)^4561 ≤ (11262589511757/100000000000000 : ℝ)^3537 := by
    have hnat : (1838895319 : ℕ)^4561*100000000000000^3537 ≤ 11262589511757^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838895319 10000000000 11262589511757 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043930831/2000000000 : ℝ)^4561 ≤ (10810255135417/25000000000000 : ℝ)^3537 := by
    have hnat : (1043930831 : ℕ)^4561*25000000000000^3537 ≤ 10810255135417^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043930831 2000000000 10810255135417 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429568003/10000000000 : ℝ)^4561 ≤ (1421762185391/3125000000000 : ℝ)^3537 := by
    have hnat : (5429568003 : ℕ)^4561*3125000000000^3537 ≤ 1421762185391^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429568003 10000000000 1421762185391 3125000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838895319/10000000000 : ℝ), (1043930831/2000000000 : ℝ), (5429568003/10000000000 : ℝ)] ![(11262589511757/100000000000000 : ℝ), (10810255135417/25000000000000 : ℝ), (1421762185391/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838895319/10000000000 : ℝ)|^4561 ≤ (11262589511757/100000000000000 : ℝ)^3537
        have hw : |(-1838895319/10000000000 : ℝ)|=(1838895319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043930831/2000000000 : ℝ)|^4561 ≤ (10810255135417/25000000000000 : ℝ)^3537
        have hw : |(1043930831/2000000000 : ℝ)|=(1043930831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429568003/10000000000 : ℝ)|^4561 ≤ (1421762185391/3125000000000 : ℝ)^3537
        have hw : |(5429568003/10000000000 : ℝ)|=(5429568003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294619173/10000000000 : ℝ)*x 0 + (-173644937/1000000000 : ℝ)*x 1 + (1085913601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294619173/10000000000 : ℝ)^4561 ≤ (22021752636873/50000000000000 : ℝ)^3537 := by
    have hnat : (5294619173 : ℕ)^4561*50000000000000^3537 ≤ 22021752636873^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294619173 10000000000 22021752636873 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173644937/1000000000 : ℝ)^4561 ≤ (653756547337/6250000000000 : ℝ)^3537 := by
    have hnat : (173644937 : ℕ)^4561*6250000000000^3537 ≤ 653756547337^3537*1000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173644937 1000000000 653756547337 6250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085913601/2000000000 : ℝ)^4561 ≤ (45496389954123/100000000000000 : ℝ)^3537 := by
    have hnat : (1085913601 : ℕ)^4561*100000000000000^3537 ≤ 45496389954123^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085913601 2000000000 45496389954123 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294619173/10000000000 : ℝ), (-173644937/1000000000 : ℝ), (1085913601/2000000000 : ℝ)] ![(22021752636873/50000000000000 : ℝ), (653756547337/6250000000000 : ℝ), (45496389954123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294619173/10000000000 : ℝ)|^4561 ≤ (22021752636873/50000000000000 : ℝ)^3537
        have hw : |(5294619173/10000000000 : ℝ)|=(5294619173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173644937/1000000000 : ℝ)|^4561 ≤ (653756547337/6250000000000 : ℝ)^3537
        have hw : |(-173644937/1000000000 : ℝ)|=(173644937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085913601/2000000000 : ℝ)|^4561 ≤ (45496389954123/100000000000000 : ℝ)^3537
        have hw : |(1085913601/2000000000 : ℝ)|=(1085913601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647309587/5000000000 : ℝ)*x 0 + (2714784001/5000000000 : ℝ)*x 1 + (-1736449373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647309587/5000000000 : ℝ)^4561 ≤ (5505438160559/12500000000000 : ℝ)^3537 := by
    have hnat : (2647309587 : ℕ)^4561*12500000000000^3537 ≤ 5505438160559^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647309587 5000000000 5505438160559 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714784001/5000000000 : ℝ)^4561 ≤ (45496389921707/100000000000000 : ℝ)^3537 := by
    have hnat : (2714784001 : ℕ)^4561*100000000000000^3537 ≤ 45496389921707^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714784001 5000000000 45496389921707 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736449373/10000000000 : ℝ)^4561 ≤ (2092020956139/20000000000000 : ℝ)^3537 := by
    have hnat : (1736449373 : ℕ)^4561*20000000000000^3537 ≤ 2092020956139^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736449373 10000000000 2092020956139 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647309587/5000000000 : ℝ), (2714784001/5000000000 : ℝ), (-1736449373/10000000000 : ℝ)] ![(5505438160559/12500000000000 : ℝ), (45496389921707/100000000000000 : ℝ), (2092020956139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647309587/5000000000 : ℝ)|^4561 ≤ (5505438160559/12500000000000 : ℝ)^3537
        have hw : |(2647309587/5000000000 : ℝ)|=(2647309587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714784001/5000000000 : ℝ)|^4561 ≤ (45496389921707/100000000000000 : ℝ)^3537
        have hw : |(2714784001/5000000000 : ℝ)|=(2714784001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736449373/10000000000 : ℝ)|^4561 ≤ (2092020956139/20000000000000 : ℝ)^3537
        have hw : |(-1736449373/10000000000 : ℝ)|=(1736449373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s5_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260610299/10000000000 : ℝ)*x 0 + (4507741233/10000000000 : ℝ)*x 1 + (805005557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260610299/10000000000 : ℝ)^4561 ≤ (33281268393711/100000000000000 : ℝ)^3537 := by
    have hnat : (4260610299 : ℕ)^4561*100000000000000^3537 ≤ 33281268393711^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260610299 10000000000 33281268393711 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507741233/10000000000 : ℝ)^4561 ≤ (17895603097031/50000000000000 : ℝ)^3537 := by
    have hnat : (4507741233 : ℕ)^4561*50000000000000^3537 ≤ 17895603097031^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507741233 10000000000 17895603097031 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805005557/2000000000 : ℝ)^4561 ≤ (30927525392787/100000000000000 : ℝ)^3537 := by
    have hnat : (805005557 : ℕ)^4561*100000000000000^3537 ≤ 30927525392787^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805005557 2000000000 30927525392787 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260610299/10000000000 : ℝ), (4507741233/10000000000 : ℝ), (805005557/2000000000 : ℝ)] ![(33281268393711/100000000000000 : ℝ), (17895603097031/50000000000000 : ℝ), (30927525392787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260610299/10000000000 : ℝ)|^4561 ≤ (33281268393711/100000000000000 : ℝ)^3537
        have hw : |(4260610299/10000000000 : ℝ)|=(4260610299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507741233/10000000000 : ℝ)|^4561 ≤ (17895603097031/50000000000000 : ℝ)^3537
        have hw : |(4507741233/10000000000 : ℝ)|=(4507741233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805005557/2000000000 : ℝ)|^4561 ≤ (30927525392787/100000000000000 : ℝ)^3537
        have hw : |(805005557/2000000000 : ℝ)|=(805005557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1099/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2197/20000 : ℝ) ^ (4559/1024 : ℝ) ≤ (1341033108348859/25000000000000000000 : ℝ) := by
    have hpowers : (2197/20000 : ℝ)^4559 ≤ (1341033108348859/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2197 : ℕ)^4559*25000000000000000000^1024 ≤ 1341033108348859^1024*20000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2197 20000 1341033108348859 25000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2197/20000 : ℝ)) (X := (1341033108348859/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4559/1024 : ℝ) ≤ (24773575130303527/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4559 ≤ (24773575130303527/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4559*100000000000000000000^1024 ≤ 24773575130303527^1024*10000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 24773575130303527 100000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (24773575130303527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501341033108348859/12500000000000000000 : ℝ) ≤ (10000240958243553/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (12501341033108348859/12500000000000000000 : ℝ)^1024 ≤ (10000240958243553/10000000000000000 : ℝ)^4559 := by
      have hnat : (12501341033108348859 : ℕ)^1024*10000000000000000^4559 ≤ 10000240958243553^4559*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501341033108348859 12500000000000000000 10000240958243553 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000240958243553/10000000000000000 : ℝ)) (X := (12501341033108348859/12500000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030137707563698963/100000000000000000000 : ℝ) ≤ (10000676845960013/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (100030137707563698963/100000000000000000000 : ℝ)^1024 ≤ (10000676845960013/10000000000000000 : ℝ)^4559 := by
      have hnat : (100030137707563698963 : ℕ)^1024*10000000000000000^4559 ≤ 10000676845960013^4559*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030137707563698963 100000000000000000000 10000676845960013 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000676845960013/10000000000000000 : ℝ)) (X := (100030137707563698963/100000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024773575130303527/50000000000000000000 : ℝ) ≤ (10001112733676473/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (50024773575130303527/50000000000000000000 : ℝ)^1024 ≤ (10001112733676473/10000000000000000 : ℝ)^4559 := by
      have hnat : (50024773575130303527 : ℕ)^1024*10000000000000000^4559 ≤ 10001112733676473^4559*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024773575130303527 50000000000000000000 10001112733676473 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001112733676473/10000000000000000 : ℝ)) (X := (50024773575130303527/50000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1341033108348859/25000000000000000000 : ℝ) ≤ ((9008301812751316013/9010000000000000000 : ℝ)+2*(21794385823/22525000000000 : ℝ)*(2197/20000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (9008301812751316013/9010000000000000000 : ℝ)+2*(21794385823/22525000000000 : ℝ)*(2197/20000 : ℝ)=(10000240958243553/10000000000000000 : ℝ) by norm_num, show 1+2*(1341033108348859/25000000000000000000 : ℝ)=(12501341033108348859/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24773575130303527/100000000000000000000 : ℝ)+(1341033108348859/25000000000000000000 : ℝ) ≤ ((9008301812751316013/9010000000000000000 : ℝ)+(21794385823/22525000000000 : ℝ)*((1549/10000 : ℝ)+(2197/20000 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (9008301812751316013/9010000000000000000 : ℝ)+(21794385823/22525000000000 : ℝ)*((1549/10000 : ℝ)+(2197/20000 : ℝ))=(10000676845960013/10000000000000000 : ℝ) by norm_num, show 1+(24773575130303527/100000000000000000000 : ℝ)+(1341033108348859/25000000000000000000 : ℝ)=(100030137707563698963/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24773575130303527/100000000000000000000 : ℝ) ≤ ((9008301812751316013/9010000000000000000 : ℝ)+2*(21794385823/22525000000000 : ℝ)*(1549/10000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (9008301812751316013/9010000000000000000 : ℝ)+2*(21794385823/22525000000000 : ℝ)*(1549/10000 : ℝ)=(10001112733676473/10000000000000000 : ℝ) by norm_num, show 1+2*(24773575130303527/100000000000000000000 : ℝ)=(50024773575130303527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9008301812751316013/9010000000000000000 : ℝ)*(X 1 0+X 2 0)+(21794385823/22525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (9008301812751316013/9010000000000000000 : ℝ)) (alpha := (21794385823/22525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9008301812751316013/9010000000000000000 : ℝ)*(X 0 1+X 2 1)+(21794385823/22525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (9008301812751316013/9010000000000000000 : ℝ)) (alpha := (21794385823/22525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9008301812751316013/9010000000000000000 : ℝ)*(X 0 2+X 1 2)+(21794385823/22525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (9008301812751316013/9010000000000000000 : ℝ)) (alpha := (21794385823/22525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-229858339/1250000000 : ℝ)*X 0 0+(5430673023/10000000000 : ℝ)*X 0 1+(1304639383/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350463121/10000000000 : ℝ)*X 1 0+(-973730091/5000000000 : ℝ)*X 1 1+(521855807/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675231613/5000000000 : ℝ)*X 2 0+(130463963/250000000 : ℝ)*X 2 1+(-973729721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260545179/10000000000 : ℝ)*X 0 0+(4022487599/10000000000 : ℝ)*X 0 1+(4510263111/10000000000 : ℝ)*X 0 2+(4260545179/10000000000 : ℝ)*X 1 0+(4022487599/10000000000 : ℝ)*X 1 1+(4510263111/10000000000 : ℝ)*X 1 2+(4260545179/10000000000 : ℝ)*X 2 0+(4022487599/10000000000 : ℝ)*X 2 1+(4510263111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1838895319/10000000000 : ℝ)*X 0 0+(1043930831/2000000000 : ℝ)*X 0 1+(5429568003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294619173/10000000000 : ℝ)*X 1 0+(-173644937/1000000000 : ℝ)*X 1 1+(1085913601/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647309587/5000000000 : ℝ)*X 2 0+(2714784001/5000000000 : ℝ)*X 2 1+(-1736449373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260610299/10000000000 : ℝ)*X 0 0+(4507741233/10000000000 : ℝ)*X 0 1+(805005557/2000000000 : ℝ)*X 0 2+(4260610299/10000000000 : ℝ)*X 1 0+(4507741233/10000000000 : ℝ)*X 1 1+(805005557/2000000000 : ℝ)*X 1 2+(4260610299/10000000000 : ℝ)*X 2 0+(4507741233/10000000000 : ℝ)*X 2 1+(805005557/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6522817717395944864536388193/450500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (808534541/100000000000000 : ℝ)*(base19) + (509843629/100000000000000 : ℝ)*(base23) + (222308567/100000000000000 : ℝ)*(lower2) + (169366723/50000000000000 : ℝ)*(upper5) + (1691151351159881/50000000000000 : ℝ)*(major0) + (1691151351159881/50000000000000 : ℝ)*(major1) + (3382302702319763/100000000000000 : ℝ)*(major2) + (471443018048021/10000000000000 : ℝ)*(sp0) + (4714459713286977/100000000000000 : ℝ)*(sp1) + (2357231169341567/50000000000000 : ℝ)*(sp2) + (2050133698026877/100000000000000 : ℝ)*(sp3) + (32668046553/100000000000000 : ℝ)*(sp4) + (465341049/20000000000000 : ℝ)*(sp5) + (4187725227/50000000000000 : ℝ)*(sp7) + (2050142073477331/100000000000000 : ℝ)*(f.failure) + (4714462848526763/100000000000000 : ℝ)*(f.sum) + (1260752553257/225250000000000000000000000 : ℝ)*base65 + (8508632592116725547/450500000000000000000000000000000 : ℝ)*base68 + (5886693108677335081/901000000000000000000000000000000 : ℝ)*base70 + (6431295407907225547/450500000000000000000000000000000 : ℝ)*base72 + (4760884167911/901000000000000000000000000 : ℝ)*base74 + (7158234076313335081/901000000000000000000000000000000 : ℝ)*base76 + (153548255194872091/26500000000000000000000000000000 : ℝ)*base78 + (521533556152872091/26500000000000000000000000000000 : ℝ)*base80 + (5211161891541/4505000000000000000000000000 : ℝ)*base82 + (64681901/5000000000000000000000 : ℝ)*base89 + (64681901/5000000000000000000000 : ℝ)*base91 + (14681901/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5121720492745241353968902313/450500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (920262069/50000000000000 : ℝ)*(base19) + (397878389/20000000000000 : ℝ)*(base23) + (151458291/25000000000000 : ℝ)*(lower1) + (236318643/100000000000000 : ℝ)*(upper3) + (536947/800000000000 : ℝ)*(lower4) + (234932803/100000000000000 : ℝ)*(upper5) + (3417719472848367/100000000000000 : ℝ)*(major0) + (3417719472848367/100000000000000 : ℝ)*(major1) + (3417719472848367/100000000000000 : ℝ)*(major2) + (1005037353/50000000000000 : ℝ)*(sp2) + (1190957261018887/25000000000000 : ℝ)*(sp4) + (476382720355141/10000000000000 : ℝ)*(sp5) + (4763825044608897/100000000000000 : ℝ)*(sp6) + (258951190331943/12500000000000 : ℝ)*(sp7) + (258951190331943/12500000000000 : ℝ)*(f.failure) + (1190957261018887/25000000000000 : ℝ)*(f.sum) + (988321647/2199707031250000000000000 : ℝ)*base66 + (1419414092307505837/53000000000000000000000000000000 : ℝ)*base68 + (211908259116494163/53000000000000000000000000000000 : ℝ)*base69 + (2836479538689505837/53000000000000000000000000000000 : ℝ)*base72 + (101414810939/70390625000000000000000000 : ℝ)*base74 + (425331499598494163/53000000000000000000000000000000 : ℝ)*base75 + (95095280001505837/53000000000000000000000000000000 : ℝ)*base78 + (377243661929505837/53000000000000000000000000000000 : ℝ)*base80 + (18982477450629/4505000000000000000000000000 : ℝ)*base81 + (1277847/625000000000000000000 : ℝ)*base90 + (1277847/625000000000000000000 : ℝ)*base92 + (1277847/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1532_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1532_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (637/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1532_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1532_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1532_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (637/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

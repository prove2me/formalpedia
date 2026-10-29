-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:53.764222+00:00
-- url     : https://prove2.me/submissions/8b9572ee-3b8a-47d5-b0e1-222efa9e9adb

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
theorem support_rectangle_w1508_s3_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873419929/10000000000 : ℝ)*x 0 + (1359295411/2500000000 : ℝ)*x 1 + (5214349919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873419929/10000000000 : ℝ)^4513 ≤ (5729649223733/50000000000000 : ℝ)^3489 := by
    have hnat : (1873419929 : ℕ)^4513*50000000000000^3489 ≤ 5729649223733^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873419929 10000000000 5729649223733 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359295411/2500000000 : ℝ)^4513 ≤ (11367048265277/25000000000000 : ℝ)^3489 := by
    have hnat : (1359295411 : ℕ)^4513*25000000000000^3489 ≤ 11367048265277^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359295411 2500000000 11367048265277 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214349919/10000000000 : ℝ)^4513 ≤ (21536254237737/50000000000000 : ℝ)^3489 := by
    have hnat : (5214349919 : ℕ)^4513*50000000000000^3489 ≤ 21536254237737^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214349919 10000000000 21536254237737 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873419929/10000000000 : ℝ), (1359295411/2500000000 : ℝ), (5214349919/10000000000 : ℝ)] ![(5729649223733/50000000000000 : ℝ), (11367048265277/25000000000000 : ℝ), (21536254237737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873419929/10000000000 : ℝ)|^4513 ≤ (5729649223733/50000000000000 : ℝ)^3489
        have hw : |(-1873419929/10000000000 : ℝ)|=(1873419929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359295411/2500000000 : ℝ)|^4513 ≤ (11367048265277/25000000000000 : ℝ)^3489
        have hw : |(1359295411/2500000000 : ℝ)|=(1359295411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214349919/10000000000 : ℝ)|^4513 ≤ (21536254237737/50000000000000 : ℝ)^3489
        have hw : |(5214349919/10000000000 : ℝ)|=(5214349919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167272149/312500000 : ℝ)*x 0 + (-1987633887/10000000000 : ℝ)*x 1 + (5214349899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167272149/312500000 : ℝ)^4513 ≤ (4455655893961/10000000000000 : ℝ)^3489 := by
    have hnat : (167272149 : ℕ)^4513*10000000000000^3489 ≤ 4455655893961^3489*312500000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167272149 312500000 4455655893961 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987633887/10000000000 : ℝ)^4513 ≤ (12370932788047/100000000000000 : ℝ)^3489 := by
    have hnat : (1987633887 : ℕ)^4513*100000000000000^3489 ≤ 12370932788047^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987633887 10000000000 12370932788047 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214349899/10000000000 : ℝ)^4513 ≤ (43072508261779/100000000000000 : ℝ)^3489 := by
    have hnat : (5214349899 : ℕ)^4513*100000000000000^3489 ≤ 43072508261779^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214349899 10000000000 43072508261779 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167272149/312500000 : ℝ), (-1987633887/10000000000 : ℝ), (5214349899/10000000000 : ℝ)] ![(4455655893961/10000000000000 : ℝ), (12370932788047/100000000000000 : ℝ), (43072508261779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167272149/312500000 : ℝ)|^4513 ≤ (4455655893961/10000000000000 : ℝ)^3489
        have hw : |(167272149/312500000 : ℝ)|=(167272149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987633887/10000000000 : ℝ)|^4513 ≤ (12370932788047/100000000000000 : ℝ)^3489
        have hw : |(-1987633887/10000000000 : ℝ)|=(1987633887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214349899/10000000000 : ℝ)|^4513 ≤ (43072508261779/100000000000000 : ℝ)^3489
        have hw : |(5214349899/10000000000 : ℝ)|=(5214349899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352709337/10000000000 : ℝ)*x 0 + (2607174743/5000000000 : ℝ)*x 1 + (-1987633673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352709337/10000000000 : ℝ)^4513 ≤ (22278282533071/50000000000000 : ℝ)^3489 := by
    have hnat : (5352709337 : ℕ)^4513*50000000000000^3489 ≤ 22278282533071^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352709337 10000000000 22278282533071 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607174743/5000000000 : ℝ)^4513 ≤ (21536251924489/50000000000000 : ℝ)^3489 := by
    have hnat : (2607174743 : ℕ)^4513*50000000000000^3489 ≤ 21536251924489^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607174743 5000000000 21536251924489 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987633673/10000000000 : ℝ)^4513 ≤ (1237093106521/10000000000000 : ℝ)^3489 := by
    have hnat : (1987633673 : ℕ)^4513*10000000000000^3489 ≤ 1237093106521^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987633673 10000000000 1237093106521 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352709337/10000000000 : ℝ), (2607174743/5000000000 : ℝ), (-1987633673/10000000000 : ℝ)] ![(22278282533071/50000000000000 : ℝ), (21536251924489/50000000000000 : ℝ), (1237093106521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352709337/10000000000 : ℝ)|^4513 ≤ (22278282533071/50000000000000 : ℝ)^3489
        have hw : |(5352709337/10000000000 : ℝ)|=(5352709337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607174743/5000000000 : ℝ)|^4513 ≤ (21536251924489/50000000000000 : ℝ)^3489
        have hw : |(2607174743/5000000000 : ℝ)|=(2607174743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987633673/10000000000 : ℝ)|^4513 ≤ (1237093106521/10000000000000 : ℝ)^3489
        have hw : |(-1987633673/10000000000 : ℝ)|=(1987633673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135656283/5000000000 : ℝ)*x 0 + (4025706863/10000000000 : ℝ)*x 1 + (1132393469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135656283/5000000000 : ℝ)^4513 ≤ (16638087023679/50000000000000 : ℝ)^3489 := by
    have hnat : (2135656283 : ℕ)^4513*50000000000000^3489 ≤ 16638087023679^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135656283 5000000000 16638087023679 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025706863/10000000000 : ℝ)^4513 ≤ (30822350408867/100000000000000 : ℝ)^3489 := by
    have hnat : (4025706863 : ℕ)^4513*100000000000000^3489 ≤ 30822350408867^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025706863 10000000000 30822350408867 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132393469/2500000000 : ℝ)^4513 ≤ (359014755251/1000000000000 : ℝ)^3489 := by
    have hnat : (1132393469 : ℕ)^4513*1000000000000^3489 ≤ 359014755251^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132393469 2500000000 359014755251 1000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135656283/5000000000 : ℝ), (4025706863/10000000000 : ℝ), (1132393469/2500000000 : ℝ)] ![(16638087023679/50000000000000 : ℝ), (30822350408867/100000000000000 : ℝ), (359014755251/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135656283/5000000000 : ℝ)|^4513 ≤ (16638087023679/50000000000000 : ℝ)^3489
        have hw : |(2135656283/5000000000 : ℝ)|=(2135656283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025706863/10000000000 : ℝ)|^4513 ≤ (30822350408867/100000000000000 : ℝ)^3489
        have hw : |(4025706863/10000000000 : ℝ)|=(4025706863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132393469/2500000000 : ℝ)|^4513 ≤ (359014755251/1000000000000 : ℝ)^3489
        have hw : |(1132393469/2500000000 : ℝ)|=(1132393469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-234181353/1250000000 : ℝ)*x 0 + (6519413/12500000 : ℝ)*x 1 + (5435992897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234181353/1250000000 : ℝ)^4513 ≤ (11459542889849/100000000000000 : ℝ)^3489 := by
    have hnat : (234181353 : ℕ)^4513*100000000000000^3489 ≤ 11459542889849^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234181353 1250000000 11459542889849 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6519413/12500000 : ℝ)^4513 ≤ (344680976309/800000000000 : ℝ)^3489 := by
    have hnat : (6519413 : ℕ)^4513*800000000000^3489 ≤ 344680976309^3489*12500000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6519413 12500000 344680976309 800000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435992897/10000000000 : ℝ)^4513 ≤ (45455335052369/100000000000000 : ℝ)^3489 := by
    have hnat : (5435992897 : ℕ)^4513*100000000000000^3489 ≤ 45455335052369^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435992897 10000000000 45455335052369 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234181353/1250000000 : ℝ), (6519413/12500000 : ℝ), (5435992897/10000000000 : ℝ)] ![(11459542889849/100000000000000 : ℝ), (344680976309/800000000000 : ℝ), (45455335052369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234181353/1250000000 : ℝ)|^4513 ≤ (11459542889849/100000000000000 : ℝ)^3489
        have hw : |(-234181353/1250000000 : ℝ)|=(234181353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6519413/12500000 : ℝ)|^4513 ≤ (344680976309/800000000000 : ℝ)^3489
        have hw : |(6519413/12500000 : ℝ)|=(6519413/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435992897/10000000000 : ℝ)|^4513 ≤ (45455335052369/100000000000000 : ℝ)^3489
        have hw : |(5435992897/10000000000 : ℝ)|=(5435992897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323561579/2500000000 : ℝ)*x 0 + (-220748843/1250000000 : ℝ)*x 1 + (1087198623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323561579/2500000000 : ℝ)^4513 ≤ (21964047051973/50000000000000 : ℝ)^3489 := by
    have hnat : (1323561579 : ℕ)^4513*50000000000000^3489 ≤ 21964047051973^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323561579 2500000000 21964047051973 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220748843/1250000000 : ℝ)^4513 ≤ (5308284239429/50000000000000 : ℝ)^3489 := by
    have hnat : (220748843 : ℕ)^4513*50000000000000^3489 ≤ 5308284239429^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220748843 1250000000 5308284239429 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087198623/2000000000 : ℝ)^4513 ≤ (45455337410277/100000000000000 : ℝ)^3489 := by
    have hnat : (1087198623 : ℕ)^4513*100000000000000^3489 ≤ 45455337410277^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087198623 2000000000 45455337410277 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323561579/2500000000 : ℝ), (-220748843/1250000000 : ℝ), (1087198623/2000000000 : ℝ)] ![(21964047051973/50000000000000 : ℝ), (5308284239429/50000000000000 : ℝ), (45455337410277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323561579/2500000000 : ℝ)|^4513 ≤ (21964047051973/50000000000000 : ℝ)^3489
        have hw : |(1323561579/2500000000 : ℝ)|=(1323561579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220748843/1250000000 : ℝ)|^4513 ≤ (5308284239429/50000000000000 : ℝ)^3489
        have hw : |(-220748843/1250000000 : ℝ)|=(220748843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087198623/2000000000 : ℝ)|^4513 ≤ (45455337410277/100000000000000 : ℝ)^3489
        have hw : |(1087198623/2000000000 : ℝ)|=(1087198623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26471233/50000000 : ℝ)*x 0 + (1358998193/2500000000 : ℝ)*x 1 + (-441497707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26471233/50000000 : ℝ)^4513 ≤ (10982024287997/25000000000000 : ℝ)^3489 := by
    have hnat : (26471233 : ℕ)^4513*25000000000000^3489 ≤ 10982024287997^3489*50000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26471233 50000000 10982024287997 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358998193/2500000000 : ℝ)^4513 ≤ (22727666850179/50000000000000 : ℝ)^3489 := by
    have hnat : (1358998193 : ℕ)^4513*50000000000000^3489 ≤ 22727666850179^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358998193 2500000000 22727666850179 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441497707/2500000000 : ℝ)^4513 ≤ (663535570753/6250000000000 : ℝ)^3489 := by
    have hnat : (441497707 : ℕ)^4513*6250000000000^3489 ≤ 663535570753^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441497707 2500000000 663535570753 6250000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26471233/50000000 : ℝ), (1358998193/2500000000 : ℝ), (-441497707/2500000000 : ℝ)] ![(10982024287997/25000000000000 : ℝ), (22727666850179/50000000000000 : ℝ), (663535570753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26471233/50000000 : ℝ)|^4513 ≤ (10982024287997/25000000000000 : ℝ)^3489
        have hw : |(26471233/50000000 : ℝ)|=(26471233/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358998193/2500000000 : ℝ)|^4513 ≤ (22727666850179/50000000000000 : ℝ)^3489
        have hw : |(1358998193/2500000000 : ℝ)|=(1358998193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441497707/2500000000 : ℝ)|^4513 ≤ (663535570753/6250000000000 : ℝ)^3489
        have hw : |(-441497707/2500000000 : ℝ)|=(441497707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s3_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3337019/7812500 : ℝ)*x 0 + (4526905113/10000000000 : ℝ)*x 1 + (2014198049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3337019/7812500 : ℝ)^4513 ≤ (6655379424551/20000000000000 : ℝ)^3489 := by
    have hnat : (3337019 : ℕ)^4513*20000000000000^3489 ≤ 6655379424551^3489*7812500^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3337019 7812500 6655379424551 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526905113/10000000000 : ℝ)^4513 ≤ (4484264632201/12500000000000 : ℝ)^3489 := by
    have hnat : (4526905113 : ℕ)^4513*12500000000000^3489 ≤ 4484264632201^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526905113 10000000000 4484264632201 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014198049/5000000000 : ℝ)^4513 ≤ (15424492906457/50000000000000 : ℝ)^3489 := by
    have hnat : (2014198049 : ℕ)^4513*50000000000000^3489 ≤ 15424492906457^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014198049 5000000000 15424492906457 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3337019/7812500 : ℝ), (4526905113/10000000000 : ℝ), (2014198049/5000000000 : ℝ)] ![(6655379424551/20000000000000 : ℝ), (4484264632201/12500000000000 : ℝ), (15424492906457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3337019/7812500 : ℝ)|^4513 ≤ (6655379424551/20000000000000 : ℝ)^3489
        have hw : |(3337019/7812500 : ℝ)|=(3337019/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526905113/10000000000 : ℝ)|^4513 ≤ (4484264632201/12500000000000 : ℝ)^3489
        have hw : |(4526905113/10000000000 : ℝ)|=(4526905113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014198049/5000000000 : ℝ)|^4513 ≤ (15424492906457/50000000000000 : ℝ)^3489
        have hw : |(2014198049/5000000000 : ℝ)|=(2014198049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5417/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15553/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10413/100000 : ℝ) ^ (4511/1024 : ℝ) ≤ (2350298768381287/50000000000000000000 : ℝ) := by
    have hpowers : (10413/100000 : ℝ)^4511 ≤ (2350298768381287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10413 : ℕ)^4511*50000000000000000000^1024 ≤ 2350298768381287^1024*100000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10413 100000 2350298768381287 50000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10413/100000 : ℝ)) (X := (2350298768381287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4003/25000 : ℝ) ^ (4511/1024 : ℝ) ≤ (1251483831501813/4000000000000000000 : ℝ) := by
    have hpowers : (4003/25000 : ℝ)^4511 ≤ (1251483831501813/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4003 : ℕ)^4511*4000000000000000000^1024 ≤ 1251483831501813^1024*25000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003 25000 1251483831501813 4000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4003/25000 : ℝ)) (X := (1251483831501813/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002350298768381287/25000000000000000000 : ℝ) ≤ (5000106699999761/5000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (25002350298768381287/25000000000000000000 : ℝ)^1024 ≤ (5000106699999761/5000000000000000 : ℝ)^4511 := by
      have hnat : (25002350298768381287 : ℕ)^1024*5000000000000000^4511 ≤ 5000106699999761^4511*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002350298768381287 25000000000000000000 5000106699999761 5000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106699999761/5000000000000000 : ℝ)) (X := (25002350298768381287/25000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035987693324307899/100000000000000000000 : ℝ) ≤ (10000816809428237/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (100035987693324307899/100000000000000000000 : ℝ)^1024 ≤ (10000816809428237/10000000000000000 : ℝ)^4511 := by
      have hnat : (100035987693324307899 : ℕ)^1024*10000000000000000^4511 ≤ 10000816809428237^4511*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035987693324307899 100000000000000000000 10000816809428237 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000816809428237/10000000000000000 : ℝ)) (X := (100035987693324307899/100000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001251483831501813/2000000000000000000 : ℝ) ≤ (1250177527357119/1250000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (2001251483831501813/2000000000000000000 : ℝ)^1024 ≤ (1250177527357119/1250000000000000 : ℝ)^4511 := by
      have hnat : (2001251483831501813 : ℕ)^1024*1250000000000000^4511 ≤ 1250177527357119^4511*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001251483831501813 2000000000000000000 1250177527357119 1250000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250177527357119/1250000000000000 : ℝ)) (X := (2001251483831501813/2000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2350298768381287/50000000000000000000 : ℝ) ≤ ((109333258245771299/109355468750000000 : ℝ)+2*(120681885743/111980000000000 : ℝ)*(10413/100000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (109333258245771299/109355468750000000 : ℝ)+2*(120681885743/111980000000000 : ℝ)*(10413/100000 : ℝ)=(5000106699999761/5000000000000000 : ℝ) by norm_num, show 1+2*(2350298768381287/50000000000000000000 : ℝ)=(25002350298768381287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1251483831501813/4000000000000000000 : ℝ)+(2350298768381287/50000000000000000000 : ℝ) ≤ ((109333258245771299/109355468750000000 : ℝ)+(120681885743/111980000000000 : ℝ)*((4003/25000 : ℝ)+(10413/100000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (109333258245771299/109355468750000000 : ℝ)+(120681885743/111980000000000 : ℝ)*((4003/25000 : ℝ)+(10413/100000 : ℝ))=(10000816809428237/10000000000000000 : ℝ) by norm_num, show 1+(1251483831501813/4000000000000000000 : ℝ)+(2350298768381287/50000000000000000000 : ℝ)=(100035987693324307899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1251483831501813/4000000000000000000 : ℝ) ≤ ((109333258245771299/109355468750000000 : ℝ)+2*(120681885743/111980000000000 : ℝ)*(4003/25000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (109333258245771299/109355468750000000 : ℝ)+2*(120681885743/111980000000000 : ℝ)*(4003/25000 : ℝ)=(1250177527357119/1250000000000000 : ℝ) by norm_num, show 1+2*(1251483831501813/4000000000000000000 : ℝ)=(2001251483831501813/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109333258245771299/109355468750000000 : ℝ)*(X 1 0+X 2 0)+(120681885743/111980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (109333258245771299/109355468750000000 : ℝ)) (alpha := (120681885743/111980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109333258245771299/109355468750000000 : ℝ)*(X 0 1+X 2 1)+(120681885743/111980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (109333258245771299/109355468750000000 : ℝ)) (alpha := (120681885743/111980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109333258245771299/109355468750000000 : ℝ)*(X 0 2+X 1 2)+(120681885743/111980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (109333258245771299/109355468750000000 : ℝ)) (alpha := (120681885743/111980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1873419929/10000000000 : ℝ)*X 0 0+(1359295411/2500000000 : ℝ)*X 0 1+(5214349919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167272149/312500000 : ℝ)*X 1 0+(-1987633887/10000000000 : ℝ)*X 1 1+(5214349899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352709337/10000000000 : ℝ)*X 2 0+(2607174743/5000000000 : ℝ)*X 2 1+(-1987633673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135656283/5000000000 : ℝ)*X 0 0+(4025706863/10000000000 : ℝ)*X 0 1+(1132393469/2500000000 : ℝ)*X 0 2+(2135656283/5000000000 : ℝ)*X 1 0+(4025706863/10000000000 : ℝ)*X 1 1+(1132393469/2500000000 : ℝ)*X 1 2+(2135656283/5000000000 : ℝ)*X 2 0+(4025706863/10000000000 : ℝ)*X 2 1+(1132393469/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-234181353/1250000000 : ℝ)*X 0 0+(6519413/12500000 : ℝ)*X 0 1+(5435992897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323561579/2500000000 : ℝ)*X 1 0+(-220748843/1250000000 : ℝ)*X 1 1+(1087198623/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26471233/50000000 : ℝ)*X 2 0+(1358998193/2500000000 : ℝ)*X 2 1+(-441497707/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3337019/7812500 : ℝ)*X 0 0+(4526905113/10000000000 : ℝ)*X 0 1+(2014198049/5000000000 : ℝ)*X 0 2+(3337019/7812500 : ℝ)*X 1 0+(4526905113/10000000000 : ℝ)*X 1 1+(2014198049/5000000000 : ℝ)*X 1 2+(3337019/7812500 : ℝ)*X 2 0+(4526905113/10000000000 : ℝ)*X 2 1+(2014198049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301914023770220714507780847/43742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2826172841/100000000000000 : ℝ)*(base19) + (2734621089/100000000000000 : ℝ)*(base23) + (451613859/100000000000000 : ℝ)*(upper3) + (243487/80000000000 : ℝ)*(upper4) + (164736789/50000000000000 : ℝ)*(upper5) + (404528422093633/12500000000000 : ℝ)*(major0) + (404528422093633/12500000000000 : ℝ)*(major1) + (404528422093633/12500000000000 : ℝ)*(major2) + (4487726339228117/100000000000000 : ℝ)*(sp0) + (4487763754259857/100000000000000 : ℝ)*(sp1) + (4487763845811609/100000000000000 : ℝ)*(sp2) + (1984667206877491/100000000000000 : ℝ)*(sp3) + (40241204581/100000000000000 : ℝ)*(sp4) + (5184029279/25000000000000 : ℝ)*(sp7) + (1984687942994607/100000000000000 : ℝ)*(f.failure) + (2243883290216349/50000000000000 : ℝ)*(f.sum) + (23565030599259/5599000000000000000000000000 : ℝ)*base66 + (581457612670278713/87484375000000000000000000000000 : ℝ)*base67 + (7447689936883017/1366943359375000000000000000000 : ℝ)*base69 + (86767042221009081/43742187500000000000000000000000 : ℝ)*base72 + (4666629768017/2799500000000000000000000000 : ℝ)*base73 + (588074813741184963/87484375000000000000000000000000 : ℝ)*base75 + (358111344430747463/87484375000000000000000000000000 : ℝ)*base77 + (849497820023809963/87484375000000000000000000000000 : ℝ)*base79 + (14963981388021/5599000000000000000000000000 : ℝ)*base82 + (44280287/10000000000000000000000 : ℝ)*base90 + (44280287/10000000000000000000000 : ℝ)*base92 + (44280287/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (830754763315700834674508373/87484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296241897/20000000000000 : ℝ)*(base19) + (191917057/10000000000000 : ℝ)*(base23) + (4474877/2000000000000 : ℝ)*(upper3) + (11012003/12500000000000 : ℝ)*(lower4) + (88661101/50000000000000 : ℝ)*(upper5) + (817737499995553/25000000000000 : ℝ)*(major0) + (817737499995553/25000000000000 : ℝ)*(major1) + (817737499995553/25000000000000 : ℝ)*(major2) + (24867180049/100000000000000 : ℝ)*(sp1) + (13712238401/50000000000000 : ℝ)*(sp2) + (2267958662271887/50000000000000 : ℝ)*(sp4) + (4535890976154241/100000000000000 : ℝ)*(sp5) + (4535887980896401/100000000000000 : ℝ)*(sp6) + (1002991179443057/50000000000000 : ℝ)*(sp7) + (1002991179443057/50000000000000 : ℝ)*(f.failure) + (2267958662271887/50000000000000 : ℝ)*(f.sum) + (832920311191/279950000000000000000000000 : ℝ)*base65 + (16283417838136431/5467773437500000000000000000000 : ℝ)*base68 + (5909014629435403/2733886718750000000000000000000 : ℝ)*base70 + (161993454453638323/43742187500000000000000000000000 : ℝ)*base72 + (13717694005369/5599000000000000000000000000 : ℝ)*base74 + (143297651272257237/10935546875000000000000000000000 : ℝ)*base76 + (22703944258944737/10935546875000000000000000000000 : ℝ)*base78 + (55799837378019819/5467773437500000000000000000000 : ℝ)*base79 + (10248997502943/2799500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (28643263/5000000000000000000000 : ℝ)*base89 + (28643263/5000000000000000000000 : ℝ)*base91 + (28643263/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1508_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1508_s4_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873878883/10000000000 : ℝ)*x 0 + (1086835331/2000000000 : ℝ)*x 1 + (1304262931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873878883/10000000000 : ℝ)^4513 ≤ (2292585966049/20000000000000 : ℝ)^3489 := by
    have hnat : (1873878883 : ℕ)^4513*20000000000000^3489 ≤ 2292585966049^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873878883 10000000000 2292585966049 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086835331/2000000000 : ℝ)^4513 ≤ (45435691376229/100000000000000 : ℝ)^3489 := by
    have hnat : (1086835331 : ℕ)^4513*100000000000000^3489 ≤ 45435691376229^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086835331 2000000000 45435691376229 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304262931/2500000000 : ℝ)^4513 ≤ (10775344695173/25000000000000 : ℝ)^3489 := by
    have hnat : (1304262931 : ℕ)^4513*25000000000000^3489 ≤ 10775344695173^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304262931 2500000000 10775344695173 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873878883/10000000000 : ℝ), (1086835331/2000000000 : ℝ), (1304262931/2500000000 : ℝ)] ![(2292585966049/20000000000000 : ℝ), (45435691376229/100000000000000 : ℝ), (10775344695173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873878883/10000000000 : ℝ)|^4513 ≤ (2292585966049/20000000000000 : ℝ)^3489
        have hw : |(-1873878883/10000000000 : ℝ)|=(1873878883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086835331/2000000000 : ℝ)|^4513 ≤ (45435691376229/100000000000000 : ℝ)^3489
        have hw : |(1086835331/2000000000 : ℝ)|=(1086835331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304262931/2500000000 : ℝ)|^4513 ≤ (10775344695173/25000000000000 : ℝ)^3489
        have hw : |(1304262931/2500000000 : ℝ)|=(1304262931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351922763/10000000000 : ℝ)*x 0 + (-198509859/1000000000 : ℝ)*x 1 + (5217051659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351922763/10000000000 : ℝ)^4513 ≤ (89096192113/200000000000 : ℝ)^3489 := by
    have hnat : (5351922763 : ℕ)^4513*200000000000^3489 ≤ 89096192113^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351922763 10000000000 89096192113 200000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198509859/1000000000 : ℝ)^4513 ≤ (6175262922841/50000000000000 : ℝ)^3489 := by
    have hnat : (198509859 : ℕ)^4513*50000000000000^3489 ≤ 6175262922841^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198509859 1000000000 6175262922841 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217051659/10000000000 : ℝ)^4513 ≤ (21550689043039/50000000000000 : ℝ)^3489 := by
    have hnat : (5217051659 : ℕ)^4513*50000000000000^3489 ≤ 21550689043039^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217051659 10000000000 21550689043039 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351922763/10000000000 : ℝ), (-198509859/1000000000 : ℝ), (5217051659/10000000000 : ℝ)] ![(89096192113/200000000000 : ℝ), (6175262922841/50000000000000 : ℝ), (21550689043039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351922763/10000000000 : ℝ)|^4513 ≤ (89096192113/200000000000 : ℝ)^3489
        have hw : |(5351922763/10000000000 : ℝ)|=(5351922763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198509859/1000000000 : ℝ)|^4513 ≤ (6175262922841/50000000000000 : ℝ)^3489
        have hw : |(-198509859/1000000000 : ℝ)|=(198509859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217051659/10000000000 : ℝ)|^4513 ≤ (21550689043039/50000000000000 : ℝ)^3489
        have hw : |(5217051659/10000000000 : ℝ)|=(5217051659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351922571/10000000000 : ℝ)*x 0 + (5217051761/10000000000 : ℝ)*x 1 + (-1985098711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351922571/10000000000 : ℝ)^4513 ≤ (5568511748661/12500000000000 : ℝ)^3489 := by
    have hnat : (5351922571 : ℕ)^4513*12500000000000^3489 ≤ 5568511748661^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351922571 10000000000 5568511748661 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217051761/10000000000 : ℝ)^4513 ≤ (5387672397011/12500000000000 : ℝ)^3489 := by
    have hnat : (5217051761 : ℕ)^4513*12500000000000^3489 ≤ 5387672397011^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217051761 10000000000 5387672397011 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985098711/10000000000 : ℝ)^4513 ≤ (2470105363889/20000000000000 : ℝ)^3489 := by
    have hnat : (1985098711 : ℕ)^4513*20000000000000^3489 ≤ 2470105363889^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985098711 10000000000 2470105363889 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351922571/10000000000 : ℝ), (5217051761/10000000000 : ℝ), (-1985098711/10000000000 : ℝ)] ![(5568511748661/12500000000000 : ℝ), (5387672397011/12500000000000 : ℝ), (2470105363889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351922571/10000000000 : ℝ)|^4513 ≤ (5568511748661/12500000000000 : ℝ)^3489
        have hw : |(5351922571/10000000000 : ℝ)|=(5351922571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217051761/10000000000 : ℝ)|^4513 ≤ (5387672397011/12500000000000 : ℝ)^3489
        have hw : |(5217051761/10000000000 : ℝ)|=(5217051761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985098711/10000000000 : ℝ)|^4513 ≤ (2470105363889/20000000000000 : ℝ)^3489
        have hw : |(-1985098711/10000000000 : ℝ)|=(1985098711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213579931/500000000 : ℝ)*x 0 + (4032127031/10000000000 : ℝ)*x 1 + (4523088131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213579931/500000000 : ℝ)^4513 ≤ (8319764168989/25000000000000 : ℝ)^3489 := by
    have hnat : (213579931 : ℕ)^4513*25000000000000^3489 ≤ 8319764168989^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213579931 500000000 8319764168989 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032127031/10000000000 : ℝ)^4513 ≤ (1235437892377/4000000000000 : ℝ)^3489 := by
    have hnat : (4032127031 : ℕ)^4513*4000000000000^3489 ≤ 1235437892377^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032127031 10000000000 1235437892377 4000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523088131/10000000000 : ℝ)^4513 ≤ (35834996002927/100000000000000 : ℝ)^3489 := by
    have hnat : (4523088131 : ℕ)^4513*100000000000000^3489 ≤ 35834996002927^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523088131 10000000000 35834996002927 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213579931/500000000 : ℝ), (4032127031/10000000000 : ℝ), (4523088131/10000000000 : ℝ)] ![(8319764168989/25000000000000 : ℝ), (1235437892377/4000000000000 : ℝ), (35834996002927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213579931/500000000 : ℝ)|^4513 ≤ (8319764168989/25000000000000 : ℝ)^3489
        have hw : |(213579931/500000000 : ℝ)|=(213579931/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032127031/10000000000 : ℝ)|^4513 ≤ (1235437892377/4000000000000 : ℝ)^3489
        have hw : |(4032127031/10000000000 : ℝ)|=(4032127031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523088131/10000000000 : ℝ)|^4513 ≤ (35834996002927/100000000000000 : ℝ)^3489
        have hw : |(4523088131/10000000000 : ℝ)|=(4523088131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-187390857/1000000000 : ℝ)*x 0 + (5218172627/10000000000 : ℝ)*x 1 + (5433047297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187390857/1000000000 : ℝ)^4513 ≤ (1432895591469/12500000000000 : ℝ)^3489 := by
    have hnat : (187390857 : ℕ)^4513*12500000000000^3489 ≤ 1432895591469^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187390857 1000000000 1432895591469 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218172627/10000000000 : ℝ)^4513 ≤ (10778339386859/25000000000000 : ℝ)^3489 := by
    have hnat : (5218172627 : ℕ)^4513*25000000000000^3489 ≤ 10778339386859^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218172627 10000000000 10778339386859 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433047297/10000000000 : ℝ)^4513 ≤ (45423477707419/100000000000000 : ℝ)^3489 := by
    have hnat : (5433047297 : ℕ)^4513*100000000000000^3489 ≤ 45423477707419^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433047297 10000000000 45423477707419 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187390857/1000000000 : ℝ), (5218172627/10000000000 : ℝ), (5433047297/10000000000 : ℝ)] ![(1432895591469/12500000000000 : ℝ), (10778339386859/25000000000000 : ℝ), (45423477707419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187390857/1000000000 : ℝ)|^4513 ≤ (1432895591469/12500000000000 : ℝ)^3489
        have hw : |(-187390857/1000000000 : ℝ)|=(187390857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218172627/10000000000 : ℝ)|^4513 ≤ (10778339386859/25000000000000 : ℝ)^3489
        have hw : |(5218172627/10000000000 : ℝ)|=(5218172627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433047297/10000000000 : ℝ)|^4513 ≤ (45423477707419/100000000000000 : ℝ)^3489
        have hw : |(5433047297/10000000000 : ℝ)|=(5433047297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66186989/125000000 : ℝ)*x 0 + (-884551607/5000000000 : ℝ)*x 1 + (2716523663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66186989/125000000 : ℝ)^4513 ≤ (43935744453701/100000000000000 : ℝ)^3489 := by
    have hnat : (66186989 : ℕ)^4513*100000000000000^3489 ≤ 43935744453701^3489*125000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66186989 125000000 43935744453701 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884551607/5000000000 : ℝ)^4513 ≤ (5320388758727/50000000000000 : ℝ)^3489 := by
    have hnat : (884551607 : ℕ)^4513*50000000000000^3489 ≤ 5320388758727^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884551607 5000000000 5320388758727 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716523663/5000000000 : ℝ)^4513 ≤ (11355869505259/25000000000000 : ℝ)^3489 := by
    have hnat : (2716523663 : ℕ)^4513*25000000000000^3489 ≤ 11355869505259^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716523663 5000000000 11355869505259 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66186989/125000000 : ℝ), (-884551607/5000000000 : ℝ), (2716523663/5000000000 : ℝ)] ![(43935744453701/100000000000000 : ℝ), (5320388758727/50000000000000 : ℝ), (11355869505259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66186989/125000000 : ℝ)|^4513 ≤ (43935744453701/100000000000000 : ℝ)^3489
        have hw : |(66186989/125000000 : ℝ)|=(66186989/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884551607/5000000000 : ℝ)|^4513 ≤ (5320388758727/50000000000000 : ℝ)^3489
        have hw : |(-884551607/5000000000 : ℝ)|=(884551607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716523663/5000000000 : ℝ)|^4513 ≤ (11355869505259/25000000000000 : ℝ)^3489
        have hw : |(2716523663/5000000000 : ℝ)|=(2716523663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294959233/10000000000 : ℝ)*x 0 + (2716523619/5000000000 : ℝ)*x 1 + (-88455159/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294959233/10000000000 : ℝ)^4513 ≤ (21967872833263/50000000000000 : ℝ)^3489 := by
    have hnat : (5294959233 : ℕ)^4513*50000000000000^3489 ≤ 21967872833263^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294959233 10000000000 21967872833263 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716523619/5000000000 : ℝ)^4513 ≤ (45423477069371/100000000000000 : ℝ)^3489 := by
    have hnat : (2716523619 : ℕ)^4513*100000000000000^3489 ≤ 45423477069371^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716523619 5000000000 45423477069371 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88455159/500000000 : ℝ)^4513 ≤ (10640777252931/100000000000000 : ℝ)^3489 := by
    have hnat : (88455159 : ℕ)^4513*100000000000000^3489 ≤ 10640777252931^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88455159 500000000 10640777252931 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294959233/10000000000 : ℝ), (2716523619/5000000000 : ℝ), (-88455159/500000000 : ℝ)] ![(21967872833263/50000000000000 : ℝ), (45423477069371/100000000000000 : ℝ), (10640777252931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294959233/10000000000 : ℝ)|^4513 ≤ (21967872833263/50000000000000 : ℝ)^3489
        have hw : |(5294959233/10000000000 : ℝ)|=(5294959233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716523619/5000000000 : ℝ)|^4513 ≤ (45423477069371/100000000000000 : ℝ)^3489
        have hw : |(2716523619/5000000000 : ℝ)|=(2716523619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88455159/500000000 : ℝ)|^4513 ≤ (10640777252931/100000000000000 : ℝ)^3489
        have hw : |(-88455159/500000000 : ℝ)|=(88455159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s4_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271665447/10000000000 : ℝ)*x 0 + (4520553647/10000000000 : ℝ)*x 1 + (4034680021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271665447/10000000000 : ℝ)^4513 ≤ (33279730114387/100000000000000 : ℝ)^3489 := by
    have hnat : (4271665447 : ℕ)^4513*100000000000000^3489 ≤ 33279730114387^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271665447 10000000000 33279730114387 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520553647/10000000000 : ℝ)^4513 ≤ (35809024892983/100000000000000 : ℝ)^3489 := by
    have hnat : (4520553647 : ℕ)^4513*100000000000000^3489 ≤ 35809024892983^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520553647 10000000000 35809024892983 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034680021/10000000000 : ℝ)^4513 ≤ (3863905622569/12500000000000 : ℝ)^3489 := by
    have hnat : (4034680021 : ℕ)^4513*12500000000000^3489 ≤ 3863905622569^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034680021 10000000000 3863905622569 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271665447/10000000000 : ℝ), (4520553647/10000000000 : ℝ), (4034680021/10000000000 : ℝ)] ![(33279730114387/100000000000000 : ℝ), (35809024892983/100000000000000 : ℝ), (3863905622569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271665447/10000000000 : ℝ)|^4513 ≤ (33279730114387/100000000000000 : ℝ)^3489
        have hw : |(4271665447/10000000000 : ℝ)|=(4271665447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520553647/10000000000 : ℝ)|^4513 ≤ (35809024892983/100000000000000 : ℝ)^3489
        have hw : |(4520553647/10000000000 : ℝ)|=(4520553647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034680021/10000000000 : ℝ)|^4513 ≤ (3863905622569/12500000000000 : ℝ)^3489
        have hw : |(4034680021/10000000000 : ℝ)|=(4034680021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2723/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5417/50000 : ℝ) ^ (4511/1024 : ℝ) ≤ (5597329542589163/100000000000000000000 : ℝ) := by
    have hpowers : (5417/50000 : ℝ)^4511 ≤ (5597329542589163/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5417 : ℕ)^4511*100000000000000000000^1024 ≤ 5597329542589163^1024*50000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5417 50000 5597329542589163 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5417/50000 : ℝ)) (X := (5597329542589163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15553/100000 : ℝ) ^ (4511/1024 : ℝ) ≤ (27524563432057189/100000000000000000000 : ℝ) := by
    have hpowers : (15553/100000 : ℝ)^4511 ≤ (27524563432057189/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15553 : ℕ)^4511*100000000000000000000^1024 ≤ 27524563432057189^1024*100000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15553 100000 27524563432057189 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15553/100000 : ℝ)) (X := (27524563432057189/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005597329542589163/50000000000000000000 : ℝ) ≤ (5000127054255691/5000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50005597329542589163/50000000000000000000 : ℝ)^1024 ≤ (5000127054255691/5000000000000000 : ℝ)^4511 := by
      have hnat : (50005597329542589163 : ℕ)^1024*5000000000000000^4511 ≤ 5000127054255691^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005597329542589163 50000000000000000000 5000127054255691 5000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000127054255691/5000000000000000 : ℝ)) (X := (50005597329542589163/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252070118310915397/6250000000000000000 : ℝ) ≤ (2000150354588163/2000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (6252070118310915397/6250000000000000000 : ℝ)^1024 ≤ (2000150354588163/2000000000000000 : ℝ)^4511 := by
      have hnat : (6252070118310915397 : ℕ)^1024*2000000000000000^4511 ≤ 2000150354588163^4511*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252070118310915397 6250000000000000000 2000150354588163 2000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000150354588163/2000000000000000 : ℝ)) (X := (6252070118310915397/6250000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027524563432057189/50000000000000000000 : ℝ) ≤ (1250156179671281/1250000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50027524563432057189/50000000000000000000 : ℝ)^1024 ≤ (1250156179671281/1250000000000000 : ℝ)^4511 := by
      have hnat : (50027524563432057189 : ℕ)^1024*1250000000000000^4511 ≤ 1250156179671281^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027524563432057189 50000000000000000000 1250156179671281 1250000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250156179671281/1250000000000000 : ℝ)) (X := (50027524563432057189/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5597329542589163/100000000000000000000 : ℝ) ≤ ((23590207872604128707/23595000000000000000 : ℝ)+2*(497664429433/471900000000000 : ℝ)*(5417/50000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (23590207872604128707/23595000000000000000 : ℝ)+2*(497664429433/471900000000000 : ℝ)*(5417/50000 : ℝ)=(5000127054255691/5000000000000000 : ℝ) by norm_num, show 1+2*(5597329542589163/100000000000000000000 : ℝ)=(50005597329542589163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27524563432057189/100000000000000000000 : ℝ)+(5597329542589163/100000000000000000000 : ℝ) ≤ ((23590207872604128707/23595000000000000000 : ℝ)+(497664429433/471900000000000 : ℝ)*((15553/100000 : ℝ)+(5417/50000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (23590207872604128707/23595000000000000000 : ℝ)+(497664429433/471900000000000 : ℝ)*((15553/100000 : ℝ)+(5417/50000 : ℝ))=(2000150354588163/2000000000000000 : ℝ) by norm_num, show 1+(27524563432057189/100000000000000000000 : ℝ)+(5597329542589163/100000000000000000000 : ℝ)=(6252070118310915397/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27524563432057189/100000000000000000000 : ℝ) ≤ ((23590207872604128707/23595000000000000000 : ℝ)+2*(497664429433/471900000000000 : ℝ)*(15553/100000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (23590207872604128707/23595000000000000000 : ℝ)+2*(497664429433/471900000000000 : ℝ)*(15553/100000 : ℝ)=(1250156179671281/1250000000000000 : ℝ) by norm_num, show 1+2*(27524563432057189/100000000000000000000 : ℝ)=(50027524563432057189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23590207872604128707/23595000000000000000 : ℝ)*(X 1 0+X 2 0)+(497664429433/471900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (23590207872604128707/23595000000000000000 : ℝ)) (alpha := (497664429433/471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23590207872604128707/23595000000000000000 : ℝ)*(X 0 1+X 2 1)+(497664429433/471900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (23590207872604128707/23595000000000000000 : ℝ)) (alpha := (497664429433/471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23590207872604128707/23595000000000000000 : ℝ)*(X 0 2+X 1 2)+(497664429433/471900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (23590207872604128707/23595000000000000000 : ℝ)) (alpha := (497664429433/471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1873878883/10000000000 : ℝ)*X 0 0+(1086835331/2000000000 : ℝ)*X 0 1+(1304262931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351922763/10000000000 : ℝ)*X 1 0+(-198509859/1000000000 : ℝ)*X 1 1+(5217051659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351922571/10000000000 : ℝ)*X 2 0+(5217051761/10000000000 : ℝ)*X 2 1+(-1985098711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213579931/500000000 : ℝ)*X 0 0+(4032127031/10000000000 : ℝ)*X 0 1+(4523088131/10000000000 : ℝ)*X 0 2+(213579931/500000000 : ℝ)*X 1 0+(4032127031/10000000000 : ℝ)*X 1 1+(4523088131/10000000000 : ℝ)*X 1 2+(213579931/500000000 : ℝ)*X 2 0+(4032127031/10000000000 : ℝ)*X 2 1+(4523088131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-187390857/1000000000 : ℝ)*X 0 0+(5218172627/10000000000 : ℝ)*X 0 1+(5433047297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66186989/125000000 : ℝ)*X 1 0+(-884551607/5000000000 : ℝ)*X 1 1+(2716523663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294959233/10000000000 : ℝ)*X 2 0+(2716523619/5000000000 : ℝ)*X 2 1+(-88455159/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271665447/10000000000 : ℝ)*X 0 0+(4520553647/10000000000 : ℝ)*X 0 1+(4034680021/10000000000 : ℝ)*X 0 2+(4271665447/10000000000 : ℝ)*X 1 0+(4520553647/10000000000 : ℝ)*X 1 1+(4034680021/10000000000 : ℝ)*X 1 2+(4271665447/10000000000 : ℝ)*X 2 0+(4520553647/10000000000 : ℝ)*X 2 1+(4034680021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172276565370992887395672759/17875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1633979217/100000000000000 : ℝ)*(base19) + (41728273/3125000000000 : ℝ)*(base23) + (91076667/100000000000000 : ℝ)*(lower2) + (240574071/100000000000000 : ℝ)*(upper3) + (19657751/100000000000000 : ℝ)*(lower4) + (664253948507439/20000000000000 : ℝ)*(major0) + (664253948507439/20000000000000 : ℝ)*(major1) + (830317435634299/25000000000000 : ℝ)*(major2) + (4605673452512779/100000000000000 : ℝ)*(sp0) + (4605695477014577/100000000000000 : ℝ)*(sp1) + (2302847887844529/50000000000000 : ℝ)*(sp2) + (1018415155236393/50000000000000 : ℝ)*(sp3) + (4731696203/20000000000000 : ℝ)*(sp4) + (587117307/5000000000000 : ℝ)*(sp7) + (2036842052818927/100000000000000 : ℝ)*(f.failure) + (2302848555496897/50000000000000 : ℝ)*(f.sum) + (387161324035633/47190000000000000000000000000 : ℝ)*base65 + (3542423545449231373/471900000000000000000000000000000 : ℝ)*base67 + (52940787537236251/4125000000000000000000000000000 : ℝ)*base69 + (2236395674944731373/471900000000000000000000000000000 : ℝ)*base71 + (104433338840263/47190000000000000000000000000 : ℝ)*base73 + (53685408645236251/4125000000000000000000000000000 : ℝ)*base75 + (10975236871033791/157300000000000000000000000000000 : ℝ)*base77 + (1584325376289233791/157300000000000000000000000000000 : ℝ)*base79 + (2648060708453/314600000000000000000000000 : ℝ)*base81 + (7258593/10000000000000000000000 : ℝ)*base89 + (7258593/10000000000000000000000 : ℝ)*base91 + (92741407/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59004807086811749119052627/8937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1017006511/100000000000000 : ℝ)*(base19) + (1197408509/100000000000000 : ℝ)*(base23) + (141248163/100000000000000 : ℝ)*(upper3) + (242569/800000000000 : ℝ)*(lower4) + (64843767/50000000000000 : ℝ)*(upper5) + (1678006059422671/50000000000000 : ℝ)*(major0) + (1678006059422671/50000000000000 : ℝ)*(major1) + (1678006059422671/50000000000000 : ℝ)*(major2) + (7794372463/50000000000000 : ℝ)*(sp1) + (4450730513/25000000000000 : ℝ)*(sp2) + (4653875434906013/100000000000000 : ℝ)*(sp4) + (290866176822161/6250000000000 : ℝ)*(sp5) + (1163464108643863/25000000000000 : ℝ)*(sp6) + (2058148582720119/100000000000000 : ℝ)*(sp7) + (2058148582720119/100000000000000 : ℝ)*(f.failure) + (4653875434906013/100000000000000 : ℝ)*(f.sum) + (2587735423291/2145000000000000000000000000 : ℝ)*base65 + (175325340746284873/107250000000000000000000000000000 : ℝ)*base68 + (471241020837715127/107250000000000000000000000000000 : ℝ)*base69 + (87271128822034873/107250000000000000000000000000000 : ℝ)*base72 + (9772915698421/2145000000000000000000000000 : ℝ)*base73 + (12981912892534873/107250000000000000000000000000000 : ℝ)*base76 + (56586941359534873/107250000000000000000000000000000 : ℝ)*base78 + (407975150674534873/107250000000000000000000000000000 : ℝ)*base80 + (3180970814611/2145000000000000000000000000 : ℝ)*base81 + (31408679/10000000000000000000000 : ℝ)*base90 + (31408679/10000000000000000000000 : ℝ)*base92 + (31408679/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1508_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1508_s5_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936968699/5000000000 : ℝ)*x 0 + (1086760063/2000000000 : ℝ)*x 1 + (260869463/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936968699/5000000000 : ℝ)^4513 ≤ (11463392837377/100000000000000 : ℝ)^3489 := by
    have hnat : (936968699 : ℕ)^4513*100000000000000^3489 ≤ 11463392837377^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936968699 5000000000 11463392837377 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086760063/2000000000 : ℝ)^4513 ≤ (22715810644489/50000000000000 : ℝ)^3489 := by
    have hnat : (1086760063 : ℕ)^4513*50000000000000^3489 ≤ 22715810644489^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086760063 2000000000 22715810644489 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260869463/500000000 : ℝ)^4513 ≤ (43104985850999/100000000000000 : ℝ)^3489 := by
    have hnat : (260869463 : ℕ)^4513*100000000000000^3489 ≤ 43104985850999^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260869463 500000000 43104985850999 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936968699/5000000000 : ℝ), (1086760063/2000000000 : ℝ), (260869463/500000000 : ℝ)] ![(11463392837377/100000000000000 : ℝ), (22715810644489/50000000000000 : ℝ), (43104985850999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936968699/5000000000 : ℝ)|^4513 ≤ (11463392837377/100000000000000 : ℝ)^3489
        have hw : |(-936968699/5000000000 : ℝ)|=(936968699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086760063/2000000000 : ℝ)|^4513 ≤ (22715810644489/50000000000000 : ℝ)^3489
        have hw : |(1086760063/2000000000 : ℝ)|=(1086760063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260869463/500000000 : ℝ)|^4513 ≤ (43104985850999/100000000000000 : ℝ)^3489
        have hw : |(260869463/500000000 : ℝ)|=(260869463/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070364763/2000000000 : ℝ)*x 0 + (-49619557/250000000 : ℝ)*x 1 + (5217389547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070364763/2000000000 : ℝ)^4513 ≤ (44547030713353/100000000000000 : ℝ)^3489 := by
    have hnat : (1070364763 : ℕ)^4513*100000000000000^3489 ≤ 44547030713353^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070364763 2000000000 44547030713353 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49619557/250000000 : ℝ)^4513 ≤ (6173990180469/50000000000000 : ℝ)^3489 := by
    have hnat : (49619557 : ℕ)^4513*50000000000000^3489 ≤ 6173990180469^3489*250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49619557 250000000 6173990180469 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217389547/10000000000 : ℝ)^4513 ≤ (43104988918047/100000000000000 : ℝ)^3489 := by
    have hnat : (5217389547 : ℕ)^4513*100000000000000^3489 ≤ 43104988918047^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217389547 10000000000 43104988918047 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070364763/2000000000 : ℝ), (-49619557/250000000 : ℝ), (5217389547/10000000000 : ℝ)] ![(44547030713353/100000000000000 : ℝ), (6173990180469/50000000000000 : ℝ), (43104988918047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070364763/2000000000 : ℝ)|^4513 ≤ (44547030713353/100000000000000 : ℝ)^3489
        have hw : |(1070364763/2000000000 : ℝ)|=(1070364763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49619557/250000000 : ℝ)|^4513 ≤ (6173990180469/50000000000000 : ℝ)^3489
        have hw : |(-49619557/250000000 : ℝ)|=(49619557/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217389547/10000000000 : ℝ)|^4513 ≤ (43104988918047/100000000000000 : ℝ)^3489
        have hw : |(5217389547/10000000000 : ℝ)|=(5217389547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070364523/2000000000 : ℝ)*x 0 + (652173931/1250000000 : ℝ)*x 1 + (-1984781361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070364523/2000000000 : ℝ)^4513 ≤ (5568377224169/12500000000000 : ℝ)^3489 := by
    have hnat : (1070364523 : ℕ)^4513*12500000000000^3489 ≤ 5568377224169^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070364523 2000000000 5568377224169 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652173931/1250000000 : ℝ)^4513 ≤ (43105009233231/100000000000000 : ℝ)^3489 := by
    have hnat : (652173931 : ℕ)^4513*100000000000000^3489 ≤ 43105009233231^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652173931 1250000000 43105009233231 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984781361/10000000000 : ℝ)^4513 ≤ (12347972965517/100000000000000 : ℝ)^3489 := by
    have hnat : (1984781361 : ℕ)^4513*100000000000000^3489 ≤ 12347972965517^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984781361 10000000000 12347972965517 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070364523/2000000000 : ℝ), (652173931/1250000000 : ℝ), (-1984781361/10000000000 : ℝ)] ![(5568377224169/12500000000000 : ℝ), (43105009233231/100000000000000 : ℝ), (12347972965517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070364523/2000000000 : ℝ)|^4513 ≤ (5568377224169/12500000000000 : ℝ)^3489
        have hw : |(1070364523/2000000000 : ℝ)|=(1070364523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652173931/1250000000 : ℝ)|^4513 ≤ (43105009233231/100000000000000 : ℝ)^3489
        have hw : |(652173931/1250000000 : ℝ)|=(652173931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984781361/10000000000 : ℝ)|^4513 ≤ (12347972965517/100000000000000 : ℝ)^3489
        have hw : |(-1984781361/10000000000 : ℝ)|=(1984781361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135817119/5000000000 : ℝ)*x 0 + (4032931213/10000000000 : ℝ)*x 1 + (4522275547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135817119/5000000000 : ℝ)^4513 ≤ (8319853902571/25000000000000 : ℝ)^3489 := by
    have hnat : (2135817119 : ℕ)^4513*25000000000000^3489 ≤ 8319853902571^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135817119 5000000000 8319853902571 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032931213/10000000000 : ℝ)^4513 ≤ (3861739433899/12500000000000 : ℝ)^3489 := by
    have hnat : (4032931213 : ℕ)^4513*12500000000000^3489 ≤ 3861739433899^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032931213 10000000000 3861739433899 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522275547/10000000000 : ℝ)^4513 ≤ (3582666890847/10000000000000 : ℝ)^3489 := by
    have hnat : (4522275547 : ℕ)^4513*10000000000000^3489 ≤ 3582666890847^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522275547 10000000000 3582666890847 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135817119/5000000000 : ℝ), (4032931213/10000000000 : ℝ), (4522275547/10000000000 : ℝ)] ![(8319853902571/25000000000000 : ℝ), (3861739433899/12500000000000 : ℝ), (3582666890847/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135817119/5000000000 : ℝ)|^4513 ≤ (8319853902571/25000000000000 : ℝ)^3489
        have hw : |(2135817119/5000000000 : ℝ)|=(2135817119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032931213/10000000000 : ℝ)|^4513 ≤ (3861739433899/12500000000000 : ℝ)^3489
        have hw : |(4032931213/10000000000 : ℝ)|=(4032931213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522275547/10000000000 : ℝ)|^4513 ≤ (3582666890847/10000000000000 : ℝ)^3489
        have hw : |(4522275547/10000000000 : ℝ)|=(4522275547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936982897/5000000000 : ℝ)*x 0 + (5218503593/10000000000 : ℝ)*x 1 + (5432678351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936982897/5000000000 : ℝ)^4513 ≤ (11463617525747/100000000000000 : ℝ)^3489 := by
    have hnat : (936982897 : ℕ)^4513*100000000000000^3489 ≤ 11463617525747^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936982897 5000000000 11463617525747 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218503593/10000000000 : ℝ)^4513 ≤ (43116894629947/100000000000000 : ℝ)^3489 := by
    have hnat : (5218503593 : ℕ)^4513*100000000000000^3489 ≤ 43116894629947^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218503593 10000000000 43116894629947 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432678351/10000000000 : ℝ)^4513 ≤ (454194878283/1000000000000 : ℝ)^3489 := by
    have hnat : (5432678351 : ℕ)^4513*1000000000000^3489 ≤ 454194878283^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432678351 10000000000 454194878283 1000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936982897/5000000000 : ℝ), (5218503593/10000000000 : ℝ), (5432678351/10000000000 : ℝ)] ![(11463617525747/100000000000000 : ℝ), (43116894629947/100000000000000 : ℝ), (454194878283/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936982897/5000000000 : ℝ)|^4513 ≤ (11463617525747/100000000000000 : ℝ)^3489
        have hw : |(-936982897/5000000000 : ℝ)|=(936982897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218503593/10000000000 : ℝ)|^4513 ≤ (43116894629947/100000000000000 : ℝ)^3489
        have hw : |(5218503593/10000000000 : ℝ)|=(5218503593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432678351/10000000000 : ℝ)|^4513 ≤ (454194878283/1000000000000 : ℝ)^3489
        have hw : |(5432678351/10000000000 : ℝ)|=(5432678351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529504823/1000000000 : ℝ)*x 0 + (-1769493109/10000000000 : ℝ)*x 1 + (43461427/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529504823/1000000000 : ℝ)^4513 ≤ (21968350435319/50000000000000 : ℝ)^3489 := by
    have hnat : (529504823 : ℕ)^4513*50000000000000^3489 ≤ 21968350435319^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529504823 1000000000 21968350435319 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769493109/10000000000 : ℝ)^4513 ≤ (1330476379161/12500000000000 : ℝ)^3489 := by
    have hnat : (1769493109 : ℕ)^4513*12500000000000^3489 ≤ 1330476379161^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769493109 10000000000 1330476379161 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43461427/80000000 : ℝ)^4513 ≤ (45419488087839/100000000000000 : ℝ)^3489 := by
    have hnat : (43461427 : ℕ)^4513*100000000000000^3489 ≤ 45419488087839^3489*80000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43461427 80000000 45419488087839 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529504823/1000000000 : ℝ), (-1769493109/10000000000 : ℝ), (43461427/80000000 : ℝ)] ![(21968350435319/50000000000000 : ℝ), (1330476379161/12500000000000 : ℝ), (45419488087839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529504823/1000000000 : ℝ)|^4513 ≤ (21968350435319/50000000000000 : ℝ)^3489
        have hw : |(529504823/1000000000 : ℝ)|=(529504823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769493109/10000000000 : ℝ)|^4513 ≤ (1330476379161/12500000000000 : ℝ)^3489
        have hw : |(-1769493109/10000000000 : ℝ)|=(1769493109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43461427/80000000 : ℝ)|^4513 ≤ (45419488087839/100000000000000 : ℝ)^3489
        have hw : |(43461427/80000000 : ℝ)|=(43461427/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165470259/312500000 : ℝ)*x 0 + (339542399/625000000 : ℝ)*x 1 + (-353898603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165470259/312500000 : ℝ)^4513 ≤ (43936701493153/100000000000000 : ℝ)^3489 := by
    have hnat : (165470259 : ℕ)^4513*100000000000000^3489 ≤ 43936701493153^3489*312500000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165470259 312500000 43936701493153 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339542399/625000000 : ℝ)^4513 ≤ (45419488185167/100000000000000 : ℝ)^3489 := by
    have hnat : (339542399 : ℕ)^4513*100000000000000^3489 ≤ 45419488185167^3489*625000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339542399 625000000 45419488185167 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353898603/2000000000 : ℝ)^4513 ≤ (1330476287739/12500000000000 : ℝ)^3489 := by
    have hnat : (353898603 : ℕ)^4513*12500000000000^3489 ≤ 1330476287739^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353898603 2000000000 1330476287739 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165470259/312500000 : ℝ), (339542399/625000000 : ℝ), (-353898603/2000000000 : ℝ)] ![(43936701493153/100000000000000 : ℝ), (45419488185167/100000000000000 : ℝ), (1330476287739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165470259/312500000 : ℝ)|^4513 ≤ (43936701493153/100000000000000 : ℝ)^3489
        have hw : |(165470259/312500000 : ℝ)|=(165470259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339542399/625000000 : ℝ)|^4513 ≤ (45419488185167/100000000000000 : ℝ)^3489
        have hw : |(339542399/625000000 : ℝ)|=(339542399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353898603/2000000000 : ℝ)|^4513 ≤ (1330476287739/12500000000000 : ℝ)^3489
        have hw : |(-353898603/2000000000 : ℝ)|=(353898603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s5_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135850111/5000000000 : ℝ)*x 0 + (564969761/1250000000 : ℝ)*x 1 + (1008866793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135850111/5000000000 : ℝ)^4513 ≤ (8320020138781/25000000000000 : ℝ)^3489 := by
    have hnat : (2135850111 : ℕ)^4513*25000000000000^3489 ≤ 8320020138781^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135850111 5000000000 8320020138781 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564969761/1250000000 : ℝ)^4513 ≤ (7160174720357/20000000000000 : ℝ)^3489 := by
    have hnat : (564969761 : ℕ)^4513*20000000000000^3489 ≤ 7160174720357^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564969761 1250000000 7160174720357 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008866793/2500000000 : ℝ)^4513 ≤ (6183809167263/20000000000000 : ℝ)^3489 := by
    have hnat : (1008866793 : ℕ)^4513*20000000000000^3489 ≤ 6183809167263^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008866793 2500000000 6183809167263 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135850111/5000000000 : ℝ), (564969761/1250000000 : ℝ), (1008866793/2500000000 : ℝ)] ![(8320020138781/25000000000000 : ℝ), (7160174720357/20000000000000 : ℝ), (6183809167263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135850111/5000000000 : ℝ)|^4513 ≤ (8320020138781/25000000000000 : ℝ)^3489
        have hw : |(2135850111/5000000000 : ℝ)|=(2135850111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564969761/1250000000 : ℝ)|^4513 ≤ (7160174720357/20000000000000 : ℝ)^3489
        have hw : |(564969761/1250000000 : ℝ)|=(564969761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008866793/2500000000 : ℝ)|^4513 ≤ (6183809167263/20000000000000 : ℝ)^3489
        have hw : |(1008866793/2500000000 : ℝ)|=(1008866793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10899/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2723/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2723/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2723/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2723/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2723/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2723/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2723/25000 : ℝ) ^ (4511/1024 : ℝ) ≤ (114610874606399/2000000000000000000 : ℝ) := by
    have hpowers : (2723/25000 : ℝ)^4511 ≤ (114610874606399/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2723 : ℕ)^4511*2000000000000000000^1024 ≤ 114610874606399^1024*25000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2723 25000 114610874606399 2000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2723/25000 : ℝ)) (X := (114610874606399/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4511/1024 : ℝ) ≤ (5407356718967167/20000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4511 ≤ (5407356718967167/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4511*20000000000000000000^1024 ≤ 5407356718967167^1024*10000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 5407356718967167 20000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (5407356718967167/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000114610874606399/1000000000000000000 : ℝ) ≤ (10000260155923693/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (1000114610874606399/1000000000000000000 : ℝ)^1024 ≤ (10000260155923693/10000000000000000 : ℝ)^4511 := by
      have hnat : (1000114610874606399 : ℕ)^1024*10000000000000000^4511 ≤ 10000260155923693^4511*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000114610874606399 1000000000000000000 10000260155923693 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260155923693/10000000000000000 : ℝ)) (X := (1000114610874606399/1000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006553465465031157/20000000000000000000 : ℝ) ≤ (10000743726326079/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (20006553465465031157/20000000000000000000 : ℝ)^1024 ≤ (10000743726326079/10000000000000000 : ℝ)^4511 := by
      have hnat : (20006553465465031157 : ℕ)^1024*10000000000000000^4511 ≤ 10000743726326079^4511*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006553465465031157 20000000000000000000 10000743726326079 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000743726326079/10000000000000000 : ℝ)) (X := (20006553465465031157/20000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005407356718967167/10000000000000000000 : ℝ) ≤ (2000245459345693/2000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (10005407356718967167/10000000000000000000 : ℝ)^1024 ≤ (2000245459345693/2000000000000000 : ℝ)^4511 := by
      have hnat : (10005407356718967167 : ℕ)^1024*2000000000000000^4511 ≤ 2000245459345693^4511*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005407356718967167 10000000000000000000 2000245459345693 2000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000245459345693/2000000000000000 : ℝ)) (X := (10005407356718967167/10000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(114610874606399/2000000000000000000 : ℝ) ≤ ((4597066209929156379/4598000000000000000 : ℝ)+2*(241785201193/229900000000000 : ℝ)*(2723/25000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (4597066209929156379/4598000000000000000 : ℝ)+2*(241785201193/229900000000000 : ℝ)*(2723/25000 : ℝ)=(10000260155923693/10000000000000000 : ℝ) by norm_num, show 1+2*(114610874606399/2000000000000000000 : ℝ)=(1000114610874606399/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5407356718967167/20000000000000000000 : ℝ)+(114610874606399/2000000000000000000 : ℝ) ≤ ((4597066209929156379/4598000000000000000 : ℝ)+(241785201193/229900000000000 : ℝ)*((1549/10000 : ℝ)+(2723/25000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (4597066209929156379/4598000000000000000 : ℝ)+(241785201193/229900000000000 : ℝ)*((1549/10000 : ℝ)+(2723/25000 : ℝ))=(10000743726326079/10000000000000000 : ℝ) by norm_num, show 1+(5407356718967167/20000000000000000000 : ℝ)+(114610874606399/2000000000000000000 : ℝ)=(20006553465465031157/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5407356718967167/20000000000000000000 : ℝ) ≤ ((4597066209929156379/4598000000000000000 : ℝ)+2*(241785201193/229900000000000 : ℝ)*(1549/10000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (4597066209929156379/4598000000000000000 : ℝ)+2*(241785201193/229900000000000 : ℝ)*(1549/10000 : ℝ)=(2000245459345693/2000000000000000 : ℝ) by norm_num, show 1+2*(5407356718967167/20000000000000000000 : ℝ)=(10005407356718967167/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4597066209929156379/4598000000000000000 : ℝ)*(X 1 0+X 2 0)+(241785201193/229900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4597066209929156379/4598000000000000000 : ℝ)) (alpha := (241785201193/229900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4597066209929156379/4598000000000000000 : ℝ)*(X 0 1+X 2 1)+(241785201193/229900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4597066209929156379/4598000000000000000 : ℝ)) (alpha := (241785201193/229900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4597066209929156379/4598000000000000000 : ℝ)*(X 0 2+X 1 2)+(241785201193/229900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4597066209929156379/4598000000000000000 : ℝ)) (alpha := (241785201193/229900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-936968699/5000000000 : ℝ)*X 0 0+(1086760063/2000000000 : ℝ)*X 0 1+(260869463/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070364763/2000000000 : ℝ)*X 1 0+(-49619557/250000000 : ℝ)*X 1 1+(5217389547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070364523/2000000000 : ℝ)*X 2 0+(652173931/1250000000 : ℝ)*X 2 1+(-1984781361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135817119/5000000000 : ℝ)*X 0 0+(4032931213/10000000000 : ℝ)*X 0 1+(4522275547/10000000000 : ℝ)*X 0 2+(2135817119/5000000000 : ℝ)*X 1 0+(4032931213/10000000000 : ℝ)*X 1 1+(4522275547/10000000000 : ℝ)*X 1 2+(2135817119/5000000000 : ℝ)*X 2 0+(4032931213/10000000000 : ℝ)*X 2 1+(4522275547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-936982897/5000000000 : ℝ)*X 0 0+(5218503593/10000000000 : ℝ)*X 0 1+(5432678351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529504823/1000000000 : ℝ)*X 1 0+(-1769493109/10000000000 : ℝ)*X 1 1+(43461427/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165470259/312500000 : ℝ)*X 2 0+(339542399/625000000 : ℝ)*X 2 1+(-353898603/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135850111/5000000000 : ℝ)*X 0 0+(564969761/1250000000 : ℝ)*X 0 1+(1008866793/2500000000 : ℝ)*X 0 2+(2135850111/5000000000 : ℝ)*X 1 0+(564969761/1250000000 : ℝ)*X 1 1+(1008866793/2500000000 : ℝ)*X 1 2+(2135850111/5000000000 : ℝ)*X 2 0+(564969761/1250000000 : ℝ)*X 2 1+(1008866793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579980611774151064965627343/45980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2478034551/100000000000000 : ℝ)*(base19) + (436623543/50000000000000 : ℝ)*(base23) + (2424089/800000000000 : ℝ)*(upper3) + (38042953/12500000000000 : ℝ)*(upper4) + (307829937/50000000000000 : ℝ)*(upper5) + (833061931886201/25000000000000 : ℝ)*(major0) + (833061931886201/25000000000000 : ℝ)*(major1) + (666449545508961/20000000000000 : ℝ)*(major2) + (288804584708783/6250000000000 : ℝ)*(sp0) + (4620918011913833/100000000000000 : ℝ)*(sp1) + (2310459808350649/50000000000000 : ℝ)*(sp2) + (2043564726292221/100000000000000 : ℝ)*(sp3) + (2945912991/6250000000000 : ℝ)*(sp4) + (613649399/6250000000000 : ℝ)*(sp7) + (1021787272341303/50000000000000 : ℝ)*(f.failure) + (144403765310887/3125000000000 : ℝ)*(f.sum) + (145672077669917/22990000000000000000000000000 : ℝ)*base65 + (1998004057481711/10450000000000000000000000000000 : ℝ)*base68 + (154181950134340219/91960000000000000000000000000000 : ℝ)*base69 + (29359740114081711/10450000000000000000000000000000 : ℝ)*base72 + (17158975734787/22990000000000000000000000000 : ℝ)*base73 + (415049579910940219/91960000000000000000000000000000 : ℝ)*base75 + (462215920682886179/114950000000000000000000000000000 : ℝ)*base77 + (1011937023450536179/114950000000000000000000000000000 : ℝ)*base79 + (2572618082457/11495000000000000000000000000 : ℝ)*base81 + (32925977/5000000000000000000000 : ℝ)*base89 + (32925977/5000000000000000000000 : ℝ)*base91 + (17074023/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54167212752480609284721/11495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222349827/25000000000000 : ℝ)*(base19) + (19678311/2000000000000 : ℝ)*(base23) + (60628083/20000000000000 : ℝ)*(lower1) + (57141309/50000000000000 : ℝ)*(upper3) + (891301/10000000000000 : ℝ)*(lower4) + (7174807/6250000000000 : ℝ)*(upper5) + (3366969530437809/100000000000000 : ℝ)*(major0) + (3366969530437809/100000000000000 : ℝ)*(major1) + (3366969530437809/100000000000000 : ℝ)*(major2) + (2475273929/100000000000000 : ℝ)*(sp2) + (145908451447453/3125000000000 : ℝ)*(sp4) + (1167267389229797/25000000000000 : ℝ)*(sp5) + (2334533493564509/50000000000000 : ℝ)*(sp6) + (1032434228741197/50000000000000 : ℝ)*(sp7) + (1032434228741197/50000000000000 : ℝ)*(f.failure) + (145908451447453/3125000000000 : ℝ)*(f.sum) + (38976878971643/11495000000000000000000000000 : ℝ)*base66 + (14714441831777873611/459800000000000000000000000000000 : ℝ)*base67 + (1236052660550673611/459800000000000000000000000000000 : ℝ)*base69 + (39274258848079473611/459800000000000000000000000000000 : ℝ)*base71 + (69850857327963/11495000000000000000000000000 : ℝ)*base74 + (23317303849408526389/459800000000000000000000000000000 : ℝ)*base76 + (114824622604726389/459800000000000000000000000000000 : ℝ)*base78 + (6404792887186926389/459800000000000000000000000000000 : ℝ)*base80 + (17442940869141/5747500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6191523/5000000000000000000000 : ℝ)*base89 + (6191523/5000000000000000000000 : ℝ)*base91 + (6191523/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1508_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1508_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1508_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1508_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1508_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

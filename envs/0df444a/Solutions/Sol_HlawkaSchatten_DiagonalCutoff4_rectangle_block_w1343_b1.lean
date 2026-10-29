-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:50.041174+00:00
-- url     : https://prove2.me/submissions/50470c09-0d5a-49a9-8cb4-39e942a26031

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
theorem support_rectangle_w1343_s3_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63792453/312500000 : ℝ)*x 0 + (1085408413/2000000000 : ℝ)*x 1 + (5231401053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63792453/312500000 : ℝ)^4303 ≤ (6214178838899/50000000000000 : ℝ)^3279 := by
    have hnat : (63792453 : ℕ)^4303*50000000000000^3279 ≤ 6214178838899^3279*312500000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63792453 312500000 6214178838899 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085408413/2000000000 : ℝ)^4303 ≤ (44840437109471/100000000000000 : ℝ)^3279 := by
    have hnat : (1085408413 : ℕ)^4303*100000000000000^3279 ≤ 44840437109471^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085408413 2000000000 44840437109471 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231401053/10000000000 : ℝ)^4303 ≤ (42731205205189/100000000000000 : ℝ)^3279 := by
    have hnat : (5231401053 : ℕ)^4303*100000000000000^3279 ≤ 42731205205189^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231401053 10000000000 42731205205189 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63792453/312500000 : ℝ), (1085408413/2000000000 : ℝ), (5231401053/10000000000 : ℝ)] ![(6214178838899/50000000000000 : ℝ), (44840437109471/100000000000000 : ℝ), (42731205205189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63792453/312500000 : ℝ)|^4303 ≤ (6214178838899/50000000000000 : ℝ)^3279
        have hw : |(-63792453/312500000 : ℝ)|=(63792453/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085408413/2000000000 : ℝ)|^4303 ≤ (44840437109471/100000000000000 : ℝ)^3279
        have hw : |(1085408413/2000000000 : ℝ)|=(1085408413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231401053/10000000000 : ℝ)|^4303 ≤ (42731205205189/100000000000000 : ℝ)^3279
        have hw : |(5231401053/10000000000 : ℝ)|=(5231401053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352649957/10000000000 : ℝ)*x 0 + (-1070671649/5000000000 : ℝ)*x 1 + (5231400883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352649957/10000000000 : ℝ)^4303 ≤ (550444491443/1250000000000 : ℝ)^3279 := by
    have hnat : (5352649957 : ℕ)^4303*1250000000000^3279 ≤ 550444491443^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352649957 10000000000 550444491443 1250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070671649/5000000000 : ℝ)^4303 ≤ (1654154661803/12500000000000 : ℝ)^3279 := by
    have hnat : (1070671649 : ℕ)^4303*12500000000000^3279 ≤ 1654154661803^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070671649 5000000000 1654154661803 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231400883/10000000000 : ℝ)^4303 ≤ (10682800845737/25000000000000 : ℝ)^3279 := by
    have hnat : (5231400883 : ℕ)^4303*25000000000000^3279 ≤ 10682800845737^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231400883 10000000000 10682800845737 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352649957/10000000000 : ℝ), (-1070671649/5000000000 : ℝ), (5231400883/10000000000 : ℝ)] ![(550444491443/1250000000000 : ℝ), (1654154661803/12500000000000 : ℝ), (10682800845737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352649957/10000000000 : ℝ)|^4303 ≤ (550444491443/1250000000000 : ℝ)^3279
        have hw : |(5352649957/10000000000 : ℝ)|=(5352649957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070671649/5000000000 : ℝ)|^4303 ≤ (1654154661803/12500000000000 : ℝ)^3279
        have hw : |(-1070671649/5000000000 : ℝ)|=(1070671649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231400883/10000000000 : ℝ)|^4303 ≤ (10682800845737/25000000000000 : ℝ)^3279
        have hw : |(5231400883/10000000000 : ℝ)|=(5231400883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338162559/2500000000 : ℝ)*x 0 + (2615700249/5000000000 : ℝ)*x 1 + (-428268687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338162559/2500000000 : ℝ)^4303 ≤ (2752222645471/6250000000000 : ℝ)^3279 := by
    have hnat : (1338162559 : ℕ)^4303*6250000000000^3279 ≤ 2752222645471^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338162559 2500000000 2752222645471 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615700249/5000000000 : ℝ)^4303 ≤ (21365599628053/50000000000000 : ℝ)^3279 := by
    have hnat : (2615700249 : ℕ)^4303*50000000000000^3279 ≤ 21365599628053^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615700249 5000000000 21365599628053 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428268687/2000000000 : ℝ)^4303 ≤ (2646647681093/20000000000000 : ℝ)^3279 := by
    have hnat : (428268687 : ℕ)^4303*20000000000000^3279 ≤ 2646647681093^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428268687 2000000000 2646647681093 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338162559/2500000000 : ℝ), (2615700249/5000000000 : ℝ), (-428268687/2000000000 : ℝ)] ![(2752222645471/6250000000000 : ℝ), (21365599628053/50000000000000 : ℝ), (2646647681093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338162559/2500000000 : ℝ)|^4303 ≤ (2752222645471/6250000000000 : ℝ)^3279
        have hw : |(1338162559/2500000000 : ℝ)|=(1338162559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615700249/5000000000 : ℝ)|^4303 ≤ (21365599628053/50000000000000 : ℝ)^3279
        have hw : |(2615700249/5000000000 : ℝ)|=(2615700249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428268687/2000000000 : ℝ)|^4303 ≤ (2646647681093/20000000000000 : ℝ)^3279
        have hw : |(-428268687/2000000000 : ℝ)|=(428268687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325299489/10000000000 : ℝ)*x 0 + (4124864289/10000000000 : ℝ)*x 1 + (2267401423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325299489/10000000000 : ℝ)^4303 ≤ (33292588049271/100000000000000 : ℝ)^3279 := by
    have hnat : (4325299489 : ℕ)^4303*100000000000000^3279 ≤ 33292588049271^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325299489 10000000000 33292588049271 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124864289/10000000000 : ℝ)^4303 ≤ (31282814600421/100000000000000 : ℝ)^3279 := by
    have hnat : (4124864289 : ℕ)^4303*100000000000000^3279 ≤ 31282814600421^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124864289 10000000000 31282814600421 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267401423/5000000000 : ℝ)^4303 ≤ (17712298666663/50000000000000 : ℝ)^3279 := by
    have hnat : (2267401423 : ℕ)^4303*50000000000000^3279 ≤ 17712298666663^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267401423 5000000000 17712298666663 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325299489/10000000000 : ℝ), (4124864289/10000000000 : ℝ), (2267401423/5000000000 : ℝ)] ![(33292588049271/100000000000000 : ℝ), (31282814600421/100000000000000 : ℝ), (17712298666663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325299489/10000000000 : ℝ)|^4303 ≤ (33292588049271/100000000000000 : ℝ)^3279
        have hw : |(4325299489/10000000000 : ℝ)|=(4325299489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124864289/10000000000 : ℝ)|^4303 ≤ (31282814600421/100000000000000 : ℝ)^3279
        have hw : |(4124864289/10000000000 : ℝ)|=(4124864289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267401423/5000000000 : ℝ)|^4303 ≤ (17712298666663/50000000000000 : ℝ)^3279
        have hw : |(2267401423/5000000000 : ℝ)|=(2267401423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041377767/10000000000 : ℝ)*x 0 + (2616107861/5000000000 : ℝ)*x 1 + (1356555611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041377767/10000000000 : ℝ)^4303 ≤ (6214255822689/50000000000000 : ℝ)^3279 := by
    have hnat : (2041377767 : ℕ)^4303*50000000000000^3279 ≤ 6214255822689^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041377767 10000000000 6214255822689 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616107861/5000000000 : ℝ)^4303 ≤ (42739937910531/100000000000000 : ℝ)^3279 := by
    have hnat : (2616107861 : ℕ)^4303*100000000000000^3279 ≤ 42739937910531^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616107861 5000000000 42739937910531 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356555611/2500000000 : ℝ)^4303 ≤ (22415775216041/50000000000000 : ℝ)^3279 := by
    have hnat : (1356555611 : ℕ)^4303*50000000000000^3279 ≤ 22415775216041^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356555611 2500000000 22415775216041 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041377767/10000000000 : ℝ), (2616107861/5000000000 : ℝ), (1356555611/2500000000 : ℝ)] ![(6214255822689/50000000000000 : ℝ), (42739937910531/100000000000000 : ℝ), (22415775216041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041377767/10000000000 : ℝ)|^4303 ≤ (6214255822689/50000000000000 : ℝ)^3279
        have hw : |(-2041377767/10000000000 : ℝ)|=(2041377767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616107861/5000000000 : ℝ)|^4303 ≤ (42739937910531/100000000000000 : ℝ)^3279
        have hw : |(2616107861/5000000000 : ℝ)|=(2616107861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356555611/2500000000 : ℝ)|^4303 ≤ (22415775216041/50000000000000 : ℝ)^3279
        have hw : |(1356555611/2500000000 : ℝ)|=(1356555611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651125133/5000000000 : ℝ)*x 0 + (-1946521551/10000000000 : ℝ)*x 1 + (135655561/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651125133/5000000000 : ℝ)^4303 ≤ (21746121901309/50000000000000 : ℝ)^3279 := by
    have hnat : (2651125133 : ℕ)^4303*50000000000000^3279 ≤ 21746121901309^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651125133 5000000000 21746121901309 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946521551/10000000000 : ℝ)^4303 ≤ (91220357757/781250000000 : ℝ)^3279 := by
    have hnat : (1946521551 : ℕ)^4303*781250000000^3279 ≤ 91220357757^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946521551 10000000000 91220357757 781250000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135655561/250000000 : ℝ)^4303 ≤ (22415775194357/50000000000000 : ℝ)^3279 := by
    have hnat : (135655561 : ℕ)^4303*50000000000000^3279 ≤ 22415775194357^3279*250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135655561 250000000 22415775194357 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651125133/5000000000 : ℝ), (-1946521551/10000000000 : ℝ), (135655561/250000000 : ℝ)] ![(21746121901309/50000000000000 : ℝ), (91220357757/781250000000 : ℝ), (22415775194357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651125133/5000000000 : ℝ)|^4303 ≤ (21746121901309/50000000000000 : ℝ)^3279
        have hw : |(2651125133/5000000000 : ℝ)|=(2651125133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946521551/10000000000 : ℝ)|^4303 ≤ (91220357757/781250000000 : ℝ)^3279
        have hw : |(-1946521551/10000000000 : ℝ)|=(1946521551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135655561/250000000 : ℝ)|^4303 ≤ (22415775194357/50000000000000 : ℝ)^3279
        have hw : |(135655561/250000000 : ℝ)|=(135655561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265112501/500000000 : ℝ)*x 0 + (542622261/1000000000 : ℝ)*x 1 + (-1946521653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265112501/500000000 : ℝ)^4303 ≤ (21746120577313/50000000000000 : ℝ)^3279 := by
    have hnat : (265112501 : ℕ)^4303*50000000000000^3279 ≤ 21746120577313^3279*500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265112501 500000000 21746120577313 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542622261/1000000000 : ℝ)^4303 ≤ (22415776115941/50000000000000 : ℝ)^3279 := by
    have hnat : (542622261 : ℕ)^4303*50000000000000^3279 ≤ 22415776115941^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542622261 1000000000 22415776115941 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1946521653/10000000000 : ℝ)^4303 ≤ (11676206595817/100000000000000 : ℝ)^3279 := by
    have hnat : (1946521653 : ℕ)^4303*100000000000000^3279 ≤ 11676206595817^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946521653 10000000000 11676206595817 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265112501/500000000 : ℝ), (542622261/1000000000 : ℝ), (-1946521653/10000000000 : ℝ)] ![(21746120577313/50000000000000 : ℝ), (22415776115941/50000000000000 : ℝ), (11676206595817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265112501/500000000 : ℝ)|^4303 ≤ (21746120577313/50000000000000 : ℝ)^3279
        have hw : |(265112501/500000000 : ℝ)|=(265112501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542622261/1000000000 : ℝ)|^4303 ≤ (22415776115941/50000000000000 : ℝ)^3279
        have hw : |(542622261/1000000000 : ℝ)|=(542622261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1946521653/10000000000 : ℝ)|^4303 ≤ (11676206595817/100000000000000 : ℝ)^3279
        have hw : |(-1946521653/10000000000 : ℝ)|=(1946521653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s3_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081334879/2500000000 : ℝ)*x 0 + (906619141/2000000000 : ℝ)*x 1 + (2063290929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081334879/2500000000 : ℝ)^4303 ≤ (16646496179863/50000000000000 : ℝ)^3279 := by
    have hnat : (1081334879 : ℕ)^4303*50000000000000^3279 ≤ 16646496179863^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081334879 2500000000 16646496179863 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906619141/2000000000 : ℝ)^4303 ≤ (3540709804839/10000000000000 : ℝ)^3279 := by
    have hnat : (906619141 : ℕ)^4303*10000000000000^3279 ≤ 3540709804839^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906619141 2000000000 3540709804839 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063290929/5000000000 : ℝ)^4303 ≤ (1251996383083/4000000000000 : ℝ)^3279 := by
    have hnat : (2063290929 : ℕ)^4303*4000000000000^3279 ≤ 1251996383083^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063290929 5000000000 1251996383083 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081334879/2500000000 : ℝ), (906619141/2000000000 : ℝ), (2063290929/5000000000 : ℝ)] ![(16646496179863/50000000000000 : ℝ), (3540709804839/10000000000000 : ℝ), (1251996383083/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081334879/2500000000 : ℝ)|^4303 ≤ (16646496179863/50000000000000 : ℝ)^3279
        have hw : |(1081334879/2500000000 : ℝ)|=(1081334879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906619141/2000000000 : ℝ)|^4303 ≤ (3540709804839/10000000000000 : ℝ)^3279
        have hw : |(906619141/2000000000 : ℝ)|=(906619141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063290929/5000000000 : ℝ)|^4303 ≤ (1251996383083/4000000000000 : ℝ)^3279
        have hw : |(2063290929/5000000000 : ℝ)|=(2063290929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (161/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2717/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (161/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4929/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (161/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4929/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (161/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4929/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (161/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4929/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (161/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4929/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (161/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4929/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4929/50000 : ℝ) ^ (2151/512 : ℝ) ≤ (2962810455985187/50000000000000000000 : ℝ) := by
    have hpowers : (4929/50000 : ℝ)^2151 ≤ (2962810455985187/50000000000000000000 : ℝ)^512 := by
      have hnat : (4929 : ℕ)^2151*50000000000000000000^512 ≤ 2962810455985187^512*50000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4929 50000 2962810455985187 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4929/50000 : ℝ)) (X := (2962810455985187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (161/1000 : ℝ) ^ (2151/512 : ℝ) ≤ (46530656326382841/100000000000000000000 : ℝ) := by
    have hpowers : (161/1000 : ℝ)^2151 ≤ (46530656326382841/100000000000000000000 : ℝ)^512 := by
      have hnat : (161 : ℕ)^2151*100000000000000000000^512 ≤ 46530656326382841^512*1000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        161 1000 46530656326382841 100000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (161/1000 : ℝ)) (X := (46530656326382841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002962810455985187/25000000000000000000 : ℝ) ≤ (5000141040489561/5000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25002962810455985187/25000000000000000000 : ℝ)^512 ≤ (5000141040489561/5000000000000000 : ℝ)^2151 := by
      have hnat : (25002962810455985187 : ℕ)^512*5000000000000000^2151 ≤ 5000141040489561^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002962810455985187 25000000000000000000 5000141040489561 5000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141040489561/5000000000000000 : ℝ)) (X := (25002962810455985187/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010491255447670643/20000000000000000000 : ℝ) ≤ (10001248361138167/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (20010491255447670643/20000000000000000000 : ℝ)^512 ≤ (10001248361138167/10000000000000000 : ℝ)^2151 := by
      have hnat : (20010491255447670643 : ℕ)^512*10000000000000000^2151 ≤ 10001248361138167^2151*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010491255447670643 20000000000000000000 10001248361138167 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001248361138167/10000000000000000 : ℝ)) (X := (20010491255447670643/20000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046530656326382841/50000000000000000000 : ℝ) ≤ (2500553660324303/2500000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (50046530656326382841/50000000000000000000 : ℝ)^512 ≤ (2500553660324303/2500000000000000 : ℝ)^2151 := by
      have hnat : (50046530656326382841 : ℕ)^512*2500000000000000^2151 ≤ 2500553660324303^2151*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046530656326382841 50000000000000000000 2500553660324303 2500000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500553660324303/2500000000000000 : ℝ)) (X := (50046530656326382841/50000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2962810455985187/50000000000000000000 : ℝ) ≤ ((3900169348115996769/3901250000000000000 : ℝ)+2*(193256031809/124840000000000 : ℝ)*(4929/50000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (3900169348115996769/3901250000000000000 : ℝ)+2*(193256031809/124840000000000 : ℝ)*(4929/50000 : ℝ)=(5000141040489561/5000000000000000 : ℝ) by norm_num, show 1+2*(2962810455985187/50000000000000000000 : ℝ)=(25002962810455985187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46530656326382841/100000000000000000000 : ℝ)+(2962810455985187/50000000000000000000 : ℝ) ≤ ((3900169348115996769/3901250000000000000 : ℝ)+(193256031809/124840000000000 : ℝ)*((161/1000 : ℝ)+(4929/50000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (3900169348115996769/3901250000000000000 : ℝ)+(193256031809/124840000000000 : ℝ)*((161/1000 : ℝ)+(4929/50000 : ℝ))=(10001248361138167/10000000000000000 : ℝ) by norm_num, show 1+(46530656326382841/100000000000000000000 : ℝ)+(2962810455985187/50000000000000000000 : ℝ)=(20010491255447670643/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46530656326382841/100000000000000000000 : ℝ) ≤ ((3900169348115996769/3901250000000000000 : ℝ)+2*(193256031809/124840000000000 : ℝ)*(161/1000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (3900169348115996769/3901250000000000000 : ℝ)+2*(193256031809/124840000000000 : ℝ)*(161/1000 : ℝ)=(2500553660324303/2500000000000000 : ℝ) by norm_num, show 1+2*(46530656326382841/100000000000000000000 : ℝ)=(50046530656326382841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3900169348115996769/3901250000000000000 : ℝ)*(X 1 0+X 2 0)+(193256031809/124840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (4929/50000 : ℝ)) (hi := (161/1000 : ℝ)) (c := (3900169348115996769/3901250000000000000 : ℝ)) (alpha := (193256031809/124840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3900169348115996769/3901250000000000000 : ℝ)*(X 0 1+X 2 1)+(193256031809/124840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (4929/50000 : ℝ)) (hi := (161/1000 : ℝ)) (c := (3900169348115996769/3901250000000000000 : ℝ)) (alpha := (193256031809/124840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3900169348115996769/3901250000000000000 : ℝ)*(X 0 2+X 1 2)+(193256031809/124840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (4929/50000 : ℝ)) (hi := (161/1000 : ℝ)) (c := (3900169348115996769/3901250000000000000 : ℝ)) (alpha := (193256031809/124840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63792453/312500000 : ℝ)*X 0 0+(1085408413/2000000000 : ℝ)*X 0 1+(5231401053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352649957/10000000000 : ℝ)*X 1 0+(-1070671649/5000000000 : ℝ)*X 1 1+(5231400883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338162559/2500000000 : ℝ)*X 2 0+(2615700249/5000000000 : ℝ)*X 2 1+(-428268687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325299489/10000000000 : ℝ)*X 0 0+(4124864289/10000000000 : ℝ)*X 0 1+(2267401423/5000000000 : ℝ)*X 0 2+(4325299489/10000000000 : ℝ)*X 1 0+(4124864289/10000000000 : ℝ)*X 1 1+(2267401423/5000000000 : ℝ)*X 1 2+(4325299489/10000000000 : ℝ)*X 2 0+(4124864289/10000000000 : ℝ)*X 2 1+(2267401423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2041377767/10000000000 : ℝ)*X 0 0+(2616107861/5000000000 : ℝ)*X 0 1+(1356555611/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651125133/5000000000 : ℝ)*X 1 0+(-1946521551/10000000000 : ℝ)*X 1 1+(135655561/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265112501/500000000 : ℝ)*X 2 0+(542622261/1000000000 : ℝ)*X 2 1+(-1946521653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081334879/2500000000 : ℝ)*X 0 0+(906619141/2000000000 : ℝ)*X 0 1+(2063290929/5000000000 : ℝ)*X 0 2+(1081334879/2500000000 : ℝ)*X 1 0+(906619141/2000000000 : ℝ)*X 1 1+(2063290929/5000000000 : ℝ)*X 1 2+(1081334879/2500000000 : ℝ)*X 2 0+(906619141/2000000000 : ℝ)*X 2 1+(2063290929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80455813252718773367287797/7802500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018171241/50000000000000 : ℝ)*(base19) + (997380127/50000000000000 : ℝ)*(base23) + (32973437/20000000000000 : ℝ)*(lower2) + (76723889/20000000000000 : ℝ)*(upper3) + (50724843/100000000000000 : ℝ)*(upper5) + (471929885834153/12500000000000 : ℝ)*(major0) + (471929885834153/12500000000000 : ℝ)*(major1) + (151017563466929/4000000000000 : ℝ)*(major2) + (2555717068090057/50000000000000 : ℝ)*(sp0) + (79866527998037/1562500000000 : ℝ)*(sp1) + (5111457833456597/100000000000000 : ℝ)*(sp2) + (1219700405561159/50000000000000 : ℝ)*(sp3) + (25692036737/100000000000000 : ℝ)*(sp4) + (8595144589/50000000000000 : ℝ)*(sp7) + (304927250176437/12500000000000 : ℝ)*(f.failure) + (5111459828216851/100000000000000 : ℝ)*(f.sum) + (47089112065173/12484000000000000000000000000 : ℝ)*base65 + (1731821182861702747/195062500000000000000000000000000 : ℝ)*base68 + (148631116411812401/15605000000000000000000000000000 : ℝ)*base69 + (164635232025172253/195062500000000000000000000000000 : ℝ)*base71 + (42556222356111/12484000000000000000000000000 : ℝ)*base74 + (135818136889042401/15605000000000000000000000000000 : ℝ)*base75 + (47530503346648343/48765625000000000000000000000000 : ℝ)*base78 + (54935464306851657/48765625000000000000000000000000 : ℝ)*base79 + (2047075625789/3121000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3101681/625000000000000000000 : ℝ)*base89 + (3101681/625000000000000000000 : ℝ)*base91 + (3148319/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225973816136460340842123261/19506250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1081870499/50000000000000 : ℝ)*(base19) + (41478287/2000000000000 : ℝ)*(base23) + (221712859/100000000000000 : ℝ)*(upper3) + (43774027/50000000000000 : ℝ)*(lower4) + (130298929/50000000000000 : ℝ)*(upper5) + (380719890985373/10000000000000 : ℝ)*(major0) + (380719890985373/10000000000000 : ℝ)*(major1) + (380719890985373/10000000000000 : ℝ)*(major2) + (39311479299/100000000000000 : ℝ)*(sp1) + (18824510431/50000000000000 : ℝ)*(sp2) + (2577229255947257/50000000000000 : ℝ)*(sp4) + (644302129584277/12500000000000 : ℝ)*(sp5) + (5154418788959301/100000000000000 : ℝ)*(sp6) + (61498473041417/2500000000000 : ℝ)*(sp7) + (61498473041417/2500000000000 : ℝ)*(f.failure) + (2577229255947257/50000000000000 : ℝ)*(f.sum) + (888801370897/3121000000000000000000000000 : ℝ)*base66 + (388185474619183913/39012500000000000000000000000000 : ℝ)*base68 + (283400831330533913/39012500000000000000000000000000 : ℝ)*base70 + (168566165237821413/39012500000000000000000000000000 : ℝ)*base72 + (8029001586663/3121000000000000000000000000 : ℝ)*base73 + (191531263922453587/39012500000000000000000000000000 : ℝ)*base75 + (118613696227983913/39012500000000000000000000000000 : ℝ)*base78 + (236840194591591087/39012500000000000000000000000000 : ℝ)*base79 + (3696192315457/780250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (166421/125000000000000000000 : ℝ)*base89 + (166421/125000000000000000000 : ℝ)*base91 + (166421/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (161/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_s4_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042809609/10000000000 : ℝ)*x 0 + (5415201321/10000000000 : ℝ)*x 1 + (5242288997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042809609/10000000000 : ℝ)^4303 ≤ (3109988189919/25000000000000 : ℝ)^3279 := by
    have hnat : (2042809609 : ℕ)^4303*25000000000000^3279 ≤ 3109988189919^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042809609 10000000000 3109988189919 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415201321/10000000000 : ℝ)^4303 ≤ (44712095489503/100000000000000 : ℝ)^3279 := by
    have hnat : (5415201321 : ℕ)^4303*100000000000000^3279 ≤ 44712095489503^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415201321 10000000000 44712095489503 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242288997/10000000000 : ℝ)^4303 ≤ (42847951735209/100000000000000 : ℝ)^3279 := by
    have hnat : (5242288997 : ℕ)^4303*100000000000000^3279 ≤ 42847951735209^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242288997 10000000000 42847951735209 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042809609/10000000000 : ℝ), (5415201321/10000000000 : ℝ), (5242288997/10000000000 : ℝ)] ![(3109988189919/25000000000000 : ℝ), (44712095489503/100000000000000 : ℝ), (42847951735209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042809609/10000000000 : ℝ)|^4303 ≤ (3109988189919/25000000000000 : ℝ)^3279
        have hw : |(-2042809609/10000000000 : ℝ)|=(2042809609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415201321/10000000000 : ℝ)|^4303 ≤ (44712095489503/100000000000000 : ℝ)^3279
        have hw : |(5415201321/10000000000 : ℝ)|=(5415201321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242288997/10000000000 : ℝ)|^4303 ≤ (42847951735209/100000000000000 : ℝ)^3279
        have hw : |(5242288997/10000000000 : ℝ)|=(5242288997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334352001/625000000 : ℝ)*x 0 + (-266369607/1250000000 : ℝ)*x 1 + (1310572217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334352001/625000000 : ℝ)^4303 ≤ (11000745090907/25000000000000 : ℝ)^3279 := by
    have hnat : (334352001 : ℕ)^4303*25000000000000^3279 ≤ 11000745090907^3279*625000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334352001 625000000 11000745090907 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266369607/1250000000 : ℝ)^4303 ≤ (1643633659137/12500000000000 : ℝ)^3279 := by
    have hnat : (266369607 : ℕ)^4303*12500000000000^3279 ≤ 1643633659137^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266369607 1250000000 1643633659137 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310572217/2500000000 : ℝ)^4303 ≤ (42847950351551/100000000000000 : ℝ)^3279 := by
    have hnat : (1310572217 : ℕ)^4303*100000000000000^3279 ≤ 42847950351551^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310572217 2500000000 42847950351551 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334352001/625000000 : ℝ), (-266369607/1250000000 : ℝ), (1310572217/2500000000 : ℝ)] ![(11000745090907/25000000000000 : ℝ), (1643633659137/12500000000000 : ℝ), (42847950351551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334352001/625000000 : ℝ)|^4303 ≤ (11000745090907/25000000000000 : ℝ)^3279
        have hw : |(334352001/625000000 : ℝ)|=(334352001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266369607/1250000000 : ℝ)|^4303 ≤ (1643633659137/12500000000000 : ℝ)^3279
        have hw : |(-266369607/1250000000 : ℝ)|=(266369607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310572217/2500000000 : ℝ)|^4303 ≤ (42847950351551/100000000000000 : ℝ)^3279
        have hw : |(1310572217/2500000000 : ℝ)|=(1310572217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349632367/10000000000 : ℝ)*x 0 + (524228863/1000000000 : ℝ)*x 1 + (-1065478351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349632367/10000000000 : ℝ)^4303 ≤ (11000746038093/25000000000000 : ℝ)^3279 := by
    have hnat : (5349632367 : ℕ)^4303*25000000000000^3279 ≤ 11000746038093^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349632367 10000000000 11000746038093 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524228863/1000000000 : ℝ)^4303 ≤ (10711986949689/25000000000000 : ℝ)^3279 := by
    have hnat : (524228863 : ℕ)^4303*25000000000000^3279 ≤ 10711986949689^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524228863 1000000000 10711986949689 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065478351/5000000000 : ℝ)^4303 ≤ (13149068026083/100000000000000 : ℝ)^3279 := by
    have hnat : (1065478351 : ℕ)^4303*100000000000000^3279 ≤ 13149068026083^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065478351 5000000000 13149068026083 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349632367/10000000000 : ℝ), (524228863/1000000000 : ℝ), (-1065478351/5000000000 : ℝ)] ![(11000746038093/25000000000000 : ℝ), (10711986949689/25000000000000 : ℝ), (13149068026083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349632367/10000000000 : ℝ)|^4303 ≤ (11000746038093/25000000000000 : ℝ)^3279
        have hw : |(5349632367/10000000000 : ℝ)|=(5349632367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524228863/1000000000 : ℝ)|^4303 ≤ (10711986949689/25000000000000 : ℝ)^3279
        have hw : |(524228863/1000000000 : ℝ)|=(524228863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065478351/5000000000 : ℝ)|^4303 ≤ (13149068026083/100000000000000 : ℝ)^3279
        have hw : |(-1065478351/5000000000 : ℝ)|=(1065478351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865236369/2000000000 : ℝ)*x 0 + (4148567049/10000000000 : ℝ)*x 1 + (56386017/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865236369/2000000000 : ℝ)^4303 ≤ (33301500948137/100000000000000 : ℝ)^3279 := by
    have hnat : (865236369 : ℕ)^4303*100000000000000^3279 ≤ 33301500948137^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865236369 2000000000 33301500948137 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148567049/10000000000 : ℝ)^4303 ≤ (7879731097359/25000000000000 : ℝ)^3279 := by
    have hnat : (4148567049 : ℕ)^4303*25000000000000^3279 ≤ 7879731097359^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148567049 10000000000 7879731097359 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56386017/125000000 : ℝ)^4303 ≤ (4397446831017/12500000000000 : ℝ)^3279 := by
    have hnat : (56386017 : ℕ)^4303*12500000000000^3279 ≤ 4397446831017^3279*125000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56386017 125000000 4397446831017 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865236369/2000000000 : ℝ), (4148567049/10000000000 : ℝ), (56386017/125000000 : ℝ)] ![(33301500948137/100000000000000 : ℝ), (7879731097359/25000000000000 : ℝ), (4397446831017/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865236369/2000000000 : ℝ)|^4303 ≤ (33301500948137/100000000000000 : ℝ)^3279
        have hw : |(865236369/2000000000 : ℝ)|=(865236369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148567049/10000000000 : ℝ)|^4303 ≤ (7879731097359/25000000000000 : ℝ)^3279
        have hw : |(4148567049/10000000000 : ℝ)|=(4148567049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56386017/125000000 : ℝ)|^4303 ≤ (4397446831017/12500000000000 : ℝ)^3279
        have hw : |(56386017/125000000 : ℝ)|=(56386017/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-510705789/2500000000 : ℝ)*x 0 + (5242925731/10000000000 : ℝ)*x 1 + (5414560993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510705789/2500000000 : ℝ)^4303 ≤ (12440061018761/100000000000000 : ℝ)^3279 := by
    have hnat : (510705789 : ℕ)^4303*100000000000000^3279 ≤ 12440061018761^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510705789 2500000000 12440061018761 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242925731/10000000000 : ℝ)^4303 ≤ (21427390746589/50000000000000 : ℝ)^3279 := by
    have hnat : (5242925731 : ℕ)^4303*50000000000000^3279 ≤ 21427390746589^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242925731 10000000000 21427390746589 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414560993/10000000000 : ℝ)^4303 ≤ (44705157481117/100000000000000 : ℝ)^3279 := by
    have hnat : (5414560993 : ℕ)^4303*100000000000000^3279 ≤ 44705157481117^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414560993 10000000000 44705157481117 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510705789/2500000000 : ℝ), (5242925731/10000000000 : ℝ), (5414560993/10000000000 : ℝ)] ![(12440061018761/100000000000000 : ℝ), (21427390746589/50000000000000 : ℝ), (44705157481117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510705789/2500000000 : ℝ)|^4303 ≤ (12440061018761/100000000000000 : ℝ)^3279
        have hw : |(-510705789/2500000000 : ℝ)|=(510705789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242925731/10000000000 : ℝ)|^4303 ≤ (21427390746589/50000000000000 : ℝ)^3279
        have hw : |(5242925731/10000000000 : ℝ)|=(5242925731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414560993/10000000000 : ℝ)|^4303 ≤ (44705157481117/100000000000000 : ℝ)^3279
        have hw : |(5414560993/10000000000 : ℝ)|=(5414560993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305088611/10000000000 : ℝ)*x 0 + (-15669479/80000000 : ℝ)*x 1 + (2707280389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305088611/10000000000 : ℝ)^4303 ≤ (21761399426297/50000000000000 : ℝ)^3279 := by
    have hnat : (5305088611 : ℕ)^4303*50000000000000^3279 ≤ 21761399426297^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305088611 10000000000 21761399426297 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15669479/80000000 : ℝ)^4303 ≤ (5886022991239/50000000000000 : ℝ)^3279 := by
    have hnat : (15669479 : ℕ)^4303*50000000000000^3279 ≤ 5886022991239^3279*80000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15669479 80000000 5886022991239 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707280389/5000000000 : ℝ)^4303 ≤ (44705155151617/100000000000000 : ℝ)^3279 := by
    have hnat : (2707280389 : ℕ)^4303*100000000000000^3279 ≤ 44705155151617^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707280389 5000000000 44705155151617 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305088611/10000000000 : ℝ), (-15669479/80000000 : ℝ), (2707280389/5000000000 : ℝ)] ![(21761399426297/50000000000000 : ℝ), (5886022991239/50000000000000 : ℝ), (44705155151617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305088611/10000000000 : ℝ)|^4303 ≤ (21761399426297/50000000000000 : ℝ)^3279
        have hw : |(5305088611/10000000000 : ℝ)|=(5305088611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15669479/80000000 : ℝ)|^4303 ≤ (5886022991239/50000000000000 : ℝ)^3279
        have hw : |(-15669479/80000000 : ℝ)|=(15669479/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707280389/5000000000 : ℝ)|^4303 ≤ (44705155151617/100000000000000 : ℝ)^3279
        have hw : |(2707280389/5000000000 : ℝ)|=(2707280389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305088419/10000000000 : ℝ)*x 0 + (5414560877/10000000000 : ℝ)*x 1 + (-979342501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305088419/10000000000 : ℝ)^4303 ≤ (43522796785523/100000000000000 : ℝ)^3279 := by
    have hnat : (5305088419 : ℕ)^4303*100000000000000^3279 ≤ 43522796785523^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305088419 10000000000 43522796785523 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414560877/10000000000 : ℝ)^4303 ≤ (4470515622427/10000000000000 : ℝ)^3279 := by
    have hnat : (5414560877 : ℕ)^4303*10000000000000^3279 ≤ 4470515622427^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414560877 10000000000 4470515622427 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979342501/5000000000 : ℝ)^4303 ≤ (588602349207/5000000000000 : ℝ)^3279 := by
    have hnat : (979342501 : ℕ)^4303*5000000000000^3279 ≤ 588602349207^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979342501 5000000000 588602349207 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305088419/10000000000 : ℝ), (5414560877/10000000000 : ℝ), (-979342501/5000000000 : ℝ)] ![(43522796785523/100000000000000 : ℝ), (4470515622427/10000000000000 : ℝ), (588602349207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305088419/10000000000 : ℝ)|^4303 ≤ (43522796785523/100000000000000 : ℝ)^3279
        have hw : |(5305088419/10000000000 : ℝ)|=(5305088419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414560877/10000000000 : ℝ)|^4303 ≤ (4470515622427/10000000000000 : ℝ)^3279
        have hw : |(5414560877/10000000000 : ℝ)|=(5414560877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979342501/5000000000 : ℝ)|^4303 ≤ (588602349207/5000000000000 : ℝ)^3279
        have hw : |(-979342501/5000000000 : ℝ)|=(979342501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s4_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326209383/10000000000 : ℝ)*x 0 + (4509546549/10000000000 : ℝ)*x 1 + (4149909191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326209383/10000000000 : ℝ)^4303 ≤ (6660355825101/20000000000000 : ℝ)^3279 := by
    have hnat : (4326209383 : ℕ)^4303*20000000000000^3279 ≤ 6660355825101^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326209383 10000000000 6660355825101 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509546549/10000000000 : ℝ)^4303 ≤ (17582957196399/50000000000000 : ℝ)^3279 := by
    have hnat : (4509546549 : ℕ)^4303*50000000000000^3279 ≤ 17582957196399^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509546549 10000000000 17582957196399 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149909191/10000000000 : ℝ)^4303 ≤ (3153230646901/10000000000000 : ℝ)^3279 := by
    have hnat : (4149909191 : ℕ)^4303*10000000000000^3279 ≤ 3153230646901^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149909191 10000000000 3153230646901 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326209383/10000000000 : ℝ), (4509546549/10000000000 : ℝ), (4149909191/10000000000 : ℝ)] ![(6660355825101/20000000000000 : ℝ), (17582957196399/50000000000000 : ℝ), (3153230646901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326209383/10000000000 : ℝ)|^4303 ≤ (6660355825101/20000000000000 : ℝ)^3279
        have hw : |(4326209383/10000000000 : ℝ)|=(4326209383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509546549/10000000000 : ℝ)|^4303 ≤ (17582957196399/50000000000000 : ℝ)^3279
        have hw : |(4509546549/10000000000 : ℝ)|=(4509546549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149909191/10000000000 : ℝ)|^4303 ≤ (3153230646901/10000000000000 : ℝ)^3279
        have hw : |(4149909191/10000000000 : ℝ)|=(4149909191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2717/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2717/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2717/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2717/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2717/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2717/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2717/25000 : ℝ) ^ (2151/512 : ℝ) ≤ (8926864295877073/100000000000000000000 : ℝ) := by
    have hpowers : (2717/25000 : ℝ)^2151 ≤ (8926864295877073/100000000000000000000 : ℝ)^512 := by
      have hnat : (2717 : ℕ)^2151*100000000000000000000^512 ≤ 8926864295877073^512*25000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2717 25000 8926864295877073 100000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2717/25000 : ℝ)) (X := (8926864295877073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15009/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (6767717285079/19531250000000000 : ℝ) := by
    have hpowers : (15009/100000 : ℝ)^2151 ≤ (6767717285079/19531250000000000 : ℝ)^512 := by
      have hnat : (15009 : ℕ)^2151*19531250000000000^512 ≤ 6767717285079^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15009 100000 6767717285079 19531250000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15009/100000 : ℝ)) (X := (6767717285079/19531250000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008926864295877073/50000000000000000000 : ℝ) ≤ (10000424941298221/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (50008926864295877073/50000000000000000000 : ℝ)^512 ≤ (10000424941298221/10000000000000000 : ℝ)^2151 := by
      have hnat : (50008926864295877073 : ℕ)^512*10000000000000000^2151 ≤ 10000424941298221^2151*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008926864295877073 50000000000000000000 10000424941298221 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424941298221/10000000000000000 : ℝ)) (X := (50008926864295877073/50000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043577576795481553/100000000000000000000 : ℝ) ≤ (10001037099766611/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (100043577576795481553/100000000000000000000 : ℝ)^512 ≤ (10001037099766611/10000000000000000 : ℝ)^2151 := by
      have hnat : (100043577576795481553 : ℕ)^512*10000000000000000^2151 ≤ 10001037099766611^2151*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043577576795481553 100000000000000000000 10001037099766611 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001037099766611/10000000000000000 : ℝ)) (X := (100043577576795481553/100000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (9772392717285079/9765625000000000 : ℝ) ≤ (10001649258235001/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (9772392717285079/9765625000000000 : ℝ)^512 ≤ (10001649258235001/10000000000000000 : ℝ)^2151 := by
      have hnat : (9772392717285079 : ℕ)^512*10000000000000000^2151 ≤ 10001649258235001^2151*9765625000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9772392717285079 9765625000000000 10001649258235001 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001649258235001/10000000000000000 : ℝ)) (X := (9772392717285079/9765625000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8926864295877073/100000000000000000000 : ℝ) ≤ ((41398453805447008121/41410000000000000000 : ℝ)+2*(61215846839/41410000000000 : ℝ)*(2717/25000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (41398453805447008121/41410000000000000000 : ℝ)+2*(61215846839/41410000000000 : ℝ)*(2717/25000 : ℝ)=(10000424941298221/10000000000000000 : ℝ) by norm_num, show 1+2*(8926864295877073/100000000000000000000 : ℝ)=(50008926864295877073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6767717285079/19531250000000000 : ℝ)+(8926864295877073/100000000000000000000 : ℝ) ≤ ((41398453805447008121/41410000000000000000 : ℝ)+(61215846839/41410000000000 : ℝ)*((15009/100000 : ℝ)+(2717/25000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (41398453805447008121/41410000000000000000 : ℝ)+(61215846839/41410000000000 : ℝ)*((15009/100000 : ℝ)+(2717/25000 : ℝ))=(10001037099766611/10000000000000000 : ℝ) by norm_num, show 1+(6767717285079/19531250000000000 : ℝ)+(8926864295877073/100000000000000000000 : ℝ)=(100043577576795481553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6767717285079/19531250000000000 : ℝ) ≤ ((41398453805447008121/41410000000000000000 : ℝ)+2*(61215846839/41410000000000 : ℝ)*(15009/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (41398453805447008121/41410000000000000000 : ℝ)+2*(61215846839/41410000000000 : ℝ)*(15009/100000 : ℝ)=(10001649258235001/10000000000000000 : ℝ) by norm_num, show 1+2*(6767717285079/19531250000000000 : ℝ)=(9772392717285079/9765625000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41398453805447008121/41410000000000000000 : ℝ)*(X 1 0+X 2 0)+(61215846839/41410000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (41398453805447008121/41410000000000000000 : ℝ)) (alpha := (61215846839/41410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41398453805447008121/41410000000000000000 : ℝ)*(X 0 1+X 2 1)+(61215846839/41410000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (41398453805447008121/41410000000000000000 : ℝ)) (alpha := (61215846839/41410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41398453805447008121/41410000000000000000 : ℝ)*(X 0 2+X 1 2)+(61215846839/41410000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15009/100000 : ℝ)) (c := (41398453805447008121/41410000000000000000 : ℝ)) (alpha := (61215846839/41410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2042809609/10000000000 : ℝ)*X 0 0+(5415201321/10000000000 : ℝ)*X 0 1+(5242288997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334352001/625000000 : ℝ)*X 1 0+(-266369607/1250000000 : ℝ)*X 1 1+(1310572217/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349632367/10000000000 : ℝ)*X 2 0+(524228863/1000000000 : ℝ)*X 2 1+(-1065478351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865236369/2000000000 : ℝ)*X 0 0+(4148567049/10000000000 : ℝ)*X 0 1+(56386017/125000000 : ℝ)*X 0 2+(865236369/2000000000 : ℝ)*X 1 0+(4148567049/10000000000 : ℝ)*X 1 1+(56386017/125000000 : ℝ)*X 1 2+(865236369/2000000000 : ℝ)*X 2 0+(4148567049/10000000000 : ℝ)*X 2 1+(56386017/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-510705789/2500000000 : ℝ)*X 0 0+(5242925731/10000000000 : ℝ)*X 0 1+(5414560993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305088611/10000000000 : ℝ)*X 1 0+(-15669479/80000000 : ℝ)*X 1 1+(2707280389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305088419/10000000000 : ℝ)*X 2 0+(5414560877/10000000000 : ℝ)*X 2 1+(-979342501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326209383/10000000000 : ℝ)*X 0 0+(4509546549/10000000000 : ℝ)*X 0 1+(4149909191/10000000000 : ℝ)*X 0 2+(4326209383/10000000000 : ℝ)*X 1 0+(4509546549/10000000000 : ℝ)*X 1 1+(4149909191/10000000000 : ℝ)*X 1 2+(4326209383/10000000000 : ℝ)*X 2 0+(4509546549/10000000000 : ℝ)*X 2 1+(4149909191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418292281667987088423172461/82820000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1401942311/100000000000000 : ℝ)*(base19) + (615646339/50000000000000 : ℝ)*(base23) + (147142959/50000000000000 : ℝ)*(lower2) + (79411339/50000000000000 : ℝ)*(upper3) + (980333/100000000000000 : ℝ)*(upper5) + (533961648812739/12500000000000 : ℝ)*(major0) + (533961648812739/12500000000000 : ℝ)*(major1) + (4271693190501913/100000000000000 : ℝ)*(major2) + (722912403446151/12500000000000 : ℝ)*(sp0) + (1445830748434753/25000000000000 : ℝ)*(sp1) + (1156664632877729/20000000000000 : ℝ)*(sp2) + (1380022597027217/50000000000000 : ℝ)*(sp3) + (5033622423/20000000000000 : ℝ)*(sp4) + (8311457043/50000000000000 : ℝ)*(sp7) + (2760061816968521/100000000000000 : ℝ)*(f.failure) + (5783324395681323/100000000000000 : ℝ)*(f.sum) + (2675326262279/4141000000000000000000000000 : ℝ)*base65 + (2864525759075503419/517625000000000000000000000000000 : ℝ)*base67 + (65882679385928035473/4141000000000000000000000000000000 : ℝ)*base69 + (4477176618815371581/517625000000000000000000000000000 : ℝ)*base72 + (23687161309847/4141000000000000000000000000 : ℝ)*base73 + (54201813483783035473/4141000000000000000000000000000000 : ℝ)*base75 + (217347026611878419/517625000000000000000000000000000 : ℝ)*base77 + (2143715149233503419/517625000000000000000000000000000 : ℝ)*base79 + (911760065991/207050000000000000000000000 : ℝ)*base81 + (49654773/5000000000000000000000 : ℝ)*base89 + (49654773/5000000000000000000000 : ℝ)*base91 + (345227/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2017887803144223242842277901/414100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21832777/2000000000000 : ℝ)*(base19) + (942791529/100000000000000 : ℝ)*(base23) + (37321097/50000000000000 : ℝ)*(upper3) + (29622681/50000000000000 : ℝ)*(lower4) + (21629269/12500000000000 : ℝ)*(upper5) + (860688514882727/20000000000000 : ℝ)*(major0) + (860688514882727/20000000000000 : ℝ)*(major1) + (860688514882727/20000000000000 : ℝ)*(major2) + (3490488047/20000000000000 : ℝ)*(sp1) + (5768913971/50000000000000 : ℝ)*(sp2) + (2913154497144421/50000000000000 : ℝ)*(sp4) + (2913145225104879/50000000000000 : ℝ)*(sp5) + (5826296513669371/100000000000000 : ℝ)*(sp6) + (43446499876669/1562500000000 : ℝ)*(sp7) + (43446499876669/1562500000000 : ℝ)*(f.failure) + (2913154497144421/50000000000000 : ℝ)*(f.sum) + (6084948859143/2070500000000000000000000000 : ℝ)*base66 + (2805389411420574033/828200000000000000000000000000000 : ℝ)*base68 + (7630167059556225967/828200000000000000000000000000000 : ℝ)*base69 + (13904356788328574033/828200000000000000000000000000000 : ℝ)*base72 + (3242282554149/1035250000000000000000000000 : ℝ)*base73 + (6653910642707374033/828200000000000000000000000000000 : ℝ)*base76 + (6018139708401574033/828200000000000000000000000000000 : ℝ)*base78 + (17564434466614425967/828200000000000000000000000000000 : ℝ)*base79 + (45622601197/8282000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (51053/78125000000000000000 : ℝ)*base90 + (51053/78125000000000000000 : ℝ)*base92 + (51053/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1343_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_s5_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-408612119/2000000000 : ℝ)*x 0 + (5413039103/10000000000 : ℝ)*x 1 + (1048857197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408612119/2000000000 : ℝ)^4303 ≤ (3110489629493/25000000000000 : ℝ)^3279 := by
    have hnat : (408612119 : ℕ)^4303*25000000000000^3279 ≤ 3110489629493^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408612119 2000000000 3110489629493 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413039103/10000000000 : ℝ)^4303 ≤ (22344334350823/50000000000000 : ℝ)^3279 := by
    have hnat : (5413039103 : ℕ)^4303*50000000000000^3279 ≤ 22344334350823^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413039103 10000000000 22344334350823 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048857197/2000000000 : ℝ)^4303 ≤ (5358671595477/12500000000000 : ℝ)^3279 := by
    have hnat : (1048857197 : ℕ)^4303*12500000000000^3279 ≤ 5358671595477^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048857197 2000000000 5358671595477 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408612119/2000000000 : ℝ), (5413039103/10000000000 : ℝ), (1048857197/2000000000 : ℝ)] ![(3110489629493/25000000000000 : ℝ), (22344334350823/50000000000000 : ℝ), (5358671595477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408612119/2000000000 : ℝ)|^4303 ≤ (3110489629493/25000000000000 : ℝ)^3279
        have hw : |(-408612119/2000000000 : ℝ)|=(408612119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413039103/10000000000 : ℝ)|^4303 ≤ (22344334350823/50000000000000 : ℝ)^3279
        have hw : |(5413039103/10000000000 : ℝ)|=(5413039103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048857197/2000000000 : ℝ)|^4303 ≤ (5358671595477/12500000000000 : ℝ)^3279
        have hw : |(1048857197/2000000000 : ℝ)|=(1048857197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349079367/10000000000 : ℝ)*x 0 + (-2129047711/10000000000 : ℝ)*x 1 + (5244285983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349079367/10000000000 : ℝ)^4303 ≤ (4399701508827/10000000000000 : ℝ)^3279 := by
    have hnat : (5349079367 : ℕ)^4303*10000000000000^3279 ≤ 4399701508827^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349079367 10000000000 4399701508827 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129047711/10000000000 : ℝ)^4303 ≤ (13133612158411/100000000000000 : ℝ)^3279 := by
    have hnat : (2129047711 : ℕ)^4303*100000000000000^3279 ≤ 13133612158411^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129047711 10000000000 13133612158411 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244285983/10000000000 : ℝ)^4303 ≤ (21434686371181/50000000000000 : ℝ)^3279 := by
    have hnat : (5244285983 : ℕ)^4303*50000000000000^3279 ≤ 21434686371181^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244285983 10000000000 21434686371181 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349079367/10000000000 : ℝ), (-2129047711/10000000000 : ℝ), (5244285983/10000000000 : ℝ)] ![(4399701508827/10000000000000 : ℝ), (13133612158411/100000000000000 : ℝ), (21434686371181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349079367/10000000000 : ℝ)|^4303 ≤ (4399701508827/10000000000000 : ℝ)^3279
        have hw : |(5349079367/10000000000 : ℝ)|=(5349079367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129047711/10000000000 : ℝ)|^4303 ≤ (13133612158411/100000000000000 : ℝ)^3279
        have hw : |(-2129047711/10000000000 : ℝ)|=(2129047711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244285983/10000000000 : ℝ)|^4303 ≤ (21434686371181/50000000000000 : ℝ)^3279
        have hw : |(5244285983/10000000000 : ℝ)|=(5244285983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534907937/1000000000 : ℝ)*x 0 + (524428599/1000000000 : ℝ)*x 1 + (-2129047697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534907937/1000000000 : ℝ)^4303 ≤ (43997015120651/100000000000000 : ℝ)^3279 := by
    have hnat : (534907937 : ℕ)^4303*100000000000000^3279 ≤ 43997015120651^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534907937 1000000000 43997015120651 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524428599/1000000000 : ℝ)^4303 ≤ (42869372817453/100000000000000 : ℝ)^3279 := by
    have hnat : (524428599 : ℕ)^4303*100000000000000^3279 ≤ 42869372817453^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524428599 1000000000 42869372817453 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129047697/10000000000 : ℝ)^4303 ≤ (6566806022539/50000000000000 : ℝ)^3279 := by
    have hnat : (2129047697 : ℕ)^4303*50000000000000^3279 ≤ 6566806022539^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129047697 10000000000 6566806022539 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534907937/1000000000 : ℝ), (524428599/1000000000 : ℝ), (-2129047697/10000000000 : ℝ)] ![(43997015120651/100000000000000 : ℝ), (42869372817453/100000000000000 : ℝ), (6566806022539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534907937/1000000000 : ℝ)|^4303 ≤ (43997015120651/100000000000000 : ℝ)^3279
        have hw : |(534907937/1000000000 : ℝ)|=(534907937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524428599/1000000000 : ℝ)|^4303 ≤ (42869372817453/100000000000000 : ℝ)^3279
        have hw : |(524428599/1000000000 : ℝ)|=(524428599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129047697/10000000000 : ℝ)|^4303 ≤ (6566806022539/50000000000000 : ℝ)^3279
        have hw : |(-2129047697/10000000000 : ℝ)|=(2129047697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326331177/10000000000 : ℝ)*x 0 + (415290653/1000000000 : ℝ)*x 1 + (563313141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326331177/10000000000 : ℝ)^4303 ≤ (3330300944423/10000000000000 : ℝ)^3279 := by
    have hnat : (4326331177 : ℕ)^4303*10000000000000^3279 ≤ 3330300944423^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326331177 10000000000 3330300944423 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415290653/1000000000 : ℝ)^4303 ≤ (31562196881441/100000000000000 : ℝ)^3279 := by
    have hnat : (415290653 : ℕ)^4303*100000000000000^3279 ≤ 31562196881441^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415290653 1000000000 31562196881441 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563313141/1250000000 : ℝ)^4303 ≤ (17567396831793/50000000000000 : ℝ)^3279 := by
    have hnat : (563313141 : ℕ)^4303*50000000000000^3279 ≤ 17567396831793^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563313141 1250000000 17567396831793 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326331177/10000000000 : ℝ), (415290653/1000000000 : ℝ), (563313141/1250000000 : ℝ)] ![(3330300944423/10000000000000 : ℝ), (31562196881441/100000000000000 : ℝ), (17567396831793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326331177/10000000000 : ℝ)|^4303 ≤ (3330300944423/10000000000000 : ℝ)^3279
        have hw : |(4326331177/10000000000 : ℝ)|=(4326331177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415290653/1000000000 : ℝ)|^4303 ≤ (31562196881441/100000000000000 : ℝ)^3279
        have hw : |(415290653/1000000000 : ℝ)|=(415290653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563313141/1250000000 : ℝ)|^4303 ≤ (17567396831793/50000000000000 : ℝ)^3279
        have hw : |(563313141/1250000000 : ℝ)|=(563313141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021536469/5000000000 : ℝ)*x 0 + (5244892827/10000000000 : ℝ)*x 1 + (5412429107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021536469/5000000000 : ℝ)^4303 ≤ (12442057159223/100000000000000 : ℝ)^3279 := by
    have hnat : (1021536469 : ℕ)^4303*100000000000000^3279 ≤ 12442057159223^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021536469 5000000000 12442057159223 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244892827/10000000000 : ℝ)^4303 ≤ (53594853327/125000000000 : ℝ)^3279 := by
    have hnat : (5244892827 : ℕ)^4303*125000000000^3279 ≤ 53594853327^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244892827 10000000000 53594853327 125000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412429107/10000000000 : ℝ)^4303 ≤ (8936412032317/20000000000000 : ℝ)^3279 := by
    have hnat : (5412429107 : ℕ)^4303*20000000000000^3279 ≤ 8936412032317^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412429107 10000000000 8936412032317 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021536469/5000000000 : ℝ), (5244892827/10000000000 : ℝ), (5412429107/10000000000 : ℝ)] ![(12442057159223/100000000000000 : ℝ), (53594853327/125000000000 : ℝ), (8936412032317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021536469/5000000000 : ℝ)|^4303 ≤ (12442057159223/100000000000000 : ℝ)^3279
        have hw : |(-1021536469/5000000000 : ℝ)|=(1021536469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244892827/10000000000 : ℝ)|^4303 ≤ (53594853327/125000000000 : ℝ)^3279
        have hw : |(5244892827/10000000000 : ℝ)|=(5244892827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412429107/10000000000 : ℝ)|^4303 ≤ (8936412032317/20000000000000 : ℝ)^3279
        have hw : |(5412429107/10000000000 : ℝ)|=(5412429107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607359/10000000000 : ℝ)*x 0 + (-1960904559/10000000000 : ℝ)*x 1 + (5412429117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607359/10000000000 : ℝ)^4303 ≤ (43528383775329/100000000000000 : ℝ)^3279 := by
    have hnat : (5305607359 : ℕ)^4303*100000000000000^3279 ≤ 43528383775329^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607359 10000000000 43528383775329 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960904559/10000000000 : ℝ)^4303 ≤ (5894777973851/50000000000000 : ℝ)^3279 := by
    have hnat : (1960904559 : ℕ)^4303*50000000000000^3279 ≤ 5894777973851^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960904559 10000000000 5894777973851 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412429117/10000000000 : ℝ)^4303 ≤ (279262876687/625000000000 : ℝ)^3279 := by
    have hnat : (5412429117 : ℕ)^4303*625000000000^3279 ≤ 279262876687^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412429117 10000000000 279262876687 625000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607359/10000000000 : ℝ), (-1960904559/10000000000 : ℝ), (5412429117/10000000000 : ℝ)] ![(43528383775329/100000000000000 : ℝ), (5894777973851/50000000000000 : ℝ), (279262876687/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607359/10000000000 : ℝ)|^4303 ≤ (43528383775329/100000000000000 : ℝ)^3279
        have hw : |(5305607359/10000000000 : ℝ)|=(5305607359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960904559/10000000000 : ℝ)|^4303 ≤ (5894777973851/50000000000000 : ℝ)^3279
        have hw : |(-1960904559/10000000000 : ℝ)|=(1960904559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412429117/10000000000 : ℝ)|^4303 ≤ (279262876687/625000000000 : ℝ)^3279
        have hw : |(5412429117/10000000000 : ℝ)|=(5412429117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607341/10000000000 : ℝ)*x 0 + (5412429131/10000000000 : ℝ)*x 1 + (-490226141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607341/10000000000 : ℝ)^4303 ≤ (1360261986923/3125000000000 : ℝ)^3279 := by
    have hnat : (5305607341 : ℕ)^4303*3125000000000^3279 ≤ 1360261986923^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607341 10000000000 1360261986923 3125000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412429131/10000000000 : ℝ)^4303 ≤ (4468206042159/10000000000000 : ℝ)^3279 := by
    have hnat : (5412429131 : ℕ)^4303*10000000000000^3279 ≤ 4468206042159^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412429131 10000000000 4468206042159 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490226141/2500000000 : ℝ)^4303 ≤ (736847249197/6250000000000 : ℝ)^3279 := by
    have hnat : (490226141 : ℕ)^4303*6250000000000^3279 ≤ 736847249197^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490226141 2500000000 736847249197 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607341/10000000000 : ℝ), (5412429131/10000000000 : ℝ), (-490226141/2500000000 : ℝ)] ![(1360261986923/3125000000000 : ℝ), (4468206042159/10000000000000 : ℝ), (736847249197/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607341/10000000000 : ℝ)|^4303 ≤ (1360261986923/3125000000000 : ℝ)^3279
        have hw : |(5305607341/10000000000 : ℝ)|=(5305607341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412429131/10000000000 : ℝ)|^4303 ≤ (4468206042159/10000000000000 : ℝ)^3279
        have hw : |(5412429131/10000000000 : ℝ)|=(5412429131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490226141/2500000000 : ℝ)|^4303 ≤ (736847249197/6250000000000 : ℝ)^3279
        have hw : |(-490226141/2500000000 : ℝ)|=(490226141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s5_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865271393/2000000000 : ℝ)*x 0 + (36041869/80000000 : ℝ)*x 1 + (4154184659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865271393/2000000000 : ℝ)^4303 ≤ (33303269946621/100000000000000 : ℝ)^3279 := by
    have hnat : (865271393 : ℕ)^4303*100000000000000^3279 ≤ 33303269946621^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865271393 2000000000 33303269946621 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36041869/80000000 : ℝ)^4303 ≤ (548777893883/1562500000000 : ℝ)^3279 := by
    have hnat : (36041869 : ℕ)^4303*1562500000000^3279 ≤ 548777893883^3279*80000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36041869 80000000 548777893883 1562500000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154184659/10000000000 : ℝ)^4303 ≤ (31574944837417/100000000000000 : ℝ)^3279 := by
    have hnat : (4154184659 : ℕ)^4303*100000000000000^3279 ≤ 31574944837417^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154184659 10000000000 31574944837417 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865271393/2000000000 : ℝ), (36041869/80000000 : ℝ), (4154184659/10000000000 : ℝ)] ![(33303269946621/100000000000000 : ℝ), (548777893883/1562500000000 : ℝ), (31574944837417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865271393/2000000000 : ℝ)|^4303 ≤ (33303269946621/100000000000000 : ℝ)^3279
        have hw : |(865271393/2000000000 : ℝ)|=(865271393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36041869/80000000 : ℝ)|^4303 ≤ (548777893883/1562500000000 : ℝ)^3279
        have hw : |(36041869/80000000 : ℝ)|=(36041869/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154184659/10000000000 : ℝ)|^4303 ≤ (31574944837417/100000000000000 : ℝ)^3279
        have hw : |(4154184659/10000000000 : ℝ)|=(4154184659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1393/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11101/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (4879464011330393/50000000000000000000 : ℝ) := by
    have hpowers : (11101/100000 : ℝ)^2151 ≤ (4879464011330393/50000000000000000000 : ℝ)^512 := by
      have hnat : (11101 : ℕ)^2151*50000000000000000000^512 ≤ 4879464011330393^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11101 100000 4879464011330393 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11101/100000 : ℝ)) (X := (4879464011330393/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (16154093374614203/50000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^2151 ≤ (16154093374614203/50000000000000000000 : ℝ)^512 := by
      have hnat : (14761 : ℕ)^2151*50000000000000000000^512 ≤ 16154093374614203^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 16154093374614203 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (16154093374614203/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004879464011330393/25000000000000000000 : ℝ) ≤ (125005806833617/125000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25004879464011330393/25000000000000000000 : ℝ)^512 ≤ (125005806833617/125000000000000 : ℝ)^2151 := by
      have hnat : (25004879464011330393 : ℕ)^512*125000000000000^2151 ≤ 125005806833617^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004879464011330393 25000000000000000000 125005806833617 125000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125005806833617/125000000000000 : ℝ)) (X := (25004879464011330393/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505258389346486149/12500000000000000000 : ℝ) ≤ (10001001158143659/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (12505258389346486149/12500000000000000000 : ℝ)^512 ≤ (10001001158143659/10000000000000000 : ℝ)^2151 := by
      have hnat : (12505258389346486149 : ℕ)^512*10000000000000000^2151 ≤ 10001001158143659^2151*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505258389346486149 12500000000000000000 10001001158143659 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001001158143659/10000000000000000 : ℝ)) (X := (12505258389346486149/12500000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016154093374614203/25000000000000000000 : ℝ) ≤ (5000768884798979/5000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25016154093374614203/25000000000000000000 : ℝ)^512 ≤ (5000768884798979/5000000000000000 : ℝ)^2151 := by
      have hnat : (25016154093374614203 : ℕ)^512*5000000000000000^2151 ≤ 5000768884798979^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016154093374614203 25000000000000000000 5000768884798979 5000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000768884798979/5000000000000000 : ℝ)) (X := (25016154093374614203/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4879464011330393/50000000000000000000 : ℝ) ≤ ((18294893196687355601/18300000000000000000 : ℝ)+2*(536611454299/366000000000000 : ℝ)*(11101/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (18294893196687355601/18300000000000000000 : ℝ)+2*(536611454299/366000000000000 : ℝ)*(11101/100000 : ℝ)=(125005806833617/125000000000000 : ℝ) by norm_num, show 1+2*(4879464011330393/50000000000000000000 : ℝ)=(25004879464011330393/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16154093374614203/50000000000000000000 : ℝ)+(4879464011330393/50000000000000000000 : ℝ) ≤ ((18294893196687355601/18300000000000000000 : ℝ)+(536611454299/366000000000000 : ℝ)*((14761/100000 : ℝ)+(11101/100000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (18294893196687355601/18300000000000000000 : ℝ)+(536611454299/366000000000000 : ℝ)*((14761/100000 : ℝ)+(11101/100000 : ℝ))=(10001001158143659/10000000000000000 : ℝ) by norm_num, show 1+(16154093374614203/50000000000000000000 : ℝ)+(4879464011330393/50000000000000000000 : ℝ)=(12505258389346486149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16154093374614203/50000000000000000000 : ℝ) ≤ ((18294893196687355601/18300000000000000000 : ℝ)+2*(536611454299/366000000000000 : ℝ)*(14761/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (18294893196687355601/18300000000000000000 : ℝ)+2*(536611454299/366000000000000 : ℝ)*(14761/100000 : ℝ)=(5000768884798979/5000000000000000 : ℝ) by norm_num, show 1+2*(16154093374614203/50000000000000000000 : ℝ)=(25016154093374614203/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18294893196687355601/18300000000000000000 : ℝ)*(X 1 0+X 2 0)+(536611454299/366000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (18294893196687355601/18300000000000000000 : ℝ)) (alpha := (536611454299/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18294893196687355601/18300000000000000000 : ℝ)*(X 0 1+X 2 1)+(536611454299/366000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (18294893196687355601/18300000000000000000 : ℝ)) (alpha := (536611454299/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18294893196687355601/18300000000000000000 : ℝ)*(X 0 2+X 1 2)+(536611454299/366000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (18294893196687355601/18300000000000000000 : ℝ)) (alpha := (536611454299/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-408612119/2000000000 : ℝ)*X 0 0+(5413039103/10000000000 : ℝ)*X 0 1+(1048857197/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349079367/10000000000 : ℝ)*X 1 0+(-2129047711/10000000000 : ℝ)*X 1 1+(5244285983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534907937/1000000000 : ℝ)*X 2 0+(524428599/1000000000 : ℝ)*X 2 1+(-2129047697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326331177/10000000000 : ℝ)*X 0 0+(415290653/1000000000 : ℝ)*X 0 1+(563313141/1250000000 : ℝ)*X 0 2+(4326331177/10000000000 : ℝ)*X 1 0+(415290653/1000000000 : ℝ)*X 1 1+(563313141/1250000000 : ℝ)*X 1 2+(4326331177/10000000000 : ℝ)*X 2 0+(415290653/1000000000 : ℝ)*X 2 1+(563313141/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1021536469/5000000000 : ℝ)*X 0 0+(5244892827/10000000000 : ℝ)*X 0 1+(5412429107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305607359/10000000000 : ℝ)*X 1 0+(-1960904559/10000000000 : ℝ)*X 1 1+(5412429117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305607341/10000000000 : ℝ)*X 2 0+(5412429131/10000000000 : ℝ)*X 2 1+(-490226141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865271393/2000000000 : ℝ)*X 0 0+(36041869/80000000 : ℝ)*X 0 1+(4154184659/10000000000 : ℝ)*X 0 2+(865271393/2000000000 : ℝ)*X 1 0+(36041869/80000000 : ℝ)*X 1 1+(4154184659/10000000000 : ℝ)*X 1 2+(865271393/2000000000 : ℝ)*X 2 0+(36041869/80000000 : ℝ)*X 2 1+(4154184659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356030222568032843909181903/152500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230442493/50000000000000 : ℝ)*(base19) + (219588413/50000000000000 : ℝ)*(base23) + (836851/6250000000000 : ℝ)*(lower2) + (57809967/100000000000000 : ℝ)*(upper3) + (1769353/3125000000000 : ℝ)*(upper5) + (4376954742889793/100000000000000 : ℝ)*(major0) + (4376954742889793/100000000000000 : ℝ)*(major1) + (2188477371444897/50000000000000 : ℝ)*(major2) + (2962912798607537/50000000000000 : ℝ)*(sp0) + (5925834663248647/100000000000000 : ℝ)*(sp1) + (5925834684956807/100000000000000 : ℝ)*(sp2) + (707017453216269/25000000000000 : ℝ)*(sp3) + (4763459279/50000000000000 : ℝ)*(sp4) + (558870007/12500000000000 : ℝ)*(sp7) + (707018570956283/25000000000000 : ℝ)*(f.failure) + (5925835124133633/100000000000000 : ℝ)*(f.sum) + (56451039728287/36600000000000000000000000000 : ℝ)*base66 + (17943983464924580593/1830000000000000000000000000000000 : ℝ)*base67 + (23130887497548493097/915000000000000000000000000000000 : ℝ)*base69 + (20234631846334580593/1830000000000000000000000000000000 : ℝ)*base71 + (57796463231287/36600000000000000000000000000 : ℝ)*base74 + (1391210891973493097/915000000000000000000000000000000 : ℝ)*base75 + (6887920134410369407/1830000000000000000000000000000000 : ℝ)*base78 + (9486752778650369407/1830000000000000000000000000000000 : ℝ)*base80 + (48022224170207/18300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (13603679/1250000000000000000000 : ℝ)*base89 + (13603679/1250000000000000000000 : ℝ)*base91 + (1103679/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2160029660391850706074865501/305000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1302445123/100000000000000 : ℝ)*(base19) + (1337587091/100000000000000 : ℝ)*(base23) + (160515321/100000000000000 : ℝ)*(upper3) + (24328461/100000000000000 : ℝ)*(lower4) + (28944527/20000000000000 : ℝ)*(upper5) + (4408730438930099/100000000000000 : ℝ)*(major0) + (4408730438930099/100000000000000 : ℝ)*(major1) + (4408730438930099/100000000000000 : ℝ)*(major2) + (26344190059/100000000000000 : ℝ)*(sp1) + (5501648319/20000000000000 : ℝ)*(sp2) + (59688551818173/1000000000000 : ℝ)*(sp4) + (5968827535182119/100000000000000 : ℝ)*(sp5) + (1193765267197723/20000000000000 : ℝ)*(sp6) + (2848605459974077/100000000000000 : ℝ)*(sp7) + (2848605459974077/100000000000000 : ℝ)*(f.failure) + (59688551818173/1000000000000 : ℝ)*(f.sum) + (118654496915899/18300000000000000000000000000 : ℝ)*base66 + (3887586306525184499/1830000000000000000000000000000000 : ℝ)*base67 + (11346595694414815501/1830000000000000000000000000000000 : ℝ)*base70 + (10840759604294815501/1830000000000000000000000000000000 : ℝ)*base72 + (90600792159101/18300000000000000000000000000 : ℝ)*base73 + (5125507304985184499/1830000000000000000000000000000000 : ℝ)*base75 + (3558061967175184499/1830000000000000000000000000000000 : ℝ)*base77 + (27035664075184499/1830000000000000000000000000000000 : ℝ)*base79 + (96566767728799/18300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4231001/5000000000000000000000 : ℝ)*base89 + (4231001/5000000000000000000000 : ℝ)*base91 + (4231001/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1343_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (161/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1343_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1343_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1343_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (161/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

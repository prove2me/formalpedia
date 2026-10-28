-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:07.177188+00:00
-- url     : https://prove2.me/submissions/97620df4-4092-40e0-814a-6b57578393ed

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
theorem support_rectangle_w1170_s3_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075031859/5000000000 : ℝ)*x 0 + (2713174883/5000000000 : ℝ)*x 1 + (5234651377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075031859/5000000000 : ℝ)^8363 ≤ (13060520565733/100000000000000 : ℝ)^6315 := by
    have hnat : (1075031859 : ℕ)^8363*100000000000000^6315 ≤ 13060520565733^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075031859 5000000000 13060520565733 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713174883/5000000000 : ℝ)^8363 ≤ (4450478885763/10000000000000 : ℝ)^6315 := by
    have hnat : (2713174883 : ℕ)^8363*10000000000000^6315 ≤ 4450478885763^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713174883 5000000000 4450478885763 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234651377/10000000000 : ℝ)^8363 ≤ (21217345280143/50000000000000 : ℝ)^6315 := by
    have hnat : (5234651377 : ℕ)^8363*50000000000000^6315 ≤ 21217345280143^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234651377 10000000000 21217345280143 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075031859/5000000000 : ℝ), (2713174883/5000000000 : ℝ), (5234651377/10000000000 : ℝ)] ![(13060520565733/100000000000000 : ℝ), (4450478885763/10000000000000 : ℝ), (21217345280143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075031859/5000000000 : ℝ)|^8363 ≤ (13060520565733/100000000000000 : ℝ)^6315
        have hw : |(-1075031859/5000000000 : ℝ)|=(1075031859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713174883/5000000000 : ℝ)|^8363 ≤ (4450478885763/10000000000000 : ℝ)^6315
        have hw : |(2713174883/5000000000 : ℝ)|=(2713174883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234651377/10000000000 : ℝ)|^8363 ≤ (21217345280143/50000000000000 : ℝ)^6315
        have hw : |(5234651377/10000000000 : ℝ)|=(5234651377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338281727/2500000000 : ℝ)*x 0 + (-1123997299/5000000000 : ℝ)*x 1 + (261732559/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338281727/2500000000 : ℝ)^8363 ≤ (21855614079519/50000000000000 : ℝ)^6315 := by
    have hnat : (1338281727 : ℕ)^8363*50000000000000^6315 ≤ 21855614079519^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338281727 2500000000 21855614079519 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123997299/5000000000 : ℝ)^8363 ≤ (1731760421351/12500000000000 : ℝ)^6315 := by
    have hnat : (1123997299 : ℕ)^8363*12500000000000^6315 ≤ 1731760421351^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123997299 5000000000 1731760421351 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261732559/500000000 : ℝ)^8363 ≤ (21217344222697/50000000000000 : ℝ)^6315 := by
    have hnat : (261732559 : ℕ)^8363*50000000000000^6315 ≤ 21217344222697^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261732559 500000000 21217344222697 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338281727/2500000000 : ℝ), (-1123997299/5000000000 : ℝ), (261732559/500000000 : ℝ)] ![(21855614079519/50000000000000 : ℝ), (1731760421351/12500000000000 : ℝ), (21217344222697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338281727/2500000000 : ℝ)|^8363 ≤ (21855614079519/50000000000000 : ℝ)^6315
        have hw : |(1338281727/2500000000 : ℝ)|=(1338281727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123997299/5000000000 : ℝ)|^8363 ≤ (1731760421351/12500000000000 : ℝ)^6315
        have hw : |(-1123997299/5000000000 : ℝ)|=(1123997299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261732559/500000000 : ℝ)|^8363 ≤ (21217344222697/50000000000000 : ℝ)^6315
        have hw : |(261732559/500000000 : ℝ)|=(261732559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353126993/10000000000 : ℝ)*x 0 + (261732559/500000000 : ℝ)*x 1 + (-2247994487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353126993/10000000000 : ℝ)^8363 ≤ (43711229078203/100000000000000 : ℝ)^6315 := by
    have hnat : (5353126993 : ℕ)^8363*100000000000000^6315 ≤ 43711229078203^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353126993 10000000000 43711229078203 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261732559/500000000 : ℝ)^8363 ≤ (21217344222697/50000000000000 : ℝ)^6315 := by
    have hnat : (261732559 : ℕ)^8363*50000000000000^6315 ≤ 21217344222697^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261732559 500000000 21217344222697 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247994487/10000000000 : ℝ)^8363 ≤ (6927041232439/50000000000000 : ℝ)^6315 := by
    have hnat : (2247994487 : ℕ)^8363*50000000000000^6315 ≤ 6927041232439^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247994487 10000000000 6927041232439 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353126993/10000000000 : ℝ), (261732559/500000000 : ℝ), (-2247994487/10000000000 : ℝ)] ![(43711229078203/100000000000000 : ℝ), (21217344222697/50000000000000 : ℝ), (6927041232439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353126993/10000000000 : ℝ)|^8363 ≤ (43711229078203/100000000000000 : ℝ)^6315
        have hw : |(5353126993/10000000000 : ℝ)|=(5353126993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261732559/500000000 : ℝ)|^8363 ≤ (21217344222697/50000000000000 : ℝ)^6315
        have hw : |(261732559/500000000 : ℝ)|=(261732559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247994487/10000000000 : ℝ)|^8363 ≤ (6927041232439/50000000000000 : ℝ)^6315
        have hw : |(-2247994487/10000000000 : ℝ)|=(2247994487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179329421/5000000000 : ℝ)*x 0 + (4171085303/10000000000 : ℝ)*x 1 + (910911999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179329421/5000000000 : ℝ)^8363 ≤ (3329602716897/10000000000000 : ℝ)^6315 := by
    have hnat : (2179329421 : ℕ)^8363*10000000000000^6315 ≤ 3329602716897^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179329421 5000000000 3329602716897 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171085303/10000000000 : ℝ)^8363 ≤ (31411820679359/100000000000000 : ℝ)^6315 := by
    have hnat : (4171085303 : ℕ)^8363*100000000000000^6315 ≤ 31411820679359^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171085303 10000000000 31411820679359 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910911999/2000000000 : ℝ)^8363 ≤ (7058430425971/20000000000000 : ℝ)^6315 := by
    have hnat : (910911999 : ℕ)^8363*20000000000000^6315 ≤ 7058430425971^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910911999 2000000000 7058430425971 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179329421/5000000000 : ℝ), (4171085303/10000000000 : ℝ), (910911999/2000000000 : ℝ)] ![(3329602716897/10000000000000 : ℝ), (31411820679359/100000000000000 : ℝ), (7058430425971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179329421/5000000000 : ℝ)|^8363 ≤ (3329602716897/10000000000000 : ℝ)^6315
        have hw : |(2179329421/5000000000 : ℝ)|=(2179329421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171085303/10000000000 : ℝ)|^8363 ≤ (31411820679359/100000000000000 : ℝ)^6315
        have hw : |(4171085303/10000000000 : ℝ)|=(4171085303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910911999/2000000000 : ℝ)|^8363 ≤ (7058430425971/20000000000000 : ℝ)^6315
        have hw : |(910911999/2000000000 : ℝ)|=(910911999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-107504021/500000000 : ℝ)*x 0 + (5235380807/10000000000 : ℝ)*x 1 + (678202049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107504021/500000000 : ℝ)^8363 ≤ (13060654924783/100000000000000 : ℝ)^6315 := by
    have hnat : (107504021 : ℕ)^8363*100000000000000^6315 ≤ 13060654924783^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107504021 500000000 13060654924783 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235380807/10000000000 : ℝ)^8363 ≤ (10610630382083/25000000000000 : ℝ)^6315 := by
    have hnat : (5235380807 : ℕ)^8363*25000000000000^6315 ≤ 10610630382083^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235380807 10000000000 10610630382083 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678202049/1250000000 : ℝ)^8363 ≤ (11124205882269/25000000000000 : ℝ)^6315 := by
    have hnat : (678202049 : ℕ)^8363*25000000000000^6315 ≤ 11124205882269^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678202049 1250000000 11124205882269 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107504021/500000000 : ℝ), (5235380807/10000000000 : ℝ), (678202049/1250000000 : ℝ)] ![(13060654924783/100000000000000 : ℝ), (10610630382083/25000000000000 : ℝ), (11124205882269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107504021/500000000 : ℝ)|^8363 ≤ (13060654924783/100000000000000 : ℝ)^6315
        have hw : |(-107504021/500000000 : ℝ)|=(107504021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235380807/10000000000 : ℝ)|^8363 ≤ (10610630382083/25000000000000 : ℝ)^6315
        have hw : |(5235380807/10000000000 : ℝ)|=(5235380807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678202049/1250000000 : ℝ)|^8363 ≤ (11124205882269/25000000000000 : ℝ)^6315
        have hw : |(678202049/1250000000 : ℝ)|=(678202049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652231181/5000000000 : ℝ)*x 0 + (-411406017/2000000000 : ℝ)*x 1 + (1356404049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652231181/5000000000 : ℝ)^8363 ≤ (10796440456127/25000000000000 : ℝ)^6315 := by
    have hnat : (2652231181 : ℕ)^8363*25000000000000^6315 ≤ 10796440456127^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652231181 5000000000 10796440456127 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411406017/2000000000 : ℝ)^8363 ≤ (6158708379999/50000000000000 : ℝ)^6315 := by
    have hnat : (411406017 : ℕ)^8363*50000000000000^6315 ≤ 6158708379999^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411406017 2000000000 6158708379999 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356404049/2500000000 : ℝ)^8363 ≤ (22248410700163/50000000000000 : ℝ)^6315 := by
    have hnat : (1356404049 : ℕ)^8363*50000000000000^6315 ≤ 22248410700163^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356404049 2500000000 22248410700163 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652231181/5000000000 : ℝ), (-411406017/2000000000 : ℝ), (1356404049/2500000000 : ℝ)] ![(10796440456127/25000000000000 : ℝ), (6158708379999/50000000000000 : ℝ), (22248410700163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652231181/5000000000 : ℝ)|^8363 ≤ (10796440456127/25000000000000 : ℝ)^6315
        have hw : |(2652231181/5000000000 : ℝ)|=(2652231181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411406017/2000000000 : ℝ)|^8363 ≤ (6158708379999/50000000000000 : ℝ)^6315
        have hw : |(-411406017/2000000000 : ℝ)|=(411406017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356404049/2500000000 : ℝ)|^8363 ≤ (22248410700163/50000000000000 : ℝ)^6315
        have hw : |(1356404049/2500000000 : ℝ)|=(1356404049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304463627/10000000000 : ℝ)*x 0 + (217024603/400000000 : ℝ)*x 1 + (-2057029901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304463627/10000000000 : ℝ)^8363 ≤ (43185775463381/100000000000000 : ℝ)^6315 := by
    have hnat : (5304463627 : ℕ)^8363*100000000000000^6315 ≤ 43185775463381^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304463627 10000000000 43185775463381 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217024603/400000000 : ℝ)^8363 ≤ (22248404612589/50000000000000 : ℝ)^6315 := by
    have hnat : (217024603 : ℕ)^8363*50000000000000^6315 ≤ 22248404612589^6315*400000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217024603 400000000 22248404612589 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057029901/10000000000 : ℝ)^8363 ≤ (12317415300897/100000000000000 : ℝ)^6315 := by
    have hnat : (2057029901 : ℕ)^8363*100000000000000^6315 ≤ 12317415300897^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057029901 10000000000 12317415300897 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304463627/10000000000 : ℝ), (217024603/400000000 : ℝ), (-2057029901/10000000000 : ℝ)] ![(43185775463381/100000000000000 : ℝ), (22248404612589/50000000000000 : ℝ), (12317415300897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304463627/10000000000 : ℝ)|^8363 ≤ (43185775463381/100000000000000 : ℝ)^6315
        have hw : |(5304463627/10000000000 : ℝ)|=(5304463627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217024603/400000000 : ℝ)|^8363 ≤ (22248404612589/50000000000000 : ℝ)^6315
        have hw : |(217024603/400000000 : ℝ)|=(217024603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057029901/10000000000 : ℝ)|^8363 ≤ (12317415300897/100000000000000 : ℝ)^6315
        have hw : |(-2057029901/10000000000 : ℝ)|=(2057029901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s3_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358691963/10000000000 : ℝ)*x 0 + (4553101119/10000000000 : ℝ)*x 1 + (521569079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358691963/10000000000 : ℝ)^8363 ≤ (33296362236433/100000000000000 : ℝ)^6315 := by
    have hnat : (4358691963 : ℕ)^8363*100000000000000^6315 ≤ 33296362236433^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358691963 10000000000 33296362236433 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553101119/10000000000 : ℝ)^8363 ≤ (7055436464043/20000000000000 : ℝ)^6315 := by
    have hnat : (4553101119 : ℕ)^8363*20000000000000^6315 ≤ 7055436464043^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553101119 10000000000 7055436464043 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521569079/1250000000 : ℝ)^8363 ≤ (31426455420721/100000000000000 : ℝ)^6315 := by
    have hnat : (521569079 : ℕ)^8363*100000000000000^6315 ≤ 31426455420721^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521569079 1250000000 31426455420721 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358691963/10000000000 : ℝ), (4553101119/10000000000 : ℝ), (521569079/1250000000 : ℝ)] ![(33296362236433/100000000000000 : ℝ), (7055436464043/20000000000000 : ℝ), (31426455420721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358691963/10000000000 : ℝ)|^8363 ≤ (33296362236433/100000000000000 : ℝ)^6315
        have hw : |(4358691963/10000000000 : ℝ)|=(4358691963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553101119/10000000000 : ℝ)|^8363 ≤ (7055436464043/20000000000000 : ℝ)^6315
        have hw : |(4553101119/10000000000 : ℝ)|=(4553101119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521569079/1250000000 : ℝ)|^8363 ≤ (31426455420721/100000000000000 : ℝ)^6315
        have hw : |(521569079/1250000000 : ℝ)|=(521569079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2679/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (821/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1839/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (821/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1839/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (821/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1839/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (821/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1839/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (821/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1839/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (821/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1839/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1839/20000 : ℝ) ^ (4181/1024 : ℝ) ≤ (18324142168709/312500000000000000 : ℝ) := by
    have hpowers : (1839/20000 : ℝ)^4181 ≤ (18324142168709/312500000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^4181*312500000000000000^1024 ≤ 18324142168709^1024*20000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 20000 18324142168709 312500000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/20000 : ℝ)) (X := (18324142168709/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (821/5000 : ℝ) ^ (4181/1024 : ℝ) ≤ (1251389332726069/2000000000000000000 : ℝ) := by
    have hpowers : (821/5000 : ℝ)^4181 ≤ (1251389332726069/2000000000000000000 : ℝ)^1024 := by
      have hnat : (821 : ℕ)^4181*2000000000000000000^1024 ≤ 1251389332726069^1024*5000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        821 5000 1251389332726069 2000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (821/5000 : ℝ)) (X := (1251389332726069/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (156268324142168709/156250000000000000 : ℝ) ≤ (400011488522499/400000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (156268324142168709/156250000000000000 : ℝ)^1024 ≤ (400011488522499/400000000000000 : ℝ)^4181 := by
      have hnat : (156268324142168709 : ℕ)^1024*400000000000000^4181 ≤ 400011488522499^4181*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156268324142168709 156250000000000000 400011488522499 400000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400011488522499/400000000000000 : ℝ)) (X := (156268324142168709/156250000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006843319213029033/10000000000000000000 : ℝ) ≤ (10001675615666339/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (10006843319213029033/10000000000000000000 : ℝ)^1024 ≤ (10001675615666339/10000000000000000 : ℝ)^4181 := by
      have hnat : (10006843319213029033 : ℕ)^1024*10000000000000000^4181 ≤ 10001675615666339^4181*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006843319213029033 10000000000000000000 10001675615666339 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001675615666339/10000000000000000 : ℝ)) (X := (10006843319213029033/10000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1001251389332726069/1000000000000000000 : ℝ) ≤ (10003064018270203/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (1001251389332726069/1000000000000000000 : ℝ)^1024 ≤ (10003064018270203/10000000000000000 : ℝ)^4181 := by
      have hnat : (1001251389332726069 : ℕ)^1024*10000000000000000^4181 ≤ 10003064018270203^4181*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001251389332726069 1000000000000000000 10003064018270203 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003064018270203/10000000000000000 : ℝ)) (X := (1001251389332726069/1000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18324142168709/312500000000000000 : ℝ) ≤ ((14445308478098264583/14450000000000000000 : ℝ)+2*(173550325483/90312500000000 : ℝ)*(1839/20000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (14445308478098264583/14450000000000000000 : ℝ)+2*(173550325483/90312500000000 : ℝ)*(1839/20000 : ℝ)=(400011488522499/400000000000000 : ℝ) by norm_num, show 1+2*(18324142168709/312500000000000000 : ℝ)=(156268324142168709/156250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1251389332726069/2000000000000000000 : ℝ)+(18324142168709/312500000000000000 : ℝ) ≤ ((14445308478098264583/14450000000000000000 : ℝ)+(173550325483/90312500000000 : ℝ)*((821/5000 : ℝ)+(1839/20000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (14445308478098264583/14450000000000000000 : ℝ)+(173550325483/90312500000000 : ℝ)*((821/5000 : ℝ)+(1839/20000 : ℝ))=(10001675615666339/10000000000000000 : ℝ) by norm_num, show 1+(1251389332726069/2000000000000000000 : ℝ)+(18324142168709/312500000000000000 : ℝ)=(10006843319213029033/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1251389332726069/2000000000000000000 : ℝ) ≤ ((14445308478098264583/14450000000000000000 : ℝ)+2*(173550325483/90312500000000 : ℝ)*(821/5000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (14445308478098264583/14450000000000000000 : ℝ)+2*(173550325483/90312500000000 : ℝ)*(821/5000 : ℝ)=(10003064018270203/10000000000000000 : ℝ) by norm_num, show 1+2*(1251389332726069/2000000000000000000 : ℝ)=(1001251389332726069/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14445308478098264583/14450000000000000000 : ℝ)*(X 1 0+X 2 0)+(173550325483/90312500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (821/5000 : ℝ)) (c := (14445308478098264583/14450000000000000000 : ℝ)) (alpha := (173550325483/90312500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14445308478098264583/14450000000000000000 : ℝ)*(X 0 1+X 2 1)+(173550325483/90312500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (821/5000 : ℝ)) (c := (14445308478098264583/14450000000000000000 : ℝ)) (alpha := (173550325483/90312500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14445308478098264583/14450000000000000000 : ℝ)*(X 0 2+X 1 2)+(173550325483/90312500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1839/20000 : ℝ)) (hi := (821/5000 : ℝ)) (c := (14445308478098264583/14450000000000000000 : ℝ)) (alpha := (173550325483/90312500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1075031859/5000000000 : ℝ)*X 0 0+(2713174883/5000000000 : ℝ)*X 0 1+(5234651377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338281727/2500000000 : ℝ)*X 1 0+(-1123997299/5000000000 : ℝ)*X 1 1+(261732559/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353126993/10000000000 : ℝ)*X 2 0+(261732559/500000000 : ℝ)*X 2 1+(-2247994487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179329421/5000000000 : ℝ)*X 0 0+(4171085303/10000000000 : ℝ)*X 0 1+(910911999/2000000000 : ℝ)*X 0 2+(2179329421/5000000000 : ℝ)*X 1 0+(4171085303/10000000000 : ℝ)*X 1 1+(910911999/2000000000 : ℝ)*X 1 2+(2179329421/5000000000 : ℝ)*X 2 0+(4171085303/10000000000 : ℝ)*X 2 1+(910911999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107504021/500000000 : ℝ)*X 0 0+(5235380807/10000000000 : ℝ)*X 0 1+(678202049/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652231181/5000000000 : ℝ)*X 1 0+(-411406017/2000000000 : ℝ)*X 1 1+(1356404049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304463627/10000000000 : ℝ)*X 2 0+(217024603/400000000 : ℝ)*X 2 1+(-2057029901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358691963/10000000000 : ℝ)*X 0 0+(4553101119/10000000000 : ℝ)*X 0 1+(521569079/1250000000 : ℝ)*X 0 2+(4358691963/10000000000 : ℝ)*X 1 0+(4553101119/10000000000 : ℝ)*X 1 1+(521569079/1250000000 : ℝ)*X 1 2+(4358691963/10000000000 : ℝ)*X 2 0+(4553101119/10000000000 : ℝ)*X 2 1+(521569079/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1850055836529983172454902813/180625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1168023517/50000000000000 : ℝ)*(base19) + (2236796471/100000000000000 : ℝ)*(base23) + (9747123/10000000000000 : ℝ)*(lower2) + (114113517/50000000000000 : ℝ)*(upper3) + (112473749/50000000000000 : ℝ)*(upper5) + (978047700660937/25000000000000 : ℝ)*(major0) + (978047700660937/25000000000000 : ℝ)*(major1) + (978047700660937/25000000000000 : ℝ)*(major2) + (5216566280536317/100000000000000 : ℝ)*(sp0) + (521660490558891/10000000000000 : ℝ)*(sp1) + (5216605004839473/100000000000000 : ℝ)*(sp2) + (651938358886917/25000000000000 : ℝ)*(sp3) + (40961099627/100000000000000 : ℝ)*(sp4) + (20586686421/100000000000000 : ℝ)*(sp7) + (325971752779261/12500000000000 : ℝ)*(f.failure) + (652075905204493/12500000000000 : ℝ)*(f.sum) + (299512172962353/36125000000000000000000000000 : ℝ)*base66 + (1629597709172445729/361250000000000000000000000000000 : ℝ)*base68 + (1307235928978804271/361250000000000000000000000000000 : ℝ)*base69 + (3500499120678695729/361250000000000000000000000000000 : ℝ)*base72 + (18085973926103/36125000000000000000000000000 : ℝ)*base74 + (732948555424945729/361250000000000000000000000000000 : ℝ)*base76 + (1975760286570054271/361250000000000000000000000000000 : ℝ)*base77 + (11792252844273695729/361250000000000000000000000000000 : ℝ)*base80 + (19796350271353/36125000000000000000000000000 : ℝ)*base82 + (2137443/250000000000000000000 : ℝ)*base89 + (2137443/250000000000000000000 : ℝ)*base91 + (2137443/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1351331871150237804981757671/361250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26051067/12500000000000 : ℝ)*(base19) + (375003139/25000000000000 : ℝ)*(base23) + (12546189/50000000000000 : ℝ)*(upper4) + (15467587/100000000000000 : ℝ)*(upper5) + (1971110694431193/50000000000000 : ℝ)*(major0) + (1971110694431193/50000000000000 : ℝ)*(major1) + (1971110694431193/50000000000000 : ℝ)*(major2) + (403021147/100000000000000 : ℝ)*(sp0) + (9299133379/100000000000000 : ℝ)*(sp2) + (75706293/12500000000000 : ℝ)*(sp3) + (5256650548027827/100000000000000 : ℝ)*(sp4) + (5256650742640439/100000000000000 : ℝ)*(sp5) + (5256640151903039/100000000000000 : ℝ)*(sp6) + (656947774083769/25000000000000 : ℝ)*(sp7) + (2627791701985419/100000000000000 : ℝ)*(f.failure) + (2628325475524487/50000000000000 : ℝ)*(f.sum) + (106705159917123/18062500000000000000000000000 : ℝ)*base66 + (8089233933710122481/722500000000000000000000000000000 : ℝ)*base68 + (9412171639390122481/722500000000000000000000000000000 : ℝ)*base70 + (11617006710567622481/722500000000000000000000000000000 : ℝ)*base72 + (185825017356621/36125000000000000000000000000 : ℝ)*base74 + (2256488608012622481/722500000000000000000000000000000 : ℝ)*base76 + (4871605737812622481/722500000000000000000000000000000 : ℝ)*base78 + (7946346664975122481/722500000000000000000000000000000 : ℝ)*base80 + (4667724246281/2257812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16757397/2000000000000000000000 : ℝ)*base89 + (16757397/2000000000000000000000 : ℝ)*base91 + (16757397/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1170_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s4_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-430569681/2000000000 : ℝ)*x 0 + (2700290839/5000000000 : ℝ)*x 1 + (5258596847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430569681/2000000000 : ℝ)^8363 ≤ (1308292662387/10000000000000 : ℝ)^6315 := by
    have hnat : (430569681 : ℕ)^8363*10000000000000^6315 ≤ 1308292662387^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430569681 2000000000 1308292662387 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700290839/5000000000 : ℝ)^8363 ≤ (11056281466993/25000000000000 : ℝ)^6315 := by
    have hnat : (2700290839 : ℕ)^8363*25000000000000^6315 ≤ 11056281466993^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700290839 5000000000 11056281466993 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258596847/10000000000 : ℝ)^8363 ≤ (21345973742829/50000000000000 : ℝ)^6315 := by
    have hnat : (5258596847 : ℕ)^8363*50000000000000^6315 ≤ 21345973742829^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258596847 10000000000 21345973742829 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430569681/2000000000 : ℝ), (2700290839/5000000000 : ℝ), (5258596847/10000000000 : ℝ)] ![(1308292662387/10000000000000 : ℝ), (11056281466993/25000000000000 : ℝ), (21345973742829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430569681/2000000000 : ℝ)|^8363 ≤ (1308292662387/10000000000000 : ℝ)^6315
        have hw : |(-430569681/2000000000 : ℝ)|=(430569681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700290839/5000000000 : ℝ)|^8363 ≤ (11056281466993/25000000000000 : ℝ)^6315
        have hw : |(2700290839/5000000000 : ℝ)|=(2700290839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258596847/10000000000 : ℝ)|^8363 ≤ (21345973742829/50000000000000 : ℝ)^6315
        have hw : |(5258596847/10000000000 : ℝ)|=(5258596847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346674323/10000000000 : ℝ)*x 0 + (-2224983581/10000000000 : ℝ)*x 1 + (5258596489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346674323/10000000000 : ℝ)^8363 ≤ (21820732749791/50000000000000 : ℝ)^6315 := by
    have hnat : (5346674323 : ℕ)^8363*50000000000000^6315 ≤ 21820732749791^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346674323 10000000000 21820732749791 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224983581/10000000000 : ℝ)^8363 ≤ (2733318169237/20000000000000 : ℝ)^6315 := by
    have hnat : (2224983581 : ℕ)^8363*20000000000000^6315 ≤ 2733318169237^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224983581 10000000000 2733318169237 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258596489/10000000000 : ℝ)^8363 ≤ (21345971818329/50000000000000 : ℝ)^6315 := by
    have hnat : (5258596489 : ℕ)^8363*50000000000000^6315 ≤ 21345971818329^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258596489 10000000000 21345971818329 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346674323/10000000000 : ℝ), (-2224983581/10000000000 : ℝ), (5258596489/10000000000 : ℝ)] ![(21820732749791/50000000000000 : ℝ), (2733318169237/20000000000000 : ℝ), (21345971818329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346674323/10000000000 : ℝ)|^8363 ≤ (21820732749791/50000000000000 : ℝ)^6315
        have hw : |(5346674323/10000000000 : ℝ)|=(5346674323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224983581/10000000000 : ℝ)|^8363 ≤ (2733318169237/20000000000000 : ℝ)^6315
        have hw : |(-2224983581/10000000000 : ℝ)|=(2224983581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258596489/10000000000 : ℝ)|^8363 ≤ (21345971818329/50000000000000 : ℝ)^6315
        have hw : |(5258596489/10000000000 : ℝ)|=(5258596489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668334297/1250000000 : ℝ)*x 0 + (5258596193/10000000000 : ℝ)*x 1 + (-1112491951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668334297/1250000000 : ℝ)^8363 ≤ (10910366518121/25000000000000 : ℝ)^6315 := by
    have hnat : (668334297 : ℕ)^8363*25000000000000^6315 ≤ 10910366518121^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668334297 1250000000 10910366518121 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258596193/10000000000 : ℝ)^8363 ≤ (8538388090849/20000000000000 : ℝ)^6315 := by
    have hnat : (5258596193 : ℕ)^8363*20000000000000^6315 ≤ 8538388090849^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258596193 10000000000 8538388090849 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112491951/5000000000 : ℝ)^8363 ≤ (13666593457307/100000000000000 : ℝ)^6315 := by
    have hnat : (1112491951 : ℕ)^8363*100000000000000^6315 ≤ 13666593457307^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112491951 5000000000 13666593457307 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668334297/1250000000 : ℝ), (5258596193/10000000000 : ℝ), (-1112491951/5000000000 : ℝ)] ![(10910366518121/25000000000000 : ℝ), (8538388090849/20000000000000 : ℝ), (13666593457307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668334297/1250000000 : ℝ)|^8363 ≤ (10910366518121/25000000000000 : ℝ)^6315
        have hw : |(668334297/1250000000 : ℝ)|=(668334297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258596193/10000000000 : ℝ)|^8363 ≤ (8538388090849/20000000000000 : ℝ)^6315
        have hw : |(5258596193/10000000000 : ℝ)|=(5258596193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112491951/5000000000 : ℝ)|^8363 ≤ (13666593457307/100000000000000 : ℝ)^6315
        have hw : |(-1112491951/5000000000 : ℝ)|=(1112491951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180161077/5000000000 : ℝ)*x 0 + (2110297047/5000000000 : ℝ)*x 1 + (4504622193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180161077/5000000000 : ℝ)^8363 ≤ (33312855028309/100000000000000 : ℝ)^6315 := by
    have hnat : (2180161077 : ℕ)^8363*100000000000000^6315 ≤ 33312855028309^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180161077 5000000000 33312855028309 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110297047/5000000000 : ℝ)^8363 ≤ (31906527568763/100000000000000 : ℝ)^6315 := by
    have hnat : (2110297047 : ℕ)^8363*100000000000000^6315 ≤ 31906527568763^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110297047 5000000000 31906527568763 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504622193/10000000000 : ℝ)^8363 ≤ (8695154346123/25000000000000 : ℝ)^6315 := by
    have hnat : (4504622193 : ℕ)^8363*25000000000000^6315 ≤ 8695154346123^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504622193 10000000000 8695154346123 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180161077/5000000000 : ℝ), (2110297047/5000000000 : ℝ), (4504622193/10000000000 : ℝ)] ![(33312855028309/100000000000000 : ℝ), (31906527568763/100000000000000 : ℝ), (8695154346123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180161077/5000000000 : ℝ)|^8363 ≤ (33312855028309/100000000000000 : ℝ)^6315
        have hw : |(2180161077/5000000000 : ℝ)|=(2180161077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110297047/5000000000 : ℝ)|^8363 ≤ (31906527568763/100000000000000 : ℝ)^6315
        have hw : |(2110297047/5000000000 : ℝ)|=(2110297047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504622193/10000000000 : ℝ)|^8363 ≤ (8695154346123/25000000000000 : ℝ)^6315
        have hw : |(4504622193/10000000000 : ℝ)|=(4504622193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269106919/1250000000 : ℝ)*x 0 + (5258997647/10000000000 : ℝ)*x 1 + (2700089581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269106919/1250000000 : ℝ)^8363 ≤ (2616596506471/20000000000000 : ℝ)^6315 := by
    have hnat : (269106919 : ℕ)^8363*20000000000000^6315 ≤ 2616596506471^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269106919 1250000000 2616596506471 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258997647/10000000000 : ℝ)^8363 ≤ (42696256698167/100000000000000 : ℝ)^6315 := by
    have hnat : (5258997647 : ℕ)^8363*100000000000000^6315 ≤ 42696256698167^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258997647 10000000000 42696256698167 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700089581/5000000000 : ℝ)^8363 ≤ (22110380379047/50000000000000 : ℝ)^6315 := by
    have hnat : (2700089581 : ℕ)^8363*50000000000000^6315 ≤ 22110380379047^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700089581 5000000000 22110380379047 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269106919/1250000000 : ℝ), (5258997647/10000000000 : ℝ), (2700089581/5000000000 : ℝ)] ![(2616596506471/20000000000000 : ℝ), (42696256698167/100000000000000 : ℝ), (22110380379047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269106919/1250000000 : ℝ)|^8363 ≤ (2616596506471/20000000000000 : ℝ)^6315
        have hw : |(-269106919/1250000000 : ℝ)|=(269106919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258997647/10000000000 : ℝ)|^8363 ≤ (42696256698167/100000000000000 : ℝ)^6315
        have hw : |(5258997647/10000000000 : ℝ)|=(5258997647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700089581/5000000000 : ℝ)|^8363 ≤ (22110380379047/50000000000000 : ℝ)^6315
        have hw : |(2700089581/5000000000 : ℝ)|=(2700089581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310629679/10000000000 : ℝ)*x 0 + (-260425149/1250000000 : ℝ)*x 1 + (1350044793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310629679/10000000000 : ℝ)^8363 ≤ (43252268628053/100000000000000 : ℝ)^6315 := by
    have hnat : (5310629679 : ℕ)^8363*100000000000000^6315 ≤ 43252268628053^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310629679 10000000000 43252268628053 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260425149/1250000000 : ℝ)^8363 ≤ (2505394097017/20000000000000 : ℝ)^6315 := by
    have hnat : (260425149 : ℕ)^8363*20000000000000^6315 ≤ 2505394097017^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260425149 1250000000 2505394097017 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350044793/2500000000 : ℝ)^8363 ≤ (22110380433269/50000000000000 : ℝ)^6315 := by
    have hnat : (1350044793 : ℕ)^8363*50000000000000^6315 ≤ 22110380433269^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350044793 2500000000 22110380433269 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310629679/10000000000 : ℝ), (-260425149/1250000000 : ℝ), (1350044793/2500000000 : ℝ)] ![(43252268628053/100000000000000 : ℝ), (2505394097017/20000000000000 : ℝ), (22110380433269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310629679/10000000000 : ℝ)|^8363 ≤ (43252268628053/100000000000000 : ℝ)^6315
        have hw : |(5310629679/10000000000 : ℝ)|=(5310629679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260425149/1250000000 : ℝ)|^8363 ≤ (2505394097017/20000000000000 : ℝ)^6315
        have hw : |(-260425149/1250000000 : ℝ)|=(260425149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350044793/2500000000 : ℝ)|^8363 ≤ (22110380433269/50000000000000 : ℝ)^6315
        have hw : |(1350044793/2500000000 : ℝ)|=(1350044793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531062969/1000000000 : ℝ)*x 0 + (5400179169/10000000000 : ℝ)*x 1 + (-2083401183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531062969/1000000000 : ℝ)^8363 ≤ (43252268746697/100000000000000 : ℝ)^6315 := by
    have hnat : (531062969 : ℕ)^8363*100000000000000^6315 ≤ 43252268746697^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531062969 1000000000 43252268746697 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400179169/10000000000 : ℝ)^8363 ≤ (8844152166801/20000000000000 : ℝ)^6315 := by
    have hnat : (5400179169 : ℕ)^8363*20000000000000^6315 ≤ 8844152166801^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400179169 10000000000 8844152166801 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083401183/10000000000 : ℝ)^8363 ≤ (626348520671/5000000000000 : ℝ)^6315 := by
    have hnat : (2083401183 : ℕ)^8363*5000000000000^6315 ≤ 626348520671^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083401183 10000000000 626348520671 5000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531062969/1000000000 : ℝ), (5400179169/10000000000 : ℝ), (-2083401183/10000000000 : ℝ)] ![(43252268746697/100000000000000 : ℝ), (8844152166801/20000000000000 : ℝ), (626348520671/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531062969/1000000000 : ℝ)|^8363 ≤ (43252268746697/100000000000000 : ℝ)^6315
        have hw : |(531062969/1000000000 : ℝ)|=(531062969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400179169/10000000000 : ℝ)|^8363 ≤ (8844152166801/20000000000000 : ℝ)^6315
        have hw : |(5400179169/10000000000 : ℝ)|=(5400179169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083401183/10000000000 : ℝ)|^8363 ≤ (626348520671/5000000000000 : ℝ)^6315
        have hw : |(-2083401183/10000000000 : ℝ)|=(2083401183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s4_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360336069/10000000000 : ℝ)*x 0 + (4503819883/10000000000 : ℝ)*x 1 + (211069971/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360336069/10000000000 : ℝ)^8363 ≤ (33312995816249/100000000000000 : ℝ)^6315 := by
    have hnat : (4360336069 : ℕ)^8363*100000000000000^6315 ≤ 33312995816249^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360336069 10000000000 33312995816249 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503819883/10000000000 : ℝ)^8363 ≤ (34772413919703/100000000000000 : ℝ)^6315 := by
    have hnat : (4503819883 : ℕ)^8363*100000000000000^6315 ≤ 34772413919703^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503819883 10000000000 34772413919703 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211069971/500000000 : ℝ)^8363 ≤ (15957295128377/50000000000000 : ℝ)^6315 := by
    have hnat : (211069971 : ℕ)^8363*50000000000000^6315 ≤ 15957295128377^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211069971 500000000 15957295128377 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360336069/10000000000 : ℝ), (4503819883/10000000000 : ℝ), (211069971/500000000 : ℝ)] ![(33312995816249/100000000000000 : ℝ), (34772413919703/100000000000000 : ℝ), (15957295128377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360336069/10000000000 : ℝ)|^8363 ≤ (33312995816249/100000000000000 : ℝ)^6315
        have hw : |(4360336069/10000000000 : ℝ)|=(4360336069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503819883/10000000000 : ℝ)|^8363 ≤ (34772413919703/100000000000000 : ℝ)^6315
        have hw : |(4503819883/10000000000 : ℝ)|=(4503819883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211069971/500000000 : ℝ)|^8363 ≤ (15957295128377/50000000000000 : ℝ)^6315
        have hw : |(211069971/500000000 : ℝ)|=(211069971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11227/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2679/25000 : ℝ) ^ (4181/1024 : ℝ) ≤ (171173283846729/1562500000000000000 : ℝ) := by
    have hpowers : (2679/25000 : ℝ)^4181 ≤ (171173283846729/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2679 : ℕ)^4181*1562500000000000000^1024 ≤ 171173283846729^1024*25000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2679 25000 171173283846729 1562500000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2679/25000 : ℝ)) (X := (171173283846729/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (4181/1024 : ℝ) ≤ (8127635159206527/20000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^4181 ≤ (8127635159206527/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14773 : ℕ)^4181*20000000000000000000^1024 ≤ 8127635159206527^1024*100000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 8127635159206527 20000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (8127635159206527/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781421173283846729/781250000000000000 : ℝ) ≤ (2500134143560099/2500000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (781421173283846729/781250000000000000 : ℝ)^1024 ≤ (2500134143560099/2500000000000000 : ℝ)^4181 := by
      have hnat : (781421173283846729 : ℕ)^1024*2500000000000000^4181 ≤ 2500134143560099^4181*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781421173283846729 781250000000000000 2500134143560099 2500000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134143560099/2500000000000000 : ℝ)) (X := (781421173283846729/781250000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051593265962223291/100000000000000000000 : ℝ) ≤ (10001263363229373/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (100051593265962223291/100000000000000000000 : ℝ)^1024 ≤ (10001263363229373/10000000000000000 : ℝ)^4181 := by
      have hnat : (100051593265962223291 : ℕ)^1024*10000000000000000^4181 ≤ 10001263363229373^4181*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051593265962223291 100000000000000000000 10001263363229373 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001263363229373/10000000000000000 : ℝ)) (X := (100051593265962223291/100000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008127635159206527/10000000000000000000 : ℝ) ≤ (200039803044367/200000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (10008127635159206527/10000000000000000000 : ℝ)^1024 ≤ (200039803044367/200000000000000 : ℝ)^4181 := by
      have hnat : (10008127635159206527 : ℕ)^1024*200000000000000^4181 ≤ 200039803044367^4181*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008127635159206527 10000000000000000000 200039803044367 200000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200039803044367/200000000000000 : ℝ)) (X := (10008127635159206527/10000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(171173283846729/1562500000000000000 : ℝ) ≤ ((10139150085020382877/10142500000000000000 : ℝ)+2*(726788988977/405700000000000 : ℝ)*(2679/25000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (10139150085020382877/10142500000000000000 : ℝ)+2*(726788988977/405700000000000 : ℝ)*(2679/25000 : ℝ)=(2500134143560099/2500000000000000 : ℝ) by norm_num, show 1+2*(171173283846729/1562500000000000000 : ℝ)=(781421173283846729/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8127635159206527/20000000000000000000 : ℝ)+(171173283846729/1562500000000000000 : ℝ) ≤ ((10139150085020382877/10142500000000000000 : ℝ)+(726788988977/405700000000000 : ℝ)*((14773/100000 : ℝ)+(2679/25000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (10139150085020382877/10142500000000000000 : ℝ)+(726788988977/405700000000000 : ℝ)*((14773/100000 : ℝ)+(2679/25000 : ℝ))=(10001263363229373/10000000000000000 : ℝ) by norm_num, show 1+(8127635159206527/20000000000000000000 : ℝ)+(171173283846729/1562500000000000000 : ℝ)=(100051593265962223291/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8127635159206527/20000000000000000000 : ℝ) ≤ ((10139150085020382877/10142500000000000000 : ℝ)+2*(726788988977/405700000000000 : ℝ)*(14773/100000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (10139150085020382877/10142500000000000000 : ℝ)+2*(726788988977/405700000000000 : ℝ)*(14773/100000 : ℝ)=(200039803044367/200000000000000 : ℝ) by norm_num, show 1+2*(8127635159206527/20000000000000000000 : ℝ)=(10008127635159206527/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10139150085020382877/10142500000000000000 : ℝ)*(X 1 0+X 2 0)+(726788988977/405700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (10139150085020382877/10142500000000000000 : ℝ)) (alpha := (726788988977/405700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10139150085020382877/10142500000000000000 : ℝ)*(X 0 1+X 2 1)+(726788988977/405700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (10139150085020382877/10142500000000000000 : ℝ)) (alpha := (726788988977/405700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10139150085020382877/10142500000000000000 : ℝ)*(X 0 2+X 1 2)+(726788988977/405700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (10139150085020382877/10142500000000000000 : ℝ)) (alpha := (726788988977/405700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430569681/2000000000 : ℝ)*X 0 0+(2700290839/5000000000 : ℝ)*X 0 1+(5258596847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346674323/10000000000 : ℝ)*X 1 0+(-2224983581/10000000000 : ℝ)*X 1 1+(5258596489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668334297/1250000000 : ℝ)*X 2 0+(5258596193/10000000000 : ℝ)*X 2 1+(-1112491951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180161077/5000000000 : ℝ)*X 0 0+(2110297047/5000000000 : ℝ)*X 0 1+(4504622193/10000000000 : ℝ)*X 0 2+(2180161077/5000000000 : ℝ)*X 1 0+(2110297047/5000000000 : ℝ)*X 1 1+(4504622193/10000000000 : ℝ)*X 1 2+(2180161077/5000000000 : ℝ)*X 2 0+(2110297047/5000000000 : ℝ)*X 2 1+(4504622193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269106919/1250000000 : ℝ)*X 0 0+(5258997647/10000000000 : ℝ)*X 0 1+(2700089581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310629679/10000000000 : ℝ)*X 1 0+(-260425149/1250000000 : ℝ)*X 1 1+(1350044793/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531062969/1000000000 : ℝ)*X 2 0+(5400179169/10000000000 : ℝ)*X 2 1+(-2083401183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360336069/10000000000 : ℝ)*X 0 0+(4503819883/10000000000 : ℝ)*X 0 1+(211069971/500000000 : ℝ)*X 0 2+(4360336069/10000000000 : ℝ)*X 1 0+(4503819883/10000000000 : ℝ)*X 1 1+(211069971/500000000 : ℝ)*X 1 2+(4360336069/10000000000 : ℝ)*X 2 0+(4503819883/10000000000 : ℝ)*X 2 1+(211069971/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5079436325205399011508481311/507125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1048812071/50000000000000 : ℝ)*(base19) + (229542711/10000000000000 : ℝ)*(base23) + (112482317/50000000000000 : ℝ)*(upper3) + (3317249/4000000000000 : ℝ)*(lower4) + (5281960535461281/100000000000000 : ℝ)*(major0) + (5281960535461281/100000000000000 : ℝ)*(major1) + (5281960535461281/100000000000000 : ℝ)*(major2) + (1760763500689971/25000000000000 : ℝ)*(sp0) + (7043088453554311/100000000000000 : ℝ)*(sp1) + (880385529093547/12500000000000 : ℝ)*(sp2) + (3520802463838679/100000000000000 : ℝ)*(sp3) + (36548418569/100000000000000 : ℝ)*(sp4) + (4023002967/100000000000000 : ℝ)*(sp6) + (13861017001/50000000000000 : ℝ)*(sp7) + (1760415092936341/50000000000000 : ℝ)*(f.failure) + (7043090551178453/100000000000000 : ℝ)*(f.sum) + (136261946406677/20285000000000000000000000000 : ℝ)*base65 + (1952611447322439563/1014250000000000000000000000000000 : ℝ)*base68 + (3345065866167939563/1014250000000000000000000000000000 : ℝ)*base70 + (139854186430060437/1014250000000000000000000000000000 : ℝ)*base71 + (7185746293469/2535625000000000000000000000 : ℝ)*base73 + (7125448604598189563/1014250000000000000000000000000000 : ℝ)*base76 + (1343315411499810437/1014250000000000000000000000000000 : ℝ)*base77 + (10343719249890439563/1014250000000000000000000000000000 : ℝ)*base80 + (3076065118947/20285000000000000000000000000 : ℝ)*base81 + (20353483/1000000000000000000000 : ℝ)*base89 + (20353483/1000000000000000000000 : ℝ)*base91 + (20353483/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (234410278980517029699752097/63390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (549497429/100000000000000 : ℝ)*(base19) + (335175861/50000000000000 : ℝ)*(base23) + (39455767/50000000000000 : ℝ)*(upper3) + (22038083/50000000000000 : ℝ)*(lower4) + (59621881/100000000000000 : ℝ)*(upper5) + (663993665329679/12500000000000 : ℝ)*(major0) + (663993665329679/12500000000000 : ℝ)*(major1) + (663993665329679/12500000000000 : ℝ)*(major2) + (1277914151/10000000000000 : ℝ)*(sp1) + (3239071031/20000000000000 : ℝ)*(sp2) + (7083078518643363/100000000000000 : ℝ)*(sp4) + (885383148750553/12500000000000 : ℝ)*(sp5) + (3541530826468243/50000000000000 : ℝ)*(sp6) + (1770410001684583/50000000000000 : ℝ)*(sp7) + (1770410001684583/50000000000000 : ℝ)*(f.failure) + (7083078518643363/100000000000000 : ℝ)*(f.sum) + (35474113790583/10142500000000000000000000000 : ℝ)*base66 + (681509252873387267/126781250000000000000000000000000 : ℝ)*base68 + (449992882247106017/126781250000000000000000000000000 : ℝ)*base70 + (234922507796418517/126781250000000000000000000000000 : ℝ)*base72 + (38676690267009/5071250000000000000000000000 : ℝ)*base74 + (3316594726565356017/126781250000000000000000000000000 : ℝ)*base76 + (990250963598231017/126781250000000000000000000000000 : ℝ)*base78 + (693428996270762267/126781250000000000000000000000000 : ℝ)*base80 + (6458020263739/5071250000000000000000000000 : ℝ)*base82 + (14460729/1000000000000000000000 : ℝ)*base89 + (14460729/1000000000000000000000 : ℝ)*base91 + (14460729/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1170_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s5_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153426111/10000000000 : ℝ)*x 0 + (5394189139/10000000000 : ℝ)*x 1 + (1316152513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153426111/10000000000 : ℝ)^8363 ≤ (1635947015109/12500000000000 : ℝ)^6315 := by
    have hnat : (2153426111 : ℕ)^8363*12500000000000^6315 ≤ 1635947015109^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153426111 10000000000 1635947015109 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394189139/10000000000 : ℝ)^8363 ≤ (44155814051681/100000000000000 : ℝ)^6315 := by
    have hnat : (5394189139 : ℕ)^8363*100000000000000^6315 ≤ 44155814051681^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394189139 10000000000 44155814051681 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316152513/2500000000 : ℝ)^8363 ≤ (10689152453611/25000000000000 : ℝ)^6315 := by
    have hnat : (1316152513 : ℕ)^8363*25000000000000^6315 ≤ 10689152453611^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316152513 2500000000 10689152453611 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153426111/10000000000 : ℝ), (5394189139/10000000000 : ℝ), (1316152513/2500000000 : ℝ)] ![(1635947015109/12500000000000 : ℝ), (44155814051681/100000000000000 : ℝ), (10689152453611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153426111/10000000000 : ℝ)|^8363 ≤ (1635947015109/12500000000000 : ℝ)^6315
        have hw : |(-2153426111/10000000000 : ℝ)|=(2153426111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394189139/10000000000 : ℝ)|^8363 ≤ (44155814051681/100000000000000 : ℝ)^6315
        have hw : |(5394189139/10000000000 : ℝ)|=(5394189139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316152513/2500000000 : ℝ)|^8363 ≤ (10689152453611/25000000000000 : ℝ)^6315
        have hw : |(1316152513/2500000000 : ℝ)|=(1316152513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345066669/10000000000 : ℝ)*x 0 + (-2219167611/10000000000 : ℝ)*x 1 + (5264610039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345066669/10000000000 : ℝ)^8363 ≤ (218120442309/500000000000 : ℝ)^6315 := by
    have hnat : (5345066669 : ℕ)^8363*500000000000^6315 ≤ 218120442309^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345066669 10000000000 218120442309 500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219167611/10000000000 : ℝ)^8363 ≤ (53200397869/390625000000 : ℝ)^6315 := by
    have hnat : (2219167611 : ℕ)^8363*390625000000^6315 ≤ 53200397869^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219167611 10000000000 53200397869 390625000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264610039/10000000000 : ℝ)^8363 ≤ (342052877397/800000000000 : ℝ)^6315 := by
    have hnat : (5264610039 : ℕ)^8363*800000000000^6315 ≤ 342052877397^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264610039 10000000000 342052877397 800000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345066669/10000000000 : ℝ), (-2219167611/10000000000 : ℝ), (5264610039/10000000000 : ℝ)] ![(218120442309/500000000000 : ℝ), (53200397869/390625000000 : ℝ), (342052877397/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345066669/10000000000 : ℝ)|^8363 ≤ (218120442309/500000000000 : ℝ)^6315
        have hw : |(5345066669/10000000000 : ℝ)|=(5345066669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219167611/10000000000 : ℝ)|^8363 ≤ (53200397869/390625000000 : ℝ)^6315
        have hw : |(-2219167611/10000000000 : ℝ)|=(2219167611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264610039/10000000000 : ℝ)|^8363 ≤ (342052877397/800000000000 : ℝ)^6315
        have hw : |(5264610039/10000000000 : ℝ)|=(5264610039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672533373/5000000000 : ℝ)*x 0 + (5264609917/10000000000 : ℝ)*x 1 + (-554791917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672533373/5000000000 : ℝ)^8363 ≤ (1363252790439/3125000000000 : ℝ)^6315 := by
    have hnat : (2672533373 : ℕ)^8363*3125000000000^6315 ≤ 1363252790439^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672533373 5000000000 1363252790439 3125000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264609917/10000000000 : ℝ)^8363 ≤ (10689152090617/25000000000000 : ℝ)^6315 := by
    have hnat : (5264609917 : ℕ)^8363*25000000000000^6315 ≤ 10689152090617^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264609917 10000000000 10689152090617 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554791917/2500000000 : ℝ)^8363 ≤ (425603197429/3125000000000 : ℝ)^6315 := by
    have hnat : (554791917 : ℕ)^8363*3125000000000^6315 ≤ 425603197429^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554791917 2500000000 425603197429 3125000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672533373/5000000000 : ℝ), (5264609917/10000000000 : ℝ), (-554791917/2500000000 : ℝ)] ![(1363252790439/3125000000000 : ℝ), (10689152090617/25000000000000 : ℝ), (425603197429/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672533373/5000000000 : ℝ)|^8363 ≤ (1363252790439/3125000000000 : ℝ)^6315
        have hw : |(2672533373/5000000000 : ℝ)|=(2672533373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264609917/10000000000 : ℝ)|^8363 ≤ (10689152090617/25000000000000 : ℝ)^6315
        have hw : |(5264609917/10000000000 : ℝ)|=(5264609917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554791917/2500000000 : ℝ)|^8363 ≤ (425603197429/3125000000000 : ℝ)^6315
        have hw : |(-554791917/2500000000 : ℝ)|=(554791917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872132083/2000000000 : ℝ)*x 0 + (4232958731/10000000000 : ℝ)*x 1 + (1123042483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872132083/2000000000 : ℝ)^8363 ≤ (4164534687053/12500000000000 : ℝ)^6315 := by
    have hnat : (872132083 : ℕ)^8363*12500000000000^6315 ≤ 4164534687053^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872132083 2000000000 4164534687053 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232958731/10000000000 : ℝ)^8363 ≤ (16015186814031/50000000000000 : ℝ)^6315 := by
    have hnat : (4232958731 : ℕ)^8363*50000000000000^6315 ≤ 16015186814031^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232958731 10000000000 16015186814031 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123042483/2500000000 : ℝ)^8363 ≤ (17326674426101/50000000000000 : ℝ)^6315 := by
    have hnat : (1123042483 : ℕ)^8363*50000000000000^6315 ≤ 17326674426101^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123042483 2500000000 17326674426101 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872132083/2000000000 : ℝ), (4232958731/10000000000 : ℝ), (1123042483/2500000000 : ℝ)] ![(4164534687053/12500000000000 : ℝ), (16015186814031/50000000000000 : ℝ), (17326674426101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872132083/2000000000 : ℝ)|^8363 ≤ (4164534687053/12500000000000 : ℝ)^6315
        have hw : |(872132083/2000000000 : ℝ)|=(872132083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232958731/10000000000 : ℝ)|^8363 ≤ (16015186814031/50000000000000 : ℝ)^6315
        have hw : |(4232958731/10000000000 : ℝ)|=(4232958731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123042483/2500000000 : ℝ)|^8363 ≤ (17326674426101/50000000000000 : ℝ)^6315
        have hw : |(1123042483/2500000000 : ℝ)|=(1123042483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153431253/10000000000 : ℝ)*x 0 + (5264944633/10000000000 : ℝ)*x 1 + (5393853361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153431253/10000000000 : ℝ)^8363 ≤ (2617523501313/20000000000000 : ℝ)^6315 := by
    have hnat : (2153431253 : ℕ)^8363*20000000000000^6315 ≤ 2617523501313^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153431253 10000000000 2617523501313 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264944633/10000000000 : ℝ)^8363 ≤ (10690052099407/25000000000000 : ℝ)^6315 := by
    have hnat : (5264944633 : ℕ)^8363*25000000000000^6315 ≤ 10690052099407^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264944633 10000000000 10690052099407 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393853361/10000000000 : ℝ)^8363 ≤ (8830434815469/20000000000000 : ℝ)^6315 := by
    have hnat : (5393853361 : ℕ)^8363*20000000000000^6315 ≤ 8830434815469^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393853361 10000000000 8830434815469 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153431253/10000000000 : ℝ), (5264944633/10000000000 : ℝ), (5393853361/10000000000 : ℝ)] ![(2617523501313/20000000000000 : ℝ), (10690052099407/25000000000000 : ℝ), (8830434815469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153431253/10000000000 : ℝ)|^8363 ≤ (2617523501313/20000000000000 : ℝ)^6315
        have hw : |(-2153431253/10000000000 : ℝ)|=(2153431253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264944633/10000000000 : ℝ)|^8363 ≤ (10690052099407/25000000000000 : ℝ)^6315
        have hw : |(5264944633/10000000000 : ℝ)|=(5264944633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393853361/10000000000 : ℝ)|^8363 ≤ (8830434815469/20000000000000 : ℝ)^6315
        have hw : |(5393853361/10000000000 : ℝ)|=(5393853361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106243417/200000000 : ℝ)*x 0 + (-1044961747/5000000000 : ℝ)*x 1 + (539385351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106243417/200000000 : ℝ)^8363 ≤ (8653778428757/20000000000000 : ℝ)^6315 := by
    have hnat : (106243417 : ℕ)^8363*20000000000000^6315 ≤ 8653778428757^6315*200000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106243417 200000000 8653778428757 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044961747/5000000000 : ℝ)^8363 ≤ (3144733037119/25000000000000 : ℝ)^6315 := by
    have hnat : (1044961747 : ℕ)^8363*25000000000000^6315 ≤ 3144733037119^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044961747 5000000000 3144733037119 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539385351/1000000000 : ℝ)^8363 ≤ (44152175692551/100000000000000 : ℝ)^6315 := by
    have hnat : (539385351 : ℕ)^8363*100000000000000^6315 ≤ 44152175692551^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539385351 1000000000 44152175692551 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106243417/200000000 : ℝ), (-1044961747/5000000000 : ℝ), (539385351/1000000000 : ℝ)] ![(8653778428757/20000000000000 : ℝ), (3144733037119/25000000000000 : ℝ), (44152175692551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106243417/200000000 : ℝ)|^8363 ≤ (8653778428757/20000000000000 : ℝ)^6315
        have hw : |(106243417/200000000 : ℝ)|=(106243417/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044961747/5000000000 : ℝ)|^8363 ≤ (3144733037119/25000000000000 : ℝ)^6315
        have hw : |(-1044961747/5000000000 : ℝ)|=(1044961747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539385351/1000000000 : ℝ)|^8363 ≤ (44152175692551/100000000000000 : ℝ)^6315
        have hw : |(539385351/1000000000 : ℝ)|=(539385351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328042573/2500000000 : ℝ)*x 0 + (539385397/1000000000 : ℝ)*x 1 + (-261240453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328042573/2500000000 : ℝ)^8363 ≤ (43268886124753/100000000000000 : ℝ)^6315 := by
    have hnat : (1328042573 : ℕ)^8363*100000000000000^6315 ≤ 43268886124753^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328042573 2500000000 43268886124753 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539385397/1000000000 : ℝ)^8363 ≤ (22076090339547/50000000000000 : ℝ)^6315 := by
    have hnat : (539385397 : ℕ)^8363*50000000000000^6315 ≤ 22076090339547^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539385397 1000000000 22076090339547 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261240453/1250000000 : ℝ)^8363 ≤ (12578933184681/100000000000000 : ℝ)^6315 := by
    have hnat : (261240453 : ℕ)^8363*100000000000000^6315 ≤ 12578933184681^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261240453 1250000000 12578933184681 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328042573/2500000000 : ℝ), (539385397/1000000000 : ℝ), (-261240453/1250000000 : ℝ)] ![(43268886124753/100000000000000 : ℝ), (22076090339547/50000000000000 : ℝ), (12578933184681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328042573/2500000000 : ℝ)|^8363 ≤ (43268886124753/100000000000000 : ℝ)^6315
        have hw : |(1328042573/2500000000 : ℝ)|=(1328042573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539385397/1000000000 : ℝ)|^8363 ≤ (22076090339547/50000000000000 : ℝ)^6315
        have hw : |(539385397/1000000000 : ℝ)|=(539385397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261240453/1250000000 : ℝ)|^8363 ≤ (12578933184681/100000000000000 : ℝ)^6315
        have hw : |(-261240453/1250000000 : ℝ)|=(261240453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s5_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360671/10000000 : ℝ)*x 0 + (1122875263/2500000000 : ℝ)*x 1 + (1058407477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360671/10000000 : ℝ)^8363 ≤ (33316384595069/100000000000000 : ℝ)^6315 := by
    have hnat : (4360671 : ℕ)^8363*100000000000000^6315 ≤ 33316384595069^6315*10000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360671 10000000 33316384595069 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122875263/2500000000 : ℝ)^8363 ≤ (1732325789401/5000000000000 : ℝ)^6315 := by
    have hnat : (1122875263 : ℕ)^8363*5000000000000^6315 ≤ 1732325789401^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122875263 2500000000 1732325789401 5000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058407477/2500000000 : ℝ)^8363 ≤ (32037099598333/100000000000000 : ℝ)^6315 := by
    have hnat : (1058407477 : ℕ)^8363*100000000000000^6315 ≤ 32037099598333^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058407477 2500000000 32037099598333 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360671/10000000 : ℝ), (1122875263/2500000000 : ℝ), (1058407477/2500000000 : ℝ)] ![(33316384595069/100000000000000 : ℝ), (1732325789401/5000000000000 : ℝ), (32037099598333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360671/10000000 : ℝ)|^8363 ≤ (33316384595069/100000000000000 : ℝ)^6315
        have hw : |(4360671/10000000 : ℝ)|=(4360671/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122875263/2500000000 : ℝ)|^8363 ≤ (1732325789401/5000000000000 : ℝ)^6315
        have hw : |(1122875263/2500000000 : ℝ)|=(1122875263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058407477/2500000000 : ℝ)|^8363 ≤ (32037099598333/100000000000000 : ℝ)^6315
        have hw : |(1058407477/2500000000 : ℝ)|=(1058407477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2839/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11227/100000 : ℝ) ^ (4181/1024 : ℝ) ≤ (13250106217634403/100000000000000000000 : ℝ) := by
    have hpowers : (11227/100000 : ℝ)^4181 ≤ (13250106217634403/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11227 : ℕ)^4181*100000000000000000000^1024 ≤ 13250106217634403^1024*100000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11227 100000 13250106217634403 100000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11227/100000 : ℝ)) (X := (13250106217634403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4181/1024 : ℝ) ≤ (34916231891098471/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4181 ≤ (34916231891098471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4181*100000000000000000000^1024 ≤ 34916231891098471^1024*50000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34916231891098471 100000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34916231891098471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013250106217634403/50000000000000000000 : ℝ) ≤ (2000129794321917/2000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50013250106217634403/50000000000000000000 : ℝ)^1024 ≤ (2000129794321917/2000000000000000 : ℝ)^4181 := by
      have hnat : (50013250106217634403 : ℕ)^1024*2000000000000000^4181 ≤ 2000129794321917^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013250106217634403 50000000000000000000 2000129794321917 2000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000129794321917/2000000000000000 : ℝ)) (X := (50013250106217634403/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024083169054366437/50000000000000000000 : ℝ) ≤ (400047178534889/400000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50024083169054366437/50000000000000000000 : ℝ)^1024 ≤ (400047178534889/400000000000000 : ℝ)^4181 := by
      have hnat : (50024083169054366437 : ℕ)^1024*400000000000000^4181 ≤ 400047178534889^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024083169054366437 50000000000000000000 400047178534889 400000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400047178534889/400000000000000 : ℝ)) (X := (50024083169054366437/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034916231891098471/50000000000000000000 : ℝ) ≤ (2000341991026973/2000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50034916231891098471/50000000000000000000 : ℝ)^1024 ≤ (2000341991026973/2000000000000000 : ℝ)^4181 := by
      have hnat : (50034916231891098471 : ℕ)^1024*2000000000000000^4181 ≤ 2000341991026973^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034916231891098471 50000000000000000000 2000341991026973 2000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000341991026973/2000000000000000 : ℝ)) (X := (50034916231891098471/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13250106217634403/100000000000000000000 : ℝ) ≤ ((6012007959118340707/6014000000000000000 : ℝ)+2*(6631147033/3758750000000 : ℝ)*(11227/100000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (6012007959118340707/6014000000000000000 : ℝ)+2*(6631147033/3758750000000 : ℝ)*(11227/100000 : ℝ)=(2000129794321917/2000000000000000 : ℝ) by norm_num, show 1+2*(13250106217634403/100000000000000000000 : ℝ)=(50013250106217634403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34916231891098471/100000000000000000000 : ℝ)+(13250106217634403/100000000000000000000 : ℝ) ≤ ((6012007959118340707/6014000000000000000 : ℝ)+(6631147033/3758750000000 : ℝ)*((7117/50000 : ℝ)+(11227/100000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (6012007959118340707/6014000000000000000 : ℝ)+(6631147033/3758750000000 : ℝ)*((7117/50000 : ℝ)+(11227/100000 : ℝ))=(400047178534889/400000000000000 : ℝ) by norm_num, show 1+(34916231891098471/100000000000000000000 : ℝ)+(13250106217634403/100000000000000000000 : ℝ)=(50024083169054366437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34916231891098471/100000000000000000000 : ℝ) ≤ ((6012007959118340707/6014000000000000000 : ℝ)+2*(6631147033/3758750000000 : ℝ)*(7117/50000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (6012007959118340707/6014000000000000000 : ℝ)+2*(6631147033/3758750000000 : ℝ)*(7117/50000 : ℝ)=(2000341991026973/2000000000000000 : ℝ) by norm_num, show 1+2*(34916231891098471/100000000000000000000 : ℝ)=(50034916231891098471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6012007959118340707/6014000000000000000 : ℝ)*(X 1 0+X 2 0)+(6631147033/3758750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (6012007959118340707/6014000000000000000 : ℝ)) (alpha := (6631147033/3758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6012007959118340707/6014000000000000000 : ℝ)*(X 0 1+X 2 1)+(6631147033/3758750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (6012007959118340707/6014000000000000000 : ℝ)) (alpha := (6631147033/3758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6012007959118340707/6014000000000000000 : ℝ)*(X 0 2+X 1 2)+(6631147033/3758750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (6012007959118340707/6014000000000000000 : ℝ)) (alpha := (6631147033/3758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2153426111/10000000000 : ℝ)*X 0 0+(5394189139/10000000000 : ℝ)*X 0 1+(1316152513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345066669/10000000000 : ℝ)*X 1 0+(-2219167611/10000000000 : ℝ)*X 1 1+(5264610039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672533373/5000000000 : ℝ)*X 2 0+(5264609917/10000000000 : ℝ)*X 2 1+(-554791917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872132083/2000000000 : ℝ)*X 0 0+(4232958731/10000000000 : ℝ)*X 0 1+(1123042483/2500000000 : ℝ)*X 0 2+(872132083/2000000000 : ℝ)*X 1 0+(4232958731/10000000000 : ℝ)*X 1 1+(1123042483/2500000000 : ℝ)*X 1 2+(872132083/2000000000 : ℝ)*X 2 0+(4232958731/10000000000 : ℝ)*X 2 1+(1123042483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153431253/10000000000 : ℝ)*X 0 0+(5264944633/10000000000 : ℝ)*X 0 1+(5393853361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106243417/200000000 : ℝ)*X 1 0+(-1044961747/5000000000 : ℝ)*X 1 1+(539385351/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328042573/2500000000 : ℝ)*X 2 0+(539385397/1000000000 : ℝ)*X 2 1+(-261240453/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360671/10000000 : ℝ)*X 0 0+(1122875263/2500000000 : ℝ)*X 0 1+(1058407477/2500000000 : ℝ)*X 0 2+(4360671/10000000 : ℝ)*X 1 0+(1122875263/2500000000 : ℝ)*X 1 1+(1058407477/2500000000 : ℝ)*X 1 2+(4360671/10000000 : ℝ)*X 2 0+(1122875263/2500000000 : ℝ)*X 2 1+(1058407477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518985678759521341871911029/150350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24574849/10000000000000 : ℝ)*(base19) + (430074709/100000000000000 : ℝ)*(base23) + (8871883/12500000000000 : ℝ)*(lower2) + (8359307/50000000000000 : ℝ)*(upper3) + (55037689/50000000000000 : ℝ)*(lower4) + (5787590185065149/100000000000000 : ℝ)*(major0) + (5787590185065149/100000000000000 : ℝ)*(major1) + (5787590185065149/100000000000000 : ℝ)*(major2) + (1929325587111721/25000000000000 : ℝ)*(sp0) + (964663629616923/12500000000000 : ℝ)*(sp1) + (1543461770521833/20000000000000 : ℝ)*(sp2) + (964466048779389/25000000000000 : ℝ)*(sp3) + (693423699/10000000000000 : ℝ)*(sp4) + (1355453437/20000000000000 : ℝ)*(sp7) + (192893548619237/5000000000000 : ℝ)*(f.failure) + (3858654641341937/50000000000000 : ℝ)*(f.sum) + (127736821993/60140000000000000000000000 : ℝ)*base65 + (7231557493601879657/601400000000000000000000000000000 : ℝ)*base68 + (3312506693098920343/601400000000000000000000000000000 : ℝ)*base69 + (7439563130649479657/601400000000000000000000000000000 : ℝ)*base72 + (142479047443/46984375000000000000000000 : ℝ)*base74 + (19434978383766279657/601400000000000000000000000000000 : ℝ)*base76 + (2779441542721079657/601400000000000000000000000000000 : ℝ)*base78 + (2265389799464479657/601400000000000000000000000000000 : ℝ)*base80 + (1628669616563/187937500000000000000000000 : ℝ)*base81 + (959931/100000000000000000000 : ℝ)*base89 + (959931/100000000000000000000 : ℝ)*base91 + (959931/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140306861545466206653/75175000000000000000000000 : ℝ) := by norm_num
    linear_combination (37191061/3125000000000 : ℝ)*(base19) + (930263013/100000000000000 : ℝ)*(base23) + (143192077/50000000000000 : ℝ)*(lower4) + (4637331/25000000000000 : ℝ)*(lower5) + (1454415793861497/25000000000000 : ℝ)*(major0) + (1454415793861497/25000000000000 : ℝ)*(major1) + (1454415793861497/25000000000000 : ℝ)*(major2) + (51358054053/100000000000000 : ℝ)*(sp1) + (1685102821/3125000000000 : ℝ)*(sp2) + (8837070603/100000000000000 : ℝ)*(sp3) + (7757409370929093/100000000000000 : ℝ)*(sp4) + (7757356822761089/100000000000000 : ℝ)*(sp5) + (7757354517375809/100000000000000 : ℝ)*(sp6) + (387790808067883/10000000000000 : ℝ)*(sp7) + (484739614718679/12500000000000 : ℝ)*(f.failure) + (7757409370929093/100000000000000 : ℝ)*(f.sum) + (4383915339337/751750000000000000000000000 : ℝ)*base66 + (330902204318958379/150350000000000000000000000000000 : ℝ)*base67 + (1015871788033508379/150350000000000000000000000000000 : ℝ)*base69 + (959492236416541621/150350000000000000000000000000000 : ℝ)*base72 + (4498440608891/751750000000000000000000000 : ℝ)*base74 + (4209058167175891621/150350000000000000000000000000000 : ℝ)*base76 + (1147587007478091621/150350000000000000000000000000000 : ℝ)*base78 + (303308275619208379/150350000000000000000000000000000 : ℝ)*base79 + (2149377862051/751750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1992777/250000000000000000000 : ℝ)*base89 + (1992777/250000000000000000000 : ℝ)*base91 + (1992777/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1170_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1170_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1170_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1170_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1170_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

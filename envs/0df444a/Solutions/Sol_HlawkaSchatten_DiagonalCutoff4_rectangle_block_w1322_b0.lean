-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:39.619206+00:00
-- url     : https://prove2.me/submissions/8104b17f-2c4f-4936-973f-b4115fd3a903

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
theorem support_rectangle_w1322_s0_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-910514421/5000000000 : ℝ)*x 0 + (750699963/1250000000 : ℝ)*x 1 + (600764353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910514421/5000000000 : ℝ)^2141 ≤ (10661835943671/100000000000000 : ℝ)^1629 := by
    have hnat : (910514421 : ℕ)^2141*100000000000000^1629 ≤ 10661835943671^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910514421 5000000000 10661835943671 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750699963/1250000000 : ℝ)^2141 ≤ (25581495863331/50000000000000 : ℝ)^1629 := by
    have hnat : (750699963 : ℕ)^2141*50000000000000^1629 ≤ 25581495863331^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750699963 1250000000 25581495863331 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600764353/1250000000 : ℝ)^2141 ≤ (38175172318719/100000000000000 : ℝ)^1629 := by
    have hnat : (600764353 : ℕ)^2141*100000000000000^1629 ≤ 38175172318719^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600764353 1250000000 38175172318719 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-910514421/5000000000 : ℝ), (750699963/1250000000 : ℝ), (600764353/1250000000 : ℝ)] ![(10661835943671/100000000000000 : ℝ), (25581495863331/50000000000000 : ℝ), (38175172318719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-910514421/5000000000 : ℝ)|^2141 ≤ (10661835943671/100000000000000 : ℝ)^1629
        have hw : |(-910514421/5000000000 : ℝ)|=(910514421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750699963/1250000000 : ℝ)|^2141 ≤ (25581495863331/50000000000000 : ℝ)^1629
        have hw : |(750699963/1250000000 : ℝ)|=(750699963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600764353/1250000000 : ℝ)|^2141 ≤ (38175172318719/100000000000000 : ℝ)^1629
        have hw : |(600764353/1250000000 : ℝ)|=(600764353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5504053851/10000000000 : ℝ)*x 0 + (-2503807687/10000000000 : ℝ)*x 1 + (150191093/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504053851/10000000000 : ℝ)^2141 ≤ (2281121403757/5000000000000 : ℝ)^1629 := by
    have hnat : (5504053851 : ℕ)^2141*5000000000000^1629 ≤ 2281121403757^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504053851 10000000000 2281121403757 5000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503807687/10000000000 : ℝ)^2141 ≤ (16202398001981/100000000000000 : ℝ)^1629 := by
    have hnat : (2503807687 : ℕ)^2141*100000000000000^1629 ≤ 16202398001981^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503807687 10000000000 16202398001981 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150191093/312500000 : ℝ)^2141 ≤ (38175173905533/100000000000000 : ℝ)^1629 := by
    have hnat : (150191093 : ℕ)^2141*100000000000000^1629 ≤ 38175173905533^1629*312500000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150191093 312500000 38175173905533 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504053851/10000000000 : ℝ), (-2503807687/10000000000 : ℝ), (150191093/312500000 : ℝ)] ![(2281121403757/5000000000000 : ℝ), (16202398001981/100000000000000 : ℝ), (38175173905533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504053851/10000000000 : ℝ)|^2141 ≤ (2281121403757/5000000000000 : ℝ)^1629
        have hw : |(5504053851/10000000000 : ℝ)|=(5504053851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2503807687/10000000000 : ℝ)|^2141 ≤ (16202398001981/100000000000000 : ℝ)^1629
        have hw : |(-2503807687/10000000000 : ℝ)|=(2503807687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150191093/312500000 : ℝ)|^2141 ≤ (38175173905533/100000000000000 : ℝ)^1629
        have hw : |(150191093/312500000 : ℝ)|=(150191093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5504053121/10000000000 : ℝ)*x 0 + (4806115341/10000000000 : ℝ)*x 1 + (-1251904087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504053121/10000000000 : ℝ)^2141 ≤ (2851401257653/6250000000000 : ℝ)^1629 := by
    have hnat : (5504053121 : ℕ)^2141*6250000000000^1629 ≤ 2851401257653^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504053121 10000000000 2851401257653 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4806115341/10000000000 : ℝ)^2141 ≤ (1527007108639/4000000000000 : ℝ)^1629 := by
    have hnat : (4806115341 : ℕ)^2141*4000000000000^1629 ≤ 1527007108639^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806115341 10000000000 1527007108639 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251904087/5000000000 : ℝ)^2141 ≤ (16202402143913/100000000000000 : ℝ)^1629 := by
    have hnat : (1251904087 : ℕ)^2141*100000000000000^1629 ≤ 16202402143913^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251904087 5000000000 16202402143913 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504053121/10000000000 : ℝ), (4806115341/10000000000 : ℝ), (-1251904087/5000000000 : ℝ)] ![(2851401257653/6250000000000 : ℝ), (1527007108639/4000000000000 : ℝ), (16202402143913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504053121/10000000000 : ℝ)|^2141 ≤ (2851401257653/6250000000000 : ℝ)^1629
        have hw : |(5504053121/10000000000 : ℝ)|=(5504053121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4806115341/10000000000 : ℝ)|^2141 ≤ (1527007108639/4000000000000 : ℝ)^1629
        have hw : |(4806115341/10000000000 : ℝ)|=(4806115341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1251904087/5000000000 : ℝ)|^2141 ≤ (16202402143913/100000000000000 : ℝ)^1629
        have hw : |(-1251904087/5000000000 : ℝ)|=(1251904087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (836351277/2000000000 : ℝ)*x 0 + (1553809429/5000000000 : ℝ)*x 1 + (700141617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836351277/2000000000 : ℝ)^2141 ≤ (31794393519323/100000000000000 : ℝ)^1629 := by
    have hnat : (836351277 : ℕ)^2141*100000000000000^1629 ≤ 31794393519323^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836351277 2000000000 31794393519323 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553809429/5000000000 : ℝ)^2141 ≤ (10761334782917/50000000000000 : ℝ)^1629 := by
    have hnat : (1553809429 : ℕ)^2141*50000000000000^1629 ≤ 10761334782917^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553809429 5000000000 10761334782917 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (700141617/1250000000 : ℝ)^2141 ≤ (46682936899239/100000000000000 : ℝ)^1629 := by
    have hnat : (700141617 : ℕ)^2141*100000000000000^1629 ≤ 46682936899239^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700141617 1250000000 46682936899239 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836351277/2000000000 : ℝ), (1553809429/5000000000 : ℝ), (700141617/1250000000 : ℝ)] ![(31794393519323/100000000000000 : ℝ), (10761334782917/50000000000000 : ℝ), (46682936899239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836351277/2000000000 : ℝ)|^2141 ≤ (31794393519323/100000000000000 : ℝ)^1629
        have hw : |(836351277/2000000000 : ℝ)|=(836351277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553809429/5000000000 : ℝ)|^2141 ≤ (10761334782917/50000000000000 : ℝ)^1629
        have hw : |(1553809429/5000000000 : ℝ)|=(1553809429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(700141617/1250000000 : ℝ)|^2141 ≤ (46682936899239/100000000000000 : ℝ)^1629
        have hw : |(700141617/1250000000 : ℝ)|=(700141617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-114099459/625000000 : ℝ)*x 0 + (4837022161/10000000000 : ℝ)*x 1 + (119471799/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114099459/625000000 : ℝ)^2141 ≤ (10696958384383/100000000000000 : ℝ)^1629 := by
    have hnat : (114099459 : ℕ)^2141*100000000000000^1629 ≤ 10696958384383^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114099459 625000000 10696958384383 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4837022161/10000000000 : ℝ)^2141 ≤ (38498157111623/100000000000000 : ℝ)^1629 := by
    have hnat : (4837022161 : ℕ)^2141*100000000000000^1629 ≤ 38498157111623^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837022161 10000000000 38498157111623 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119471799/200000000 : ℝ)^2141 ≤ (50804884487109/100000000000000 : ℝ)^1629 := by
    have hnat : (119471799 : ℕ)^2141*100000000000000^1629 ≤ 50804884487109^1629*200000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119471799 200000000 50804884487109 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114099459/625000000 : ℝ), (4837022161/10000000000 : ℝ), (119471799/200000000 : ℝ)] ![(10696958384383/100000000000000 : ℝ), (38498157111623/100000000000000 : ℝ), (50804884487109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114099459/625000000 : ℝ)|^2141 ≤ (10696958384383/100000000000000 : ℝ)^1629
        have hw : |(-114099459/625000000 : ℝ)|=(114099459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4837022161/10000000000 : ℝ)|^2141 ≤ (38498157111623/100000000000000 : ℝ)^1629
        have hw : |(4837022161/10000000000 : ℝ)|=(4837022161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119471799/200000000 : ℝ)|^2141 ≤ (50804884487109/100000000000000 : ℝ)^1629
        have hw : |(119471799/200000000 : ℝ)|=(119471799/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2588643893/5000000000 : ℝ)*x 0 + (-1336333647/10000000000 : ℝ)*x 1 + (2986794923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588643893/5000000000 : ℝ)^2141 ≤ (42096281140789/100000000000000 : ℝ)^1629 := by
    have hnat : (2588643893 : ℕ)^2141*100000000000000^1629 ≤ 42096281140789^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588643893 5000000000 42096281140789 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336333647/10000000000 : ℝ)^2141 ≤ (1774708880323/25000000000000 : ℝ)^1629 := by
    have hnat : (1336333647 : ℕ)^2141*25000000000000^1629 ≤ 1774708880323^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336333647 10000000000 1774708880323 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2986794923/5000000000 : ℝ)^2141 ≤ (50804883324593/100000000000000 : ℝ)^1629 := by
    have hnat : (2986794923 : ℕ)^2141*100000000000000^1629 ≤ 50804883324593^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2986794923 5000000000 50804883324593 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588643893/5000000000 : ℝ), (-1336333647/10000000000 : ℝ), (2986794923/5000000000 : ℝ)] ![(42096281140789/100000000000000 : ℝ), (1774708880323/25000000000000 : ℝ), (50804883324593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588643893/5000000000 : ℝ)|^2141 ≤ (42096281140789/100000000000000 : ℝ)^1629
        have hw : |(2588643893/5000000000 : ℝ)|=(2588643893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1336333647/10000000000 : ℝ)|^2141 ≤ (1774708880323/25000000000000 : ℝ)^1629
        have hw : |(-1336333647/10000000000 : ℝ)|=(1336333647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2986794923/5000000000 : ℝ)|^2141 ≤ (50804883324593/100000000000000 : ℝ)^1629
        have hw : |(2986794923/5000000000 : ℝ)|=(2986794923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5177287819/10000000000 : ℝ)*x 0 + (5973589909/10000000000 : ℝ)*x 1 + (-267266699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177287819/10000000000 : ℝ)^2141 ≤ (10524070373361/25000000000000 : ℝ)^1629 := by
    have hnat : (5177287819 : ℕ)^2141*25000000000000^1629 ≤ 10524070373361^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177287819 10000000000 10524070373361 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5973589909/10000000000 : ℝ)^2141 ≤ (50804884028809/100000000000000 : ℝ)^1629 := by
    have hnat : (5973589909 : ℕ)^2141*100000000000000^1629 ≤ 50804884028809^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973589909 10000000000 50804884028809 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267266699/2000000000 : ℝ)^2141 ≤ (3549417230029/50000000000000 : ℝ)^1629 := by
    have hnat : (267266699 : ℕ)^2141*50000000000000^1629 ≤ 3549417230029^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267266699 2000000000 3549417230029 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177287819/10000000000 : ℝ), (5973589909/10000000000 : ℝ), (-267266699/2000000000 : ℝ)] ![(10524070373361/25000000000000 : ℝ), (50804884028809/100000000000000 : ℝ), (3549417230029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177287819/10000000000 : ℝ)|^2141 ≤ (10524070373361/25000000000000 : ℝ)^1629
        have hw : |(5177287819/10000000000 : ℝ)|=(5177287819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5973589909/10000000000 : ℝ)|^2141 ≤ (50804884028809/100000000000000 : ℝ)^1629
        have hw : |(5973589909/10000000000 : ℝ)|=(5973589909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267266699/2000000000 : ℝ)|^2141 ≤ (3549417230029/50000000000000 : ℝ)^1629
        have hw : |(-267266699/2000000000 : ℝ)|=(267266699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s0_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4191240159/10000000000 : ℝ)*x 0 + (1107376551/2000000000 : ℝ)*x 1 + (3174160641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191240159/10000000000 : ℝ)^2141 ≤ (1594459838967/5000000000000 : ℝ)^1629 := by
    have hnat : (4191240159 : ℕ)^2141*5000000000000^1629 ≤ 1594459838967^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191240159 10000000000 1594459838967 5000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107376551/2000000000 : ℝ)^2141 ≤ (45980404166169/100000000000000 : ℝ)^1629 := by
    have hnat : (1107376551 : ℕ)^2141*100000000000000^1629 ≤ 45980404166169^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107376551 2000000000 45980404166169 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174160641/10000000000 : ℝ)^2141 ≤ (22130399027973/100000000000000 : ℝ)^1629 := by
    have hnat : (3174160641 : ℕ)^2141*100000000000000^1629 ≤ 22130399027973^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174160641 10000000000 22130399027973 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191240159/10000000000 : ℝ), (1107376551/2000000000 : ℝ), (3174160641/10000000000 : ℝ)] ![(1594459838967/5000000000000 : ℝ), (45980404166169/100000000000000 : ℝ), (22130399027973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191240159/10000000000 : ℝ)|^2141 ≤ (1594459838967/5000000000000 : ℝ)^1629
        have hw : |(4191240159/10000000000 : ℝ)|=(4191240159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107376551/2000000000 : ℝ)|^2141 ≤ (45980404166169/100000000000000 : ℝ)^1629
        have hw : |(1107376551/2000000000 : ℝ)|=(1107376551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174160641/10000000000 : ℝ)|^2141 ≤ (22130399027973/100000000000000 : ℝ)^1629
        have hw : |(3174160641/10000000000 : ℝ)|=(3174160641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3377/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4281/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4281 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4281*1^1024 ≤ 0^1024*1^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4281/1024 : ℝ) ≤ (2169434321949747463/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4281 ≤ (2169434321949747463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4281*100000000000000000000^1024 ≤ 2169434321949747463^1024*5^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2169434321949747463 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2169434321949747463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4281 := by
      have hnat : (1 : ℕ)^1024*1^4281 ≤ 1^4281*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102169434321949747463/100000000000000000000 : ℝ) ≤ (5025734614125339/5000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (102169434321949747463/100000000000000000000 : ℝ)^1024 ≤ (5025734614125339/5000000000000000 : ℝ)^4281 := by
      have hnat : (102169434321949747463 : ℕ)^1024*5000000000000000^4281 ≤ 5025734614125339^4281*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102169434321949747463 100000000000000000000 5025734614125339 5000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025734614125339/5000000000000000 : ℝ)) (X := (102169434321949747463/100000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52169434321949747463/50000000000000000000 : ℝ) ≤ (2525734614125339/2500000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (52169434321949747463/50000000000000000000 : ℝ)^1024 ≤ (2525734614125339/2500000000000000 : ℝ)^4281 := by
      have hnat : (52169434321949747463 : ℕ)^1024*2500000000000000^4281 ≤ 2525734614125339^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52169434321949747463 50000000000000000000 2525734614125339 2500000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525734614125339/2500000000000000 : ℝ)) (X := (52169434321949747463/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25734614125339/2000000000000000 : ℝ)*(0 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25734614125339/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2169434321949747463/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25734614125339/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (1 : ℝ)+(25734614125339/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025734614125339/5000000000000000 : ℝ) by norm_num, show 1+(2169434321949747463/100000000000000000000 : ℝ)+(0 : ℝ)=(102169434321949747463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2169434321949747463/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25734614125339/2000000000000000 : ℝ)*(2/5 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25734614125339/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525734614125339/2500000000000000 : ℝ) by norm_num, show 1+2*(2169434321949747463/100000000000000000000 : ℝ)=(52169434321949747463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25734614125339/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25734614125339/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25734614125339/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25734614125339/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25734614125339/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25734614125339/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-910514421/5000000000 : ℝ)*X 0 0+(750699963/1250000000 : ℝ)*X 0 1+(600764353/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5504053851/10000000000 : ℝ)*X 1 0+(-2503807687/10000000000 : ℝ)*X 1 1+(150191093/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504053121/10000000000 : ℝ)*X 2 0+(4806115341/10000000000 : ℝ)*X 2 1+(-1251904087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((836351277/2000000000 : ℝ)*X 0 0+(1553809429/5000000000 : ℝ)*X 0 1+(700141617/1250000000 : ℝ)*X 0 2+(836351277/2000000000 : ℝ)*X 1 0+(1553809429/5000000000 : ℝ)*X 1 1+(700141617/1250000000 : ℝ)*X 1 2+(836351277/2000000000 : ℝ)*X 2 0+(1553809429/5000000000 : ℝ)*X 2 1+(700141617/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-114099459/625000000 : ℝ)*X 0 0+(4837022161/10000000000 : ℝ)*X 0 1+(119471799/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588643893/5000000000 : ℝ)*X 1 0+(-1336333647/10000000000 : ℝ)*X 1 1+(2986794923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177287819/10000000000 : ℝ)*X 2 0+(5973589909/10000000000 : ℝ)*X 2 1+(-267266699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191240159/10000000000 : ℝ)*X 0 0+(1107376551/2000000000 : ℝ)*X 0 1+(3174160641/10000000000 : ℝ)*X 0 2+(4191240159/10000000000 : ℝ)*X 1 0+(1107376551/2000000000 : ℝ)*X 1 1+(3174160641/10000000000 : ℝ)*X 1 2+(4191240159/10000000000 : ℝ)*X 2 0+(1107376551/2000000000 : ℝ)*X 2 1+(3174160641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5092952067988112043/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78545393/100000000000000 : ℝ)*(base1) + (326717307/25000000000000 : ℝ)*(base19) + (119629621/10000000000000 : ℝ)*(base23) + (5277313/2500000000000 : ℝ)*(upper3) + (52281133/100000000000000 : ℝ)*(upper5) + (617372073323053/100000000000000 : ℝ)*(major0) + (617372073323053/100000000000000 : ℝ)*(major1) + (617372073323053/100000000000000 : ℝ)*(major2) + (833695900330639/100000000000000 : ℝ)*(sp0) + (833698306026749/100000000000000 : ℝ)*(sp1) + (416849208299883/50000000000000 : ℝ)*(sp2) + (200521064014637/50000000000000 : ℝ)*(sp3) + (379111073/10000000000000 : ℝ)*(sp4) + (2157410391/100000000000000 : ℝ)*(sp7) + (200522181992529/50000000000000 : ℝ)*(f.failure) + (104212451611997/12500000000000 : ℝ)*(f.sum) + (221485230039967/100000000000000000000000000000 : ℝ)*base65 + (43360156460033/200000000000000000000000000000 : ℝ)*base68 + (662374246060033/200000000000000000000000000000 : ℝ)*base70 + (447838631460033/200000000000000000000000000000 : ℝ)*base72 + (357521106739967/100000000000000000000000000000 : ℝ)*base73 + (1214581643660033/200000000000000000000000000000 : ℝ)*base76 + (368619511139967/200000000000000000000000000000 : ℝ)*base77 + (49801479539967/200000000000000000000000000000 : ℝ)*base79 + (92735400960033/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25417/1250000000000000000000 : ℝ)*base89 + (25417/1250000000000000000000 : ℝ)*base91 + (25417/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37165588837119840607401/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88206773/5000000000000 : ℝ)*(base19) + (446963921/25000000000000 : ℝ)*(base23) + (61683719/100000000000000 : ℝ)*(base32) + (12133763/5000000000000 : ℝ)*(upper3) + (183723397/100000000000000 : ℝ)*(upper5) + (32577060841851/5000000000000 : ℝ)*(major0) + (32577060841851/5000000000000 : ℝ)*(major1) + (32577060841851/5000000000000 : ℝ)*(major2) + (31417391/800000000000 : ℝ)*(sp1) + (2107076327/50000000000000 : ℝ)*(sp2) + (175968315178667/20000000000000 : ℝ)*(sp4) + (879835884584001/100000000000000 : ℝ)*(sp5) + (879835573884997/100000000000000 : ℝ)*(sp6) + (105810137081597/25000000000000 : ℝ)*(sp7) + (423240610010107/100000000000000 : ℝ)*(f.failure) + (175968315178667/20000000000000 : ℝ)*(f.sum) + (4149246497511/5000000000000000000000000000 : ℝ)*base66 + (60801012012489/10000000000000000000000000000 : ℝ)*base67 + (67633408817511/10000000000000000000000000000 : ℝ)*base70 + (92577330267511/10000000000000000000000000000 : ℝ)*base72 + (45339969922489/5000000000000000000000000000 : ℝ)*base73 + (88364634777511/10000000000000000000000000000 : ℝ)*base76 + (20431632927511/10000000000000000000000000000 : ℝ)*base78 + (8636621507511/10000000000000000000000000000 : ℝ)*base80 + (17606761222511/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (654211/2500000000000000000000 : ℝ)*base89 + (654211/2500000000000000000000 : ℝ)*base91 + (654211/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3377/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_s1_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-200873059/1000000000 : ℝ)*x 0 + (353201979/625000000 : ℝ)*x 1 + (2520147591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200873059/1000000000 : ℝ)^2141 ≤ (12129075893697/100000000000000 : ℝ)^1629 := by
    have hnat : (200873059 : ℕ)^2141*100000000000000^1629 ≤ 12129075893697^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200873059 1000000000 12129075893697 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353201979/625000000 : ℝ)^2141 ≤ (9446498935161/20000000000000 : ℝ)^1629 := by
    have hnat : (353201979 : ℕ)^2141*20000000000000^1629 ≤ 9446498935161^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353201979 625000000 9446498935161 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520147591/5000000000 : ℝ)^2141 ≤ (40638429420279/100000000000000 : ℝ)^1629 := by
    have hnat : (2520147591 : ℕ)^2141*100000000000000^1629 ≤ 40638429420279^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520147591 5000000000 40638429420279 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200873059/1000000000 : ℝ), (353201979/625000000 : ℝ), (2520147591/5000000000 : ℝ)] ![(12129075893697/100000000000000 : ℝ), (9446498935161/20000000000000 : ℝ), (40638429420279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200873059/1000000000 : ℝ)|^2141 ≤ (12129075893697/100000000000000 : ℝ)^1629
        have hw : |(-200873059/1000000000 : ℝ)|=(200873059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(353201979/625000000 : ℝ)|^2141 ≤ (9446498935161/20000000000000 : ℝ)^1629
        have hw : |(353201979/625000000 : ℝ)|=(353201979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2520147591/5000000000 : ℝ)|^2141 ≤ (40638429420279/100000000000000 : ℝ)^1629
        have hw : |(2520147591/5000000000 : ℝ)|=(2520147591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5407814553/10000000000 : ℝ)*x 0 + (-2335305961/10000000000 : ℝ)*x 1 + (2520147669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407814553/10000000000 : ℝ)^2141 ≤ (22288440097783/50000000000000 : ℝ)^1629 := by
    have hnat : (5407814553 : ℕ)^2141*50000000000000^1629 ≤ 22288440097783^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407814553 10000000000 22288440097783 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2335305961/10000000000 : ℝ)^2141 ≤ (14784688722651/100000000000000 : ℝ)^1629 := by
    have hnat : (2335305961 : ℕ)^2141*100000000000000^1629 ≤ 14784688722651^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335305961 10000000000 14784688722651 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520147669/5000000000 : ℝ)^2141 ≤ (40638431073387/100000000000000 : ℝ)^1629 := by
    have hnat : (2520147669 : ℕ)^2141*100000000000000^1629 ≤ 40638431073387^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520147669 5000000000 40638431073387 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407814553/10000000000 : ℝ), (-2335305961/10000000000 : ℝ), (2520147669/5000000000 : ℝ)] ![(22288440097783/50000000000000 : ℝ), (14784688722651/100000000000000 : ℝ), (40638431073387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407814553/10000000000 : ℝ)|^2141 ≤ (22288440097783/50000000000000 : ℝ)^1629
        have hw : |(5407814553/10000000000 : ℝ)|=(5407814553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2335305961/10000000000 : ℝ)|^2141 ≤ (14784688722651/100000000000000 : ℝ)^1629
        have hw : |(-2335305961/10000000000 : ℝ)|=(2335305961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2520147669/5000000000 : ℝ)|^2141 ≤ (40638431073387/100000000000000 : ℝ)^1629
        have hw : |(2520147669/5000000000 : ℝ)|=(2520147669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (108156291/200000000 : ℝ)*x 0 + (5040295027/10000000000 : ℝ)*x 1 + (-58382659/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108156291/200000000 : ℝ)^2141 ≤ (5572110020383/12500000000000 : ℝ)^1629 := by
    have hnat : (108156291 : ℕ)^2141*12500000000000^1629 ≤ 5572110020383^1629*200000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108156291 200000000 5572110020383 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5040295027/10000000000 : ℝ)^2141 ≤ (5079803472221/12500000000000 : ℝ)^1629 := by
    have hnat : (5040295027 : ℕ)^2141*12500000000000^1629 ≤ 5079803472221^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040295027 10000000000 5079803472221 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58382659/250000000 : ℝ)^2141 ≤ (14784692042641/100000000000000 : ℝ)^1629 := by
    have hnat : (58382659 : ℕ)^2141*100000000000000^1629 ≤ 14784692042641^1629*250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58382659 250000000 14784692042641 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108156291/200000000 : ℝ), (5040295027/10000000000 : ℝ), (-58382659/250000000 : ℝ)] ![(5572110020383/12500000000000 : ℝ), (5079803472221/12500000000000 : ℝ), (14784692042641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108156291/200000000 : ℝ)|^2141 ≤ (5572110020383/12500000000000 : ℝ)^1629
        have hw : |(108156291/200000000 : ℝ)|=(108156291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5040295027/10000000000 : ℝ)|^2141 ≤ (5079803472221/12500000000000 : ℝ)^1629
        have hw : |(5040295027/10000000000 : ℝ)|=(5040295027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58382659/250000000 : ℝ)|^2141 ≤ (14784692042641/100000000000000 : ℝ)^1629
        have hw : |(-58382659/250000000 : ℝ)|=(58382659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (107396443/250000000 : ℝ)*x 0 + (1852360979/5000000000 : ℝ)*x 1 + (4974749357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107396443/250000000 : ℝ)^2141 ≤ (32939444831143/100000000000000 : ℝ)^1629 := by
    have hnat : (107396443 : ℕ)^2141*100000000000000^1629 ≤ 32939444831143^1629*250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107396443 250000000 32939444831143 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852360979/5000000000 : ℝ)^2141 ≤ (6778820220239/25000000000000 : ℝ)^1629 := by
    have hnat : (1852360979 : ℕ)^2141*25000000000000^1629 ≤ 6778820220239^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852360979 5000000000 6778820220239 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4974749357/10000000000 : ℝ)^2141 ≤ (39945274283909/100000000000000 : ℝ)^1629 := by
    have hnat : (4974749357 : ℕ)^2141*100000000000000^1629 ≤ 39945274283909^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974749357 10000000000 39945274283909 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107396443/250000000 : ℝ), (1852360979/5000000000 : ℝ), (4974749357/10000000000 : ℝ)] ![(32939444831143/100000000000000 : ℝ), (6778820220239/25000000000000 : ℝ), (39945274283909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107396443/250000000 : ℝ)|^2141 ≤ (32939444831143/100000000000000 : ℝ)^1629
        have hw : |(107396443/250000000 : ℝ)|=(107396443/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1852360979/5000000000 : ℝ)|^2141 ≤ (6778820220239/25000000000000 : ℝ)^1629
        have hw : |(1852360979/5000000000 : ℝ)|=(1852360979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4974749357/10000000000 : ℝ)|^2141 ≤ (39945274283909/100000000000000 : ℝ)^1629
        have hw : |(4974749357/10000000000 : ℝ)|=(4974749357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-200930539/1000000000 : ℝ)*x 0 + (631009937/1250000000 : ℝ)*x 1 + (5643303439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200930539/1000000000 : ℝ)^2141 ≤ (12133637711027/100000000000000 : ℝ)^1629 := by
    have hnat : (200930539 : ℕ)^2141*100000000000000^1629 ≤ 12133637711027^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200930539 1000000000 12133637711027 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631009937/1250000000 : ℝ)^2141 ≤ (8144187718471/20000000000000 : ℝ)^1629 := by
    have hnat : (631009937 : ℕ)^2141*20000000000000^1629 ≤ 8144187718471^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631009937 1250000000 8144187718471 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643303439/10000000000 : ℝ)^2141 ≤ (23572711837891/50000000000000 : ℝ)^1629 := by
    have hnat : (5643303439 : ℕ)^2141*50000000000000^1629 ≤ 23572711837891^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643303439 10000000000 23572711837891 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200930539/1000000000 : ℝ), (631009937/1250000000 : ℝ), (5643303439/10000000000 : ℝ)] ![(12133637711027/100000000000000 : ℝ), (8144187718471/20000000000000 : ℝ), (23572711837891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200930539/1000000000 : ℝ)|^2141 ≤ (12133637711027/100000000000000 : ℝ)^1629
        have hw : |(-200930539/1000000000 : ℝ)|=(200930539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(631009937/1250000000 : ℝ)|^2141 ≤ (8144187718471/20000000000000 : ℝ)^1629
        have hw : |(631009937/1250000000 : ℝ)|=(631009937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5643303439/10000000000 : ℝ)|^2141 ≤ (23572711837891/50000000000000 : ℝ)^1629
        have hw : |(5643303439/10000000000 : ℝ)|=(5643303439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624776883/5000000000 : ℝ)*x 0 + (-216537271/1250000000 : ℝ)*x 1 + (5643303039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624776883/5000000000 : ℝ)^2141 ≤ (8574048578557/20000000000000 : ℝ)^1629 := by
    have hnat : (2624776883 : ℕ)^2141*20000000000000^1629 ≤ 8574048578557^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624776883 5000000000 8574048578557 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216537271/1250000000 : ℝ)^2141 ≤ (4992168906101/50000000000000 : ℝ)^1629 := by
    have hnat : (216537271 : ℕ)^2141*50000000000000^1629 ≤ 4992168906101^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216537271 1250000000 4992168906101 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643303039/10000000000 : ℝ)^2141 ≤ (11786354820947/25000000000000 : ℝ)^1629 := by
    have hnat : (5643303039 : ℕ)^2141*25000000000000^1629 ≤ 11786354820947^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643303039 10000000000 11786354820947 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624776883/5000000000 : ℝ), (-216537271/1250000000 : ℝ), (5643303039/10000000000 : ℝ)] ![(8574048578557/20000000000000 : ℝ), (4992168906101/50000000000000 : ℝ), (11786354820947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624776883/5000000000 : ℝ)|^2141 ≤ (8574048578557/20000000000000 : ℝ)^1629
        have hw : |(2624776883/5000000000 : ℝ)|=(2624776883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216537271/1250000000 : ℝ)|^2141 ≤ (4992168906101/50000000000000 : ℝ)^1629
        have hw : |(-216537271/1250000000 : ℝ)|=(216537271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5643303039/10000000000 : ℝ)|^2141 ≤ (11786354820947/25000000000000 : ℝ)^1629
        have hw : |(5643303039/10000000000 : ℝ)|=(5643303039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624776777/5000000000 : ℝ)*x 0 + (5643302877/10000000000 : ℝ)*x 1 + (-108268669/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624776777/5000000000 : ℝ)^2141 ≤ (42870240617347/100000000000000 : ℝ)^1629 := by
    have hnat : (2624776777 : ℕ)^2141*100000000000000^1629 ≤ 42870240617347^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624776777 5000000000 42870240617347 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5643302877/10000000000 : ℝ)^2141 ≤ (4714541750503/10000000000000 : ℝ)^1629 := by
    have hnat : (5643302877 : ℕ)^2141*10000000000000^1629 ≤ 4714541750503^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643302877 10000000000 4714541750503 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108268669/625000000 : ℝ)^2141 ≤ (2496085468123/25000000000000 : ℝ)^1629 := by
    have hnat : (108268669 : ℕ)^2141*25000000000000^1629 ≤ 2496085468123^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108268669 625000000 2496085468123 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624776777/5000000000 : ℝ), (5643302877/10000000000 : ℝ), (-108268669/625000000 : ℝ)] ![(42870240617347/100000000000000 : ℝ), (4714541750503/10000000000000 : ℝ), (2496085468123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624776777/5000000000 : ℝ)|^2141 ≤ (42870240617347/100000000000000 : ℝ)^1629
        have hw : |(2624776777/5000000000 : ℝ)|=(2624776777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5643302877/10000000000 : ℝ)|^2141 ≤ (4714541750503/10000000000000 : ℝ)^1629
        have hw : |(5643302877/10000000000 : ℝ)|=(5643302877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108268669/625000000 : ℝ)|^2141 ≤ (2496085468123/25000000000000 : ℝ)^1629
        have hw : |(-108268669/625000000 : ℝ)|=(108268669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s1_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297051953/10000000000 : ℝ)*x 0 + (2479283361/5000000000 : ℝ)*x 1 + (3721203733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297051953/10000000000 : ℝ)^2141 ≤ (32951480493857/100000000000000 : ℝ)^1629 := by
    have hnat : (4297051953 : ℕ)^2141*100000000000000^1629 ≤ 32951480493857^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297051953 10000000000 32951480493857 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2479283361/5000000000 : ℝ)^2141 ≤ (19887290430351/50000000000000 : ℝ)^1629 := by
    have hnat : (2479283361 : ℕ)^2141*50000000000000^1629 ≤ 19887290430351^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479283361 5000000000 19887290430351 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3721203733/10000000000 : ℝ)^2141 ≤ (27273938624343/100000000000000 : ℝ)^1629 := by
    have hnat : (3721203733 : ℕ)^2141*100000000000000^1629 ≤ 27273938624343^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721203733 10000000000 27273938624343 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297051953/10000000000 : ℝ), (2479283361/5000000000 : ℝ), (3721203733/10000000000 : ℝ)] ![(32951480493857/100000000000000 : ℝ), (19887290430351/50000000000000 : ℝ), (27273938624343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297051953/10000000000 : ℝ)|^2141 ≤ (32951480493857/100000000000000 : ℝ)^1629
        have hw : |(4297051953/10000000000 : ℝ)|=(4297051953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2479283361/5000000000 : ℝ)|^2141 ≤ (19887290430351/50000000000000 : ℝ)^1629
        have hw : |(2479283361/5000000000 : ℝ)|=(2479283361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3721203733/10000000000 : ℝ)|^2141 ≤ (27273938624343/100000000000000 : ℝ)^1629
        have hw : |(3721203733/10000000000 : ℝ)|=(3721203733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3377/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6701/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9807/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3377/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3377/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3377/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3377/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3377/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3377/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1263/100000 : ℝ) ^ (4281/1024 : ℝ) ≤ (577530896413/50000000000000000000 : ℝ) := by
    have hpowers : (1263/100000 : ℝ)^4281 ≤ (577530896413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1263 : ℕ)^4281*50000000000000000000^1024 ≤ 577530896413^1024*100000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1263 100000 577530896413 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1263/100000 : ℝ)) (X := (577530896413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3377/12500 : ℝ) ^ (4281/1024 : ℝ) ≤ (420531507420045557/100000000000000000000 : ℝ) := by
    have hpowers : (3377/12500 : ℝ)^4281 ≤ (420531507420045557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3377 : ℕ)^4281*100000000000000000000^1024 ≤ 420531507420045557^1024*12500^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3377 12500 420531507420045557 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3377/12500 : ℝ)) (X := (420531507420045557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000577530896413/25000000000000000000 : ℝ) ≤ (1250000006907167/1250000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25000000577530896413/25000000000000000000 : ℝ)^1024 ≤ (1250000006907167/1250000000000000 : ℝ)^4281 := by
      have hnat : (25000000577530896413 : ℕ)^1024*1250000000000000^4281 ≤ 1250000006907167^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000577530896413 25000000000000000000 1250000006907167 1250000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000006907167/1250000000000000 : ℝ)) (X := (25000000577530896413/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100420532662481838383/100000000000000000000 : ℝ) ≤ (2502510735017241/2500000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (100420532662481838383/100000000000000000000 : ℝ)^1024 ≤ (2502510735017241/2500000000000000 : ℝ)^4281 := by
      have hnat : (100420532662481838383 : ℕ)^1024*2500000000000000^4281 ≤ 2502510735017241^4281*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100420532662481838383 100000000000000000000 2502510735017241 2500000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502510735017241/2500000000000000 : ℝ)) (X := (100420532662481838383/100000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50420531507420045557/50000000000000000000 : ℝ) ≤ (626255364055037/625000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50420531507420045557/50000000000000000000 : ℝ)^1024 ≤ (626255364055037/625000000000000 : ℝ)^4281 := by
      have hnat : (50420531507420045557 : ℕ)^1024*625000000000000^4281 ≤ 626255364055037^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50420531507420045557 50000000000000000000 626255364055037 625000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626255364055037/625000000000000 : ℝ)) (X := (50420531507420045557/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(577530896413/50000000000000000000 : ℝ) ≤ ((3218807913700100021/3219125000000000000 : ℝ)+2*(2510721202907/643825000000000 : ℝ)*(1263/100000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (3218807913700100021/3219125000000000000 : ℝ)+2*(2510721202907/643825000000000 : ℝ)*(1263/100000 : ℝ)=(1250000006907167/1250000000000000 : ℝ) by norm_num, show 1+2*(577530896413/50000000000000000000 : ℝ)=(25000000577530896413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(420531507420045557/100000000000000000000 : ℝ)+(577530896413/50000000000000000000 : ℝ) ≤ ((3218807913700100021/3219125000000000000 : ℝ)+(2510721202907/643825000000000 : ℝ)*((3377/12500 : ℝ)+(1263/100000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (3218807913700100021/3219125000000000000 : ℝ)+(2510721202907/643825000000000 : ℝ)*((3377/12500 : ℝ)+(1263/100000 : ℝ))=(2502510735017241/2500000000000000 : ℝ) by norm_num, show 1+(420531507420045557/100000000000000000000 : ℝ)+(577530896413/50000000000000000000 : ℝ)=(100420532662481838383/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(420531507420045557/100000000000000000000 : ℝ) ≤ ((3218807913700100021/3219125000000000000 : ℝ)+2*(2510721202907/643825000000000 : ℝ)*(3377/12500 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (3218807913700100021/3219125000000000000 : ℝ)+2*(2510721202907/643825000000000 : ℝ)*(3377/12500 : ℝ)=(626255364055037/625000000000000 : ℝ) by norm_num, show 1+2*(420531507420045557/100000000000000000000 : ℝ)=(50420531507420045557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3218807913700100021/3219125000000000000 : ℝ)*(X 1 0+X 2 0)+(2510721202907/643825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (1263/100000 : ℝ)) (hi := (3377/12500 : ℝ)) (c := (3218807913700100021/3219125000000000000 : ℝ)) (alpha := (2510721202907/643825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3218807913700100021/3219125000000000000 : ℝ)*(X 0 1+X 2 1)+(2510721202907/643825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (1263/100000 : ℝ)) (hi := (3377/12500 : ℝ)) (c := (3218807913700100021/3219125000000000000 : ℝ)) (alpha := (2510721202907/643825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3218807913700100021/3219125000000000000 : ℝ)*(X 0 2+X 1 2)+(2510721202907/643825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (1263/100000 : ℝ)) (hi := (3377/12500 : ℝ)) (c := (3218807913700100021/3219125000000000000 : ℝ)) (alpha := (2510721202907/643825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-200873059/1000000000 : ℝ)*X 0 0+(353201979/625000000 : ℝ)*X 0 1+(2520147591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5407814553/10000000000 : ℝ)*X 1 0+(-2335305961/10000000000 : ℝ)*X 1 1+(2520147669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((108156291/200000000 : ℝ)*X 2 0+(5040295027/10000000000 : ℝ)*X 2 1+(-58382659/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107396443/250000000 : ℝ)*X 0 0+(1852360979/5000000000 : ℝ)*X 0 1+(4974749357/10000000000 : ℝ)*X 0 2+(107396443/250000000 : ℝ)*X 1 0+(1852360979/5000000000 : ℝ)*X 1 1+(4974749357/10000000000 : ℝ)*X 1 2+(107396443/250000000 : ℝ)*X 2 0+(1852360979/5000000000 : ℝ)*X 2 1+(4974749357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200930539/1000000000 : ℝ)*X 0 0+(631009937/1250000000 : ℝ)*X 0 1+(5643303439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2624776883/5000000000 : ℝ)*X 1 0+(-216537271/1250000000 : ℝ)*X 1 1+(5643303039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624776777/5000000000 : ℝ)*X 2 0+(5643302877/10000000000 : ℝ)*X 2 1+(-108268669/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297051953/10000000000 : ℝ)*X 0 0+(2479283361/5000000000 : ℝ)*X 0 1+(3721203733/10000000000 : ℝ)*X 0 2+(4297051953/10000000000 : ℝ)*X 1 0+(2479283361/5000000000 : ℝ)*X 1 1+(3721203733/10000000000 : ℝ)*X 1 2+(4297051953/10000000000 : ℝ)*X 2 0+(2479283361/5000000000 : ℝ)*X 2 1+(3721203733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163725930653091555912943071/20119531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (18160481/20000000000000 : ℝ)*(base1) + (42729227/3125000000000 : ℝ)*(base19) + (1366427219/100000000000000 : ℝ)*(base23) + (243352073/100000000000000 : ℝ)*(upper3) + (8320953/10000000000000 : ℝ)*(upper5) + (606059632815981/50000000000000 : ℝ)*(major0) + (606059632815981/50000000000000 : ℝ)*(major1) + (606059632815981/50000000000000 : ℝ)*(major2) + (102302490678623/6250000000000 : ℝ)*(sp0) + (818422633904711/50000000000000 : ℝ)*(sp1) + (1636845268717467/100000000000000 : ℝ)*(sp2) + (393693819148509/50000000000000 : ℝ)*(sp3) + (3437544561/50000000000000 : ℝ)*(sp4) + (3895764433/100000000000000 : ℝ)*(sp7) + (157478324972771/20000000000000 : ℝ)*(f.failure) + (818423317572343/50000000000000 : ℝ)*(f.sum) + (150824665598249/128765000000000000000000000000 : ℝ)*base66 + (68913948752178223/12381250000000000000000000000000 : ℝ)*base68 + (62645141296646973/12381250000000000000000000000000 : ℝ)*base70 + (44313938308559473/12381250000000000000000000000000 : ℝ)*base72 + (81302457094473/16095625000000000000000000000 : ℝ)*base74 + (73643082545784473/12381250000000000000000000000000 : ℝ)*base76 + (83434063713584473/12381250000000000000000000000000 : ℝ)*base78 + (85244759867459473/12381250000000000000000000000000 : ℝ)*base80 + (159000958012539/128765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (498517/500000000000000000000 : ℝ)*base90 + (498517/500000000000000000000 : ℝ)*base92 + (498517/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1362832697600787503875670019/160956250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7954171/100000000000000 : ℝ)*(base1) + (1524874761/100000000000000 : ℝ)*(base19) + (278347211/20000000000000 : ℝ)*(base23) + (70245247/50000000000000 : ℝ)*(upper3) + (28326799/12500000000000 : ℝ)*(upper5) + (1244105320878029/100000000000000 : ℝ)*(major0) + (1244105320878029/100000000000000 : ℝ)*(major1) + (1244105320878029/100000000000000 : ℝ)*(major2) + (749842537/10000000000000 : ℝ)*(sp1) + (2666343083/50000000000000 : ℝ)*(sp2) + (840020314416103/50000000000000 : ℝ)*(sp4) + (105001974848619/6250000000000 : ℝ)*(sp5) + (840016948227907/50000000000000 : ℝ)*(sp6) + (808169730687171/100000000000000 : ℝ)*(sp7) + (808169738641343/100000000000000 : ℝ)*(f.failure) + (840020310439017/50000000000000 : ℝ)*(f.sum) + (338764040640617/128765000000000000000000000000 : ℝ)*base65 + (104659132928859893/24762500000000000000000000000000 : ℝ)*base67 + (120224985561872393/24762500000000000000000000000000 : ℝ)*base69 + (109264477561122393/24762500000000000000000000000000 : ℝ)*base71 + (52996954712557/8047812500000000000000000000 : ℝ)*base73 + (2340160496347393/24762500000000000000000000000000 : ℝ)*base75 + (45521291279347393/24762500000000000000000000000000 : ℝ)*base77 + (36363534310059893/24762500000000000000000000000000 : ℝ)*base79 + (596947664142057/128765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9441639/2500000000000000000000 : ℝ)*base89 + (9441639/2500000000000000000000 : ℝ)*base91 + (9441639/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1322_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3377/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6701/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9807/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_s2_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-512664473/2500000000 : ℝ)*x 0 + (685669451/1250000000 : ℝ)*x 1 + (323709059/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512664473/2500000000 : ℝ)^2141 ≤ (12462897179721/100000000000000 : ℝ)^1629 := by
    have hnat : (512664473 : ℕ)^2141*100000000000000^1629 ≤ 12462897179721^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512664473 2500000000 12462897179721 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685669451/1250000000 : ℝ)^2141 ≤ (22709418202877/50000000000000 : ℝ)^1629 := by
    have hnat : (685669451 : ℕ)^2141*50000000000000^1629 ≤ 22709418202877^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685669451 1250000000 22709418202877 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323709059/625000000 : ℝ)^2141 ≤ (8423653281839/20000000000000 : ℝ)^1629 := by
    have hnat : (323709059 : ℕ)^2141*20000000000000^1629 ≤ 8423653281839^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323709059 625000000 8423653281839 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512664473/2500000000 : ℝ), (685669451/1250000000 : ℝ), (323709059/625000000 : ℝ)] ![(12462897179721/100000000000000 : ℝ), (22709418202877/50000000000000 : ℝ), (8423653281839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512664473/2500000000 : ℝ)|^2141 ≤ (12462897179721/100000000000000 : ℝ)^1629
        have hw : |(-512664473/2500000000 : ℝ)|=(512664473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685669451/1250000000 : ℝ)|^2141 ≤ (22709418202877/50000000000000 : ℝ)^1629
        have hw : |(685669451/1250000000 : ℝ)|=(685669451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323709059/625000000 : ℝ)|^2141 ≤ (8423653281839/20000000000000 : ℝ)^1629
        have hw : |(323709059/625000000 : ℝ)|=(323709059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073476061/2000000000 : ℝ)*x 0 + (-276119367/1250000000 : ℝ)*x 1 + (1294836117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073476061/2000000000 : ℝ)^2141 ≤ (22069668289881/50000000000000 : ℝ)^1629 := by
    have hnat : (1073476061 : ℕ)^2141*50000000000000^1629 ≤ 22069668289881^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073476061 2000000000 22069668289881 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276119367/1250000000 : ℝ)^2141 ≤ (13742402084039/100000000000000 : ℝ)^1629 := by
    have hnat : (276119367 : ℕ)^2141*100000000000000^1629 ≤ 13742402084039^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276119367 1250000000 13742402084039 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294836117/2500000000 : ℝ)^2141 ≤ (5264782665221/12500000000000 : ℝ)^1629 := by
    have hnat : (1294836117 : ℕ)^2141*12500000000000^1629 ≤ 5264782665221^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294836117 2500000000 5264782665221 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073476061/2000000000 : ℝ), (-276119367/1250000000 : ℝ), (1294836117/2500000000 : ℝ)] ![(22069668289881/50000000000000 : ℝ), (13742402084039/100000000000000 : ℝ), (5264782665221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073476061/2000000000 : ℝ)|^2141 ≤ (22069668289881/50000000000000 : ℝ)^1629
        have hw : |(1073476061/2000000000 : ℝ)|=(1073476061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276119367/1250000000 : ℝ)|^2141 ≤ (13742402084039/100000000000000 : ℝ)^1629
        have hw : |(-276119367/1250000000 : ℝ)|=(276119367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294836117/2500000000 : ℝ)|^2141 ≤ (5264782665221/12500000000000 : ℝ)^1629
        have hw : |(1294836117/2500000000 : ℝ)|=(1294836117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335461227/625000000 : ℝ)*x 0 + (5179345133/10000000000 : ℝ)*x 1 + (-2208954957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335461227/625000000 : ℝ)^2141 ≤ (44139329305749/100000000000000 : ℝ)^1629 := by
    have hnat : (335461227 : ℕ)^2141*100000000000000^1629 ≤ 44139329305749^1629*625000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335461227 625000000 44139329305749 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179345133/10000000000 : ℝ)^2141 ≤ (42118268429203/100000000000000 : ℝ)^1629 := by
    have hnat : (5179345133 : ℕ)^2141*100000000000000^1629 ≤ 42118268429203^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179345133 10000000000 42118268429203 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208954957/10000000000 : ℝ)^2141 ≤ (13742402255747/100000000000000 : ℝ)^1629 := by
    have hnat : (2208954957 : ℕ)^2141*100000000000000^1629 ≤ 13742402255747^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208954957 10000000000 13742402255747 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335461227/625000000 : ℝ), (5179345133/10000000000 : ℝ), (-2208954957/10000000000 : ℝ)] ![(44139329305749/100000000000000 : ℝ), (42118268429203/100000000000000 : ℝ), (13742402255747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335461227/625000000 : ℝ)|^2141 ≤ (44139329305749/100000000000000 : ℝ)^1629
        have hw : |(335461227/625000000 : ℝ)|=(335461227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179345133/10000000000 : ℝ)|^2141 ≤ (42118268429203/100000000000000 : ℝ)^1629
        have hw : |(5179345133/10000000000 : ℝ)|=(5179345133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208954957/10000000000 : ℝ)|^2141 ≤ (13742402255747/100000000000000 : ℝ)^1629
        have hw : |(-2208954957/10000000000 : ℝ)|=(2208954957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (432510979/1000000000 : ℝ)*x 0 + (803606013/2000000000 : ℝ)*x 1 + (2327090159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432510979/1000000000 : ℝ)^2141 ≤ (33234553756151/100000000000000 : ℝ)^1629 := by
    have hnat : (432510979 : ℕ)^2141*100000000000000^1629 ≤ 33234553756151^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432510979 1000000000 33234553756151 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803606013/2000000000 : ℝ)^2141 ≤ (30168466624107/100000000000000 : ℝ)^1629 := by
    have hnat : (803606013 : ℕ)^2141*100000000000000^1629 ≤ 30168466624107^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803606013 2000000000 30168466624107 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2327090159/5000000000 : ℝ)^2141 ≤ (2287311225191/6250000000000 : ℝ)^1629 := by
    have hnat : (2327090159 : ℕ)^2141*6250000000000^1629 ≤ 2287311225191^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327090159 5000000000 2287311225191 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432510979/1000000000 : ℝ), (803606013/2000000000 : ℝ), (2327090159/5000000000 : ℝ)] ![(33234553756151/100000000000000 : ℝ), (30168466624107/100000000000000 : ℝ), (2287311225191/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432510979/1000000000 : ℝ)|^2141 ≤ (33234553756151/100000000000000 : ℝ)^1629
        have hw : |(432510979/1000000000 : ℝ)|=(432510979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803606013/2000000000 : ℝ)|^2141 ≤ (30168466624107/100000000000000 : ℝ)^1629
        have hw : |(803606013/2000000000 : ℝ)|=(803606013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2327090159/5000000000 : ℝ)|^2141 ≤ (2287311225191/6250000000000 : ℝ)^1629
        have hw : |(2327090159/5000000000 : ℝ)|=(2327090159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-82029189/400000000 : ℝ)*x 0 + (1036261423/2000000000 : ℝ)*x 1 + (5483375567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82029189/400000000 : ℝ)^2141 ≤ (12463470962853/100000000000000 : ℝ)^1629 := by
    have hnat : (82029189 : ℕ)^2141*100000000000000^1629 ≤ 12463470962853^1629*400000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82029189 400000000 12463470962853 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036261423/2000000000 : ℝ)^2141 ≤ (4213923908967/10000000000000 : ℝ)^1629 := by
    have hnat : (1036261423 : ℕ)^2141*10000000000000^1629 ≤ 4213923908967^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036261423 2000000000 4213923908967 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483375567/10000000000 : ℝ)^2141 ≤ (9079457985023/20000000000000 : ℝ)^1629 := by
    have hnat : (5483375567 : ℕ)^2141*20000000000000^1629 ≤ 9079457985023^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483375567 10000000000 9079457985023 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82029189/400000000 : ℝ), (1036261423/2000000000 : ℝ), (5483375567/10000000000 : ℝ)] ![(12463470962853/100000000000000 : ℝ), (4213923908967/10000000000000 : ℝ), (9079457985023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82029189/400000000 : ℝ)|^2141 ≤ (12463470962853/100000000000000 : ℝ)^1629
        have hw : |(-82029189/400000000 : ℝ)|=(82029189/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036261423/2000000000 : ℝ)|^2141 ≤ (4213923908967/10000000000000 : ℝ)^1629
        have hw : |(1036261423/2000000000 : ℝ)|=(1036261423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483375567/10000000000 : ℝ)|^2141 ≤ (9079457985023/20000000000000 : ℝ)^1629
        have hw : |(5483375567/10000000000 : ℝ)|=(5483375567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288679349/10000000000 : ℝ)*x 0 + (-238115417/1250000000 : ℝ)*x 1 + (2741687813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288679349/10000000000 : ℝ)^2141 ≤ (10822669137809/25000000000000 : ℝ)^1629 := by
    have hnat : (5288679349 : ℕ)^2141*25000000000000^1629 ≤ 10822669137809^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288679349 10000000000 10822669137809 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238115417/1250000000 : ℝ)^2141 ≤ (2262406572237/20000000000000 : ℝ)^1629 := by
    have hnat : (238115417 : ℕ)^2141*20000000000000^1629 ≤ 2262406572237^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238115417 1250000000 2262406572237 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741687813/5000000000 : ℝ)^2141 ≤ (22698645283553/50000000000000 : ℝ)^1629 := by
    have hnat : (2741687813 : ℕ)^2141*50000000000000^1629 ≤ 22698645283553^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741687813 5000000000 22698645283553 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288679349/10000000000 : ℝ), (-238115417/1250000000 : ℝ), (2741687813/5000000000 : ℝ)] ![(10822669137809/25000000000000 : ℝ), (2262406572237/20000000000000 : ℝ), (22698645283553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288679349/10000000000 : ℝ)|^2141 ≤ (10822669137809/25000000000000 : ℝ)^1629
        have hw : |(5288679349/10000000000 : ℝ)|=(5288679349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238115417/1250000000 : ℝ)|^2141 ≤ (2262406572237/20000000000000 : ℝ)^1629
        have hw : |(-238115417/1250000000 : ℝ)|=(238115417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741687813/5000000000 : ℝ)|^2141 ≤ (22698645283553/50000000000000 : ℝ)^1629
        have hw : |(2741687813/5000000000 : ℝ)|=(2741687813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661084929/1250000000 : ℝ)*x 0 + (2741687787/5000000000 : ℝ)*x 1 + (-952461647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661084929/1250000000 : ℝ)^2141 ≤ (43290677444173/100000000000000 : ℝ)^1629 := by
    have hnat : (661084929 : ℕ)^2141*100000000000000^1629 ≤ 43290677444173^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661084929 1250000000 43290677444173 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741687787/5000000000 : ℝ)^2141 ≤ (45397290001283/100000000000000 : ℝ)^1629 := by
    have hnat : (2741687787 : ℕ)^2141*100000000000000^1629 ≤ 45397290001283^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741687787 5000000000 45397290001283 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952461647/5000000000 : ℝ)^2141 ≤ (5656016266693/50000000000000 : ℝ)^1629 := by
    have hnat : (952461647 : ℕ)^2141*50000000000000^1629 ≤ 5656016266693^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952461647 5000000000 5656016266693 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661084929/1250000000 : ℝ), (2741687787/5000000000 : ℝ), (-952461647/5000000000 : ℝ)] ![(43290677444173/100000000000000 : ℝ), (45397290001283/100000000000000 : ℝ), (5656016266693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661084929/1250000000 : ℝ)|^2141 ≤ (43290677444173/100000000000000 : ℝ)^1629
        have hw : |(661084929/1250000000 : ℝ)|=(661084929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741687787/5000000000 : ℝ)|^2141 ≤ (45397290001283/100000000000000 : ℝ)^1629
        have hw : |(2741687787/5000000000 : ℝ)|=(2741687787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952461647/5000000000 : ℝ)|^2141 ≤ (5656016266693/50000000000000 : ℝ)^1629
        have hw : |(-952461647/5000000000 : ℝ)|=(952461647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s2_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081314377/2500000000 : ℝ)*x 0 + (2325049531/5000000000 : ℝ)*x 1 + (4022151843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081314377/2500000000 : ℝ)^2141 ≤ (16618022801169/50000000000000 : ℝ)^1629 := by
    have hnat : (1081314377 : ℕ)^2141*50000000000000^1629 ≤ 16618022801169^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081314377 2500000000 16618022801169 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2325049531/5000000000 : ℝ)^2141 ≤ (36554806884839/100000000000000 : ℝ)^1629 := by
    have hnat : (2325049531 : ℕ)^2141*100000000000000^1629 ≤ 36554806884839^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325049531 5000000000 36554806884839 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022151843/10000000000 : ℝ)^2141 ≤ (30209147493427/100000000000000 : ℝ)^1629 := by
    have hnat : (4022151843 : ℕ)^2141*100000000000000^1629 ≤ 30209147493427^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022151843 10000000000 30209147493427 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081314377/2500000000 : ℝ), (2325049531/5000000000 : ℝ), (4022151843/10000000000 : ℝ)] ![(16618022801169/50000000000000 : ℝ), (36554806884839/100000000000000 : ℝ), (30209147493427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081314377/2500000000 : ℝ)|^2141 ≤ (16618022801169/50000000000000 : ℝ)^1629
        have hw : |(1081314377/2500000000 : ℝ)|=(1081314377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2325049531/5000000000 : ℝ)|^2141 ≤ (36554806884839/100000000000000 : ℝ)^1629
        have hw : |(2325049531/5000000000 : ℝ)|=(2325049531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022151843/10000000000 : ℝ)|^2141 ≤ (30209147493427/100000000000000 : ℝ)^1629
        have hw : |(4022151843/10000000000 : ℝ)|=(4022151843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9807/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4859/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8093/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9807/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9807/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9807/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9807/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9807/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9807/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6701/100000 : ℝ) ^ (4281/1024 : ℝ) ≤ (618662925121619/50000000000000000000 : ℝ) := by
    have hpowers : (6701/100000 : ℝ)^4281 ≤ (618662925121619/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6701 : ℕ)^4281*50000000000000000000^1024 ≤ 618662925121619^1024*100000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6701 100000 618662925121619 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6701/100000 : ℝ)) (X := (618662925121619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9807/50000 : ℝ) ^ (4281/1024 : ℝ) ≤ (55134928878186017/50000000000000000000 : ℝ) := by
    have hpowers : (9807/50000 : ℝ)^4281 ≤ (55134928878186017/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9807 : ℕ)^4281*50000000000000000000^1024 ≤ 55134928878186017^1024*50000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9807 50000 55134928878186017 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9807/50000 : ℝ)) (X := (55134928878186017/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000618662925121619/25000000000000000000 : ℝ) ≤ (10000059192232823/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25000618662925121619/25000000000000000000 : ℝ)^1024 ≤ (10000059192232823/10000000000000000 : ℝ)^4281 := by
      have hnat : (25000618662925121619 : ℕ)^1024*10000000000000000^4281 ≤ 10000059192232823^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000618662925121619 25000000000000000000 10000059192232823 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059192232823/10000000000000000 : ℝ)) (X := (25000618662925121619/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12513938397950826909/12500000000000000000 : ℝ) ≤ (10002666081614751/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (12513938397950826909/12500000000000000000 : ℝ)^1024 ≤ (10002666081614751/10000000000000000 : ℝ)^4281 := by
      have hnat : (12513938397950826909 : ℕ)^1024*10000000000000000^4281 ≤ 10002666081614751^4281*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513938397950826909 12500000000000000000 10002666081614751 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002666081614751/10000000000000000 : ℝ)) (X := (12513938397950826909/12500000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25055134928878186017/25000000000000000000 : ℝ) ≤ (10005272970996679/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25055134928878186017/25000000000000000000 : ℝ)^1024 ≤ (10005272970996679/10000000000000000 : ℝ)^4281 := by
      have hnat : (25055134928878186017 : ℕ)^1024*10000000000000000^4281 ≤ 10005272970996679^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25055134928878186017 25000000000000000000 10005272970996679 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005272970996679/10000000000000000 : ℝ)) (X := (25055134928878186017/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(618662925121619/50000000000000000000 : ℝ) ≤ ((129095826817805844343/129130000000000000000 : ℝ)+2*(325861172741/161412500000000 : ℝ)*(6701/100000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (129095826817805844343/129130000000000000000 : ℝ)+2*(325861172741/161412500000000 : ℝ)*(6701/100000 : ℝ)=(10000059192232823/10000000000000000 : ℝ) by norm_num, show 1+2*(618662925121619/50000000000000000000 : ℝ)=(25000618662925121619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55134928878186017/50000000000000000000 : ℝ)+(618662925121619/50000000000000000000 : ℝ) ≤ ((129095826817805844343/129130000000000000000 : ℝ)+(325861172741/161412500000000 : ℝ)*((9807/50000 : ℝ)+(6701/100000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (129095826817805844343/129130000000000000000 : ℝ)+(325861172741/161412500000000 : ℝ)*((9807/50000 : ℝ)+(6701/100000 : ℝ))=(10002666081614751/10000000000000000 : ℝ) by norm_num, show 1+(55134928878186017/50000000000000000000 : ℝ)+(618662925121619/50000000000000000000 : ℝ)=(12513938397950826909/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55134928878186017/50000000000000000000 : ℝ) ≤ ((129095826817805844343/129130000000000000000 : ℝ)+2*(325861172741/161412500000000 : ℝ)*(9807/50000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (129095826817805844343/129130000000000000000 : ℝ)+2*(325861172741/161412500000000 : ℝ)*(9807/50000 : ℝ)=(10005272970996679/10000000000000000 : ℝ) by norm_num, show 1+2*(55134928878186017/50000000000000000000 : ℝ)=(25055134928878186017/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129095826817805844343/129130000000000000000 : ℝ)*(X 1 0+X 2 0)+(325861172741/161412500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (6701/100000 : ℝ)) (hi := (9807/50000 : ℝ)) (c := (129095826817805844343/129130000000000000000 : ℝ)) (alpha := (325861172741/161412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129095826817805844343/129130000000000000000 : ℝ)*(X 0 1+X 2 1)+(325861172741/161412500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (6701/100000 : ℝ)) (hi := (9807/50000 : ℝ)) (c := (129095826817805844343/129130000000000000000 : ℝ)) (alpha := (325861172741/161412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129095826817805844343/129130000000000000000 : ℝ)*(X 0 2+X 1 2)+(325861172741/161412500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (6701/100000 : ℝ)) (hi := (9807/50000 : ℝ)) (c := (129095826817805844343/129130000000000000000 : ℝ)) (alpha := (325861172741/161412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-512664473/2500000000 : ℝ)*X 0 0+(685669451/1250000000 : ℝ)*X 0 1+(323709059/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073476061/2000000000 : ℝ)*X 1 0+(-276119367/1250000000 : ℝ)*X 1 1+(1294836117/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335461227/625000000 : ℝ)*X 2 0+(5179345133/10000000000 : ℝ)*X 2 1+(-2208954957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((432510979/1000000000 : ℝ)*X 0 0+(803606013/2000000000 : ℝ)*X 0 1+(2327090159/5000000000 : ℝ)*X 0 2+(432510979/1000000000 : ℝ)*X 1 0+(803606013/2000000000 : ℝ)*X 1 1+(2327090159/5000000000 : ℝ)*X 1 2+(432510979/1000000000 : ℝ)*X 2 0+(803606013/2000000000 : ℝ)*X 2 1+(2327090159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-82029189/400000000 : ℝ)*X 0 0+(1036261423/2000000000 : ℝ)*X 0 1+(5483375567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288679349/10000000000 : ℝ)*X 1 0+(-238115417/1250000000 : ℝ)*X 1 1+(2741687813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661084929/1250000000 : ℝ)*X 2 0+(2741687787/5000000000 : ℝ)*X 2 1+(-952461647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081314377/2500000000 : ℝ)*X 0 0+(2325049531/5000000000 : ℝ)*X 0 1+(4022151843/10000000000 : ℝ)*X 0 2+(1081314377/2500000000 : ℝ)*X 1 0+(2325049531/5000000000 : ℝ)*X 1 1+(4022151843/10000000000 : ℝ)*X 1 2+(1081314377/2500000000 : ℝ)*X 2 0+(2325049531/5000000000 : ℝ)*X 2 1+(4022151843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11521733376539261322273/32282500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28623233/5000000000000 : ℝ)*(base19) + (343511019/50000000000000 : ℝ)*(base23) + (120415517/100000000000000 : ℝ)*(upper3) + (287679243/100000000000000 : ℝ)*(lower4) + (103726091/20000000000000 : ℝ)*(upper5) + (151244750248167/6250000000000 : ℝ)*(major0) + (151244750248167/6250000000000 : ℝ)*(major1) + (151244750248167/6250000000000 : ℝ)*(major2) + (1633928328150913/50000000000000 : ℝ)*(sp0) + (1633928041918583/50000000000000 : ℝ)*(sp1) + (3267855173190899/100000000000000 : ℝ)*(sp2) + (1571968256110927/100000000000000 : ℝ)*(sp3) + (79608889/10000000000000 : ℝ)*(sp6) + (1416726361/20000000000000 : ℝ)*(sp7) + (392993834935683/25000000000000 : ℝ)*(f.failure) + (1633928328150913/50000000000000 : ℝ)*(f.sum) + (187343810781773/32282500000000000000000000000 : ℝ)*base65 + (4417130248098856781/807062500000000000000000000000000 : ℝ)*base67 + (2464166697984106781/807062500000000000000000000000000 : ℝ)*base69 + (2363894043785580719/807062500000000000000000000000000 : ℝ)*base72 + (127253279598831/64565000000000000000000000000 : ℝ)*base73 + (9159694443804606781/807062500000000000000000000000000 : ℝ)*base75 + (1324126385312705719/807062500000000000000000000000000 : ℝ)*base78 + (2995397603710330719/807062500000000000000000000000000 : ℝ)*base80 + (70585920076873/32282500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2303541/625000000000000000000 : ℝ)*base90 + (2303541/625000000000000000000 : ℝ)*base92 + (2303541/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53908984220478561633895835421/6456500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823754923/50000000000000 : ℝ)*(base19) + (482569683/25000000000000 : ℝ)*(base23) + (111895387/50000000000000 : ℝ)*(upper3) + (11192427/12500000000000 : ℝ)*(lower4) + (125413667/100000000000000 : ℝ)*(upper5) + (2451498304973049/100000000000000 : ℝ)*(major0) + (2451498304973049/100000000000000 : ℝ)*(major1) + (2451498304973049/100000000000000 : ℝ)*(major2) + (17756716871/100000000000000 : ℝ)*(sp1) + (1094519857/5000000000000 : ℝ)*(sp2) + (1655252578256933/50000000000000 : ℝ)*(sp4) + (827621438071787/25000000000000 : ℝ)*(sp5) + (1655240667918997/50000000000000 : ℝ)*(sp6) + (796245587556651/50000000000000 : ℝ)*(sp7) + (796245587556651/50000000000000 : ℝ)*(f.failure) + (1655252578256933/50000000000000 : ℝ)*(f.sum) + (115197109177341/32282500000000000000000000000 : ℝ)*base65 + (39695839637469311807/12913000000000000000000000000000000 : ℝ)*base67 + (109446060082952688193/12913000000000000000000000000000000 : ℝ)*base70 + (18234776155947688193/12913000000000000000000000000000000 : ℝ)*base72 + (48226829041343/16141250000000000000000000000 : ℝ)*base73 + (19458749568854688193/12913000000000000000000000000000000 : ℝ)*base76 + (82369251325400688193/12913000000000000000000000000000000 : ℝ)*base78 + (25298857197451311807/12913000000000000000000000000000000 : ℝ)*base79 + (163896589565289/32282500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4200723/1250000000000000000000 : ℝ)*base89 + (4200723/1250000000000000000000 : ℝ)*base91 + (4200723/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9807/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1322_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1322_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1322_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1322_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

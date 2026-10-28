-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:00.639742+00:00
-- url     : https://prove2.me/submissions/a246a18e-555c-4554-8242-2286417b7e04

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
theorem support_rectangle_w1203_s9_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069027941/5000000000 : ℝ)*x 0 + (539187153/1000000000 : ℝ)*x 1 + (5266718411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069027941/5000000000 : ℝ)^2099 ≤ (12997772433629/100000000000000 : ℝ)^1587 := by
    have hnat : (1069027941 : ℕ)^2099*100000000000000^1587 ≤ 12997772433629^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069027941 5000000000 12997772433629 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539187153/1000000000 : ℝ)^2099 ≤ (22088336053901/50000000000000 : ℝ)^1587 := by
    have hnat : (539187153 : ℕ)^2099*50000000000000^1587 ≤ 22088336053901^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539187153 1000000000 22088336053901 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266718411/10000000000 : ℝ)^2099 ≤ (42825555442227/100000000000000 : ℝ)^1587 := by
    have hnat : (5266718411 : ℕ)^2099*100000000000000^1587 ≤ 42825555442227^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266718411 10000000000 42825555442227 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069027941/5000000000 : ℝ), (539187153/1000000000 : ℝ), (5266718411/10000000000 : ℝ)] ![(12997772433629/100000000000000 : ℝ), (22088336053901/50000000000000 : ℝ), (42825555442227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069027941/5000000000 : ℝ)|^2099 ≤ (12997772433629/100000000000000 : ℝ)^1587
        have hw : |(-1069027941/5000000000 : ℝ)|=(1069027941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539187153/1000000000 : ℝ)|^2099 ≤ (22088336053901/50000000000000 : ℝ)^1587
        have hw : |(539187153/1000000000 : ℝ)|=(539187153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266718411/10000000000 : ℝ)|^2099 ≤ (42825555442227/100000000000000 : ℝ)^1587
        have hw : |(5266718411/10000000000 : ℝ)|=(5266718411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s9_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672245269/5000000000 : ℝ)*x 0 + (-2201520201/10000000000 : ℝ)*x 1 + (526671841/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672245269/5000000000 : ℝ)^2099 ≤ (10915989331529/25000000000000 : ℝ)^1587 := by
    have hnat : (2672245269 : ℕ)^2099*25000000000000^1587 ≤ 10915989331529^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672245269 5000000000 10915989331529 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201520201/10000000000 : ℝ)^2099 ≤ (6755243611151/50000000000000 : ℝ)^1587 := by
    have hnat : (2201520201 : ℕ)^2099*50000000000000^1587 ≤ 6755243611151^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201520201 10000000000 6755243611151 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526671841/1000000000 : ℝ)^2099 ≤ (42825555431473/100000000000000 : ℝ)^1587 := by
    have hnat : (526671841 : ℕ)^2099*100000000000000^1587 ≤ 42825555431473^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526671841 1000000000 42825555431473 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672245269/5000000000 : ℝ), (-2201520201/10000000000 : ℝ), (526671841/1000000000 : ℝ)] ![(10915989331529/25000000000000 : ℝ), (6755243611151/50000000000000 : ℝ), (42825555431473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672245269/5000000000 : ℝ)|^2099 ≤ (10915989331529/25000000000000 : ℝ)^1587
        have hw : |(2672245269/5000000000 : ℝ)|=(2672245269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201520201/10000000000 : ℝ)|^2099 ≤ (6755243611151/50000000000000 : ℝ)^1587
        have hw : |(-2201520201/10000000000 : ℝ)|=(2201520201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526671841/1000000000 : ℝ)|^2099 ≤ (42825555431473/100000000000000 : ℝ)^1587
        have hw : |(526671841/1000000000 : ℝ)|=(526671841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s9_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672245269/5000000000 : ℝ)*x 0 + (526671841/1000000000 : ℝ)*x 1 + (-2201520201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672245269/5000000000 : ℝ)^2099 ≤ (10915989331529/25000000000000 : ℝ)^1587 := by
    have hnat : (2672245269 : ℕ)^2099*25000000000000^1587 ≤ 10915989331529^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672245269 5000000000 10915989331529 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526671841/1000000000 : ℝ)^2099 ≤ (42825555431473/100000000000000 : ℝ)^1587 := by
    have hnat : (526671841 : ℕ)^2099*100000000000000^1587 ≤ 42825555431473^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526671841 1000000000 42825555431473 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201520201/10000000000 : ℝ)^2099 ≤ (6755243611151/50000000000000 : ℝ)^1587 := by
    have hnat : (2201520201 : ℕ)^2099*50000000000000^1587 ≤ 6755243611151^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201520201 10000000000 6755243611151 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672245269/5000000000 : ℝ), (526671841/1000000000 : ℝ), (-2201520201/10000000000 : ℝ)] ![(10915989331529/25000000000000 : ℝ), (42825555431473/100000000000000 : ℝ), (6755243611151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672245269/5000000000 : ℝ)|^2099 ≤ (10915989331529/25000000000000 : ℝ)^1587
        have hw : |(2672245269/5000000000 : ℝ)|=(2672245269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526671841/1000000000 : ℝ)|^2099 ≤ (42825555431473/100000000000000 : ℝ)^1587
        have hw : |(526671841/1000000000 : ℝ)|=(526671841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201520201/10000000000 : ℝ)|^2099 ≤ (6755243611151/50000000000000 : ℝ)^1587
        have hw : |(-2201520201/10000000000 : ℝ)|=(2201520201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s9_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356152243/10000000000 : ℝ)*x 0 + (52899423/125000000 : ℝ)*x 1 + (4483925307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356152243/10000000000 : ℝ)^2099 ≤ (6663463183357/20000000000000 : ℝ)^1587 := by
    have hnat : (4356152243 : ℕ)^2099*20000000000000^1587 ≤ 6663463183357^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356152243 10000000000 6663463183357 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52899423/125000000 : ℝ)^2099 ≤ (16033379560657/50000000000000 : ℝ)^1587 := by
    have hnat : (52899423 : ℕ)^2099*50000000000000^1587 ≤ 16033379560657^1587*125000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52899423 125000000 16033379560657 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483925307/10000000000 : ℝ)^2099 ≤ (4326990618087/12500000000000 : ℝ)^1587 := by
    have hnat : (4483925307 : ℕ)^2099*12500000000000^1587 ≤ 4326990618087^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483925307 10000000000 4326990618087 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356152243/10000000000 : ℝ), (52899423/125000000 : ℝ), (4483925307/10000000000 : ℝ)] ![(6663463183357/20000000000000 : ℝ), (16033379560657/50000000000000 : ℝ), (4326990618087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356152243/10000000000 : ℝ)|^2099 ≤ (6663463183357/20000000000000 : ℝ)^1587
        have hw : |(4356152243/10000000000 : ℝ)|=(4356152243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52899423/125000000 : ℝ)|^2099 ≤ (16033379560657/50000000000000 : ℝ)^1587
        have hw : |(52899423/125000000 : ℝ)|=(52899423/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483925307/10000000000 : ℝ)|^2099 ≤ (4326990618087/12500000000000 : ℝ)^1587
        have hw : |(4483925307/10000000000 : ℝ)|=(4483925307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s9_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-534515257/2500000000 : ℝ)*x 0 + (5267034353/10000000000 : ℝ)*x 1 + (5391554149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534515257/2500000000 : ℝ)^2099 ≤ (324945345257/2500000000000 : ℝ)^1587 := by
    have hnat : (534515257 : ℕ)^2099*2500000000000^1587 ≤ 324945345257^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534515257 2500000000 324945345257 2500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267034353/10000000000 : ℝ)^2099 ≤ (5353619167181/12500000000000 : ℝ)^1587 := by
    have hnat : (5267034353 : ℕ)^2099*12500000000000^1587 ≤ 5353619167181^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267034353 10000000000 5353619167181 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391554149/10000000000 : ℝ)^2099 ≤ (44173232841749/100000000000000 : ℝ)^1587 := by
    have hnat : (5391554149 : ℕ)^2099*100000000000000^1587 ≤ 44173232841749^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391554149 10000000000 44173232841749 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534515257/2500000000 : ℝ), (5267034353/10000000000 : ℝ), (5391554149/10000000000 : ℝ)] ![(324945345257/2500000000000 : ℝ), (5353619167181/12500000000000 : ℝ), (44173232841749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534515257/2500000000 : ℝ)|^2099 ≤ (324945345257/2500000000000 : ℝ)^1587
        have hw : |(-534515257/2500000000 : ℝ)|=(534515257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267034353/10000000000 : ℝ)|^2099 ≤ (5353619167181/12500000000000 : ℝ)^1587
        have hw : |(5267034353/10000000000 : ℝ)|=(5267034353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391554149/10000000000 : ℝ)|^2099 ≤ (44173232841749/100000000000000 : ℝ)^1587
        have hw : |(5391554149/10000000000 : ℝ)|=(5391554149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s9_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178080639/5000000000 : ℝ)*x 0 + (2241645999/5000000000 : ℝ)*x 1 + (4232589927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178080639/5000000000 : ℝ)^2099 ≤ (33317407313539/100000000000000 : ℝ)^1587 := by
    have hnat : (2178080639 : ℕ)^2099*100000000000000^1587 ≤ 33317407313539^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178080639 5000000000 33317407313539 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241645999/5000000000 : ℝ)^2099 ≤ (17304729300029/50000000000000 : ℝ)^1587 := by
    have hnat : (2241645999 : ℕ)^2099*50000000000000^1587 ≤ 17304729300029^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241645999 5000000000 17304729300029 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232589927/10000000000 : ℝ)^2099 ≤ (32073134070223/100000000000000 : ℝ)^1587 := by
    have hnat : (4232589927 : ℕ)^2099*100000000000000^1587 ≤ 32073134070223^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232589927 10000000000 32073134070223 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178080639/5000000000 : ℝ), (2241645999/5000000000 : ℝ), (4232589927/10000000000 : ℝ)] ![(33317407313539/100000000000000 : ℝ), (17304729300029/50000000000000 : ℝ), (32073134070223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178080639/5000000000 : ℝ)|^2099 ≤ (33317407313539/100000000000000 : ℝ)^1587
        have hw : |(2178080639/5000000000 : ℝ)|=(2178080639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241645999/5000000000 : ℝ)|^2099 ≤ (17304729300029/50000000000000 : ℝ)^1587
        have hw : |(2241645999/5000000000 : ℝ)|=(2241645999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232589927/10000000000 : ℝ)|^2099 ≤ (32073134070223/100000000000000 : ℝ)^1587
        have hw : |(4232589927/10000000000 : ℝ)|=(4232589927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1429/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11431/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (13771244124248861/100000000000000000000 : ℝ) := by
    have hpowers : (11431/100000 : ℝ)^8395 ≤ (13771244124248861/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11431 : ℕ)^8395*100000000000000000000^2048 ≤ 13771244124248861^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11431 100000 13771244124248861 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11431/100000 : ℝ)) (X := (13771244124248861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (32389068066475331/100000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^8395 ≤ (32389068066475331/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14083 : ℕ)^8395*100000000000000000000^2048 ≤ 32389068066475331^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 32389068066475331 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (32389068066475331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013771244124248861/50000000000000000000 : ℝ) ≤ (10000671842096003/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50013771244124248861/50000000000000000000 : ℝ)^2048 ≤ (10000671842096003/10000000000000000 : ℝ)^8395 := by
      have hnat : (50013771244124248861 : ℕ)^2048*10000000000000000^8395 ≤ 10000671842096003^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013771244124248861 50000000000000000000 10000671842096003 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000671842096003/10000000000000000 : ℝ)) (X := (50013771244124248861/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126442509755960131/3125000000000000000 : ℝ) ≤ (10001125906224807/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (3126442509755960131/3125000000000000000 : ℝ)^2048 ≤ (10001125906224807/10000000000000000 : ℝ)^8395 := by
      have hnat : (3126442509755960131 : ℕ)^2048*10000000000000000^8395 ≤ 10001125906224807^8395*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126442509755960131 3125000000000000000 10001125906224807 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001125906224807/10000000000000000 : ℝ)) (X := (3126442509755960131/3125000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032389068066475331/50000000000000000000 : ℝ) ≤ (10001579970353611/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50032389068066475331/50000000000000000000 : ℝ)^2048 ≤ (10001579970353611/10000000000000000 : ℝ)^8395 := by
      have hnat : (50032389068066475331 : ℕ)^2048*10000000000000000^8395 ≤ 10001579970353611^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032389068066475331 50000000000000000000 10001579970353611 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001579970353611/10000000000000000 : ℝ)) (X := (50032389068066475331/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13771244124248861/100000000000000000000 : ℝ) ≤ ((509834632906266979/510000000000000000 : ℝ)+2*(8732002477/5100000000000 : ℝ)*(11431/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (509834632906266979/510000000000000000 : ℝ)+2*(8732002477/5100000000000 : ℝ)*(11431/100000 : ℝ)=(10000671842096003/10000000000000000 : ℝ) by norm_num, show 1+2*(13771244124248861/100000000000000000000 : ℝ)=(50013771244124248861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32389068066475331/100000000000000000000 : ℝ)+(13771244124248861/100000000000000000000 : ℝ) ≤ ((509834632906266979/510000000000000000 : ℝ)+(8732002477/5100000000000 : ℝ)*((14083/100000 : ℝ)+(11431/100000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (509834632906266979/510000000000000000 : ℝ)+(8732002477/5100000000000 : ℝ)*((14083/100000 : ℝ)+(11431/100000 : ℝ))=(10001125906224807/10000000000000000 : ℝ) by norm_num, show 1+(32389068066475331/100000000000000000000 : ℝ)+(13771244124248861/100000000000000000000 : ℝ)=(3126442509755960131/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32389068066475331/100000000000000000000 : ℝ) ≤ ((509834632906266979/510000000000000000 : ℝ)+2*(8732002477/5100000000000 : ℝ)*(14083/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (509834632906266979/510000000000000000 : ℝ)+2*(8732002477/5100000000000 : ℝ)*(14083/100000 : ℝ)=(10001579970353611/10000000000000000 : ℝ) by norm_num, show 1+2*(32389068066475331/100000000000000000000 : ℝ)=(50032389068066475331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (509834632906266979/510000000000000000 : ℝ)*(X 1 0+X 2 0)+(8732002477/5100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (509834632906266979/510000000000000000 : ℝ)) (alpha := (8732002477/5100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (509834632906266979/510000000000000000 : ℝ)*(X 0 1+X 2 1)+(8732002477/5100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (509834632906266979/510000000000000000 : ℝ)) (alpha := (8732002477/5100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (509834632906266979/510000000000000000 : ℝ)*(X 0 2+X 1 2)+(8732002477/5100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (509834632906266979/510000000000000000 : ℝ)) (alpha := (8732002477/5100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069027941/5000000000 : ℝ)*X 0 0+(539187153/1000000000 : ℝ)*X 0 1+(5266718411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672245269/5000000000 : ℝ)*X 1 0+(-2201520201/10000000000 : ℝ)*X 1 1+(526671841/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672245269/5000000000 : ℝ)*X 2 0+(526671841/1000000000 : ℝ)*X 2 1+(-2201520201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356152243/10000000000 : ℝ)*X 0 0+(52899423/125000000 : ℝ)*X 0 1+(4483925307/10000000000 : ℝ)*X 0 2+(4356152243/10000000000 : ℝ)*X 1 0+(52899423/125000000 : ℝ)*X 1 1+(4483925307/10000000000 : ℝ)*X 1 2+(4356152243/10000000000 : ℝ)*X 2 0+(52899423/125000000 : ℝ)*X 2 1+(4483925307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534515257/2500000000 : ℝ)*X 0 0+(5267034353/10000000000 : ℝ)*X 0 1+(5391554149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2178080639/5000000000 : ℝ)*X 0 0+(2241645999/5000000000 : ℝ)*X 0 1+(4232589927/10000000000 : ℝ)*X 0 2+(2178080639/5000000000 : ℝ)*X 1 0+(2241645999/5000000000 : ℝ)*X 1 1+(4232589927/10000000000 : ℝ)*X 1 2+(2178080639/5000000000 : ℝ)*X 2 0+(2241645999/5000000000 : ℝ)*X 2 1+(4232589927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19089539661222566745752973/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89166243/20000000000000 : ℝ)*(base19) + (414540087/100000000000000 : ℝ)*(base23) + (3344703/20000000000000 : ℝ)*(lower2) + (28663419/50000000000000 : ℝ)*(upper3) + (1371807/4000000000000 : ℝ)*(upper5) + (2989738348628381/50000000000000 : ℝ)*(major0) + (2989738348628381/50000000000000 : ℝ)*(major1) + (5979476697256763/100000000000000 : ℝ)*(major2) + (3995112608113707/50000000000000 : ℝ)*(sp0) + (1598047403675963/20000000000000 : ℝ)*(sp1) + (249694907802217/3125000000000 : ℝ)*(sp2) + (1984354627735707/50000000000000 : ℝ)*(sp3) + (23921843/195312500000 : ℝ)*(sp4) + (659997013/10000000000000 : ℝ)*(sp5) + (496089481930193/12500000000000 : ℝ)*(f.failure) + (799023746421103/10000000000000 : ℝ)*(f.sum) + (180628194331/34000000000000000000000000 : ℝ)*base65 + (85821855714639667/8500000000000000000000000000000 : ℝ)*base68 + (203264174569090341/17000000000000000000000000000000 : ℝ)*base70 + (131185206888639667/8500000000000000000000000000000 : ℝ)*base72 + (34318434561/6800000000000000000000000 : ℝ)*base73 + (50729162173090341/17000000000000000000000000000000 : ℝ)*base76 + (212020074540769001/25500000000000000000000000000000 : ℝ)*base78 + (696542844153769001/25500000000000000000000000000000 : ℝ)*base80 + (280206895423/127500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4019567/312500000000000000000 : ℝ)*base89 + (4019567/312500000000000000000 : ℝ)*base91 + (894567/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1203_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_box_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006568713/5000000000 : ℝ)*x 0 + (335963997/625000000 : ℝ)*x 1 + (2687711697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006568713/5000000000 : ℝ)^2099 ≤ (1200295458563/10000000000000 : ℝ)^1587 := by
    have hnat : (1006568713 : ℕ)^2099*10000000000000^1587 ≤ 1200295458563^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006568713 5000000000 1200295458563 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335963997/625000000 : ℝ)^2099 ≤ (4399852571839/10000000000000 : ℝ)^1587 := by
    have hnat : (335963997 : ℕ)^2099*10000000000000^1587 ≤ 4399852571839^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335963997 625000000 4399852571839 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687711697/5000000000 : ℝ)^2099 ≤ (43998519677581/100000000000000 : ℝ)^1587 := by
    have hnat : (2687711697 : ℕ)^2099*100000000000000^1587 ≤ 43998519677581^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687711697 5000000000 43998519677581 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006568713/5000000000 : ℝ), (335963997/625000000 : ℝ), (2687711697/5000000000 : ℝ)] ![(1200295458563/10000000000000 : ℝ), (4399852571839/10000000000000 : ℝ), (43998519677581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006568713/5000000000 : ℝ)|^2099 ≤ (1200295458563/10000000000000 : ℝ)^1587
        have hw : |(-1006568713/5000000000 : ℝ)|=(1006568713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335963997/625000000 : ℝ)|^2099 ≤ (4399852571839/10000000000000 : ℝ)^1587
        have hw : |(335963997/625000000 : ℝ)|=(335963997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687711697/5000000000 : ℝ)|^2099 ≤ (43998519677581/100000000000000 : ℝ)^1587
        have hw : |(2687711697/5000000000 : ℝ)|=(2687711697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165515889/312500000 : ℝ)*x 0 + (-530076561/2500000000 : ℝ)*x 1 + (2687711823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165515889/312500000 : ℝ)^2099 ≤ (43146230390167/100000000000000 : ℝ)^1587 := by
    have hnat : (165515889 : ℕ)^2099*100000000000000^1587 ≤ 43146230390167^1587*312500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165515889 312500000 43146230390167 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530076561/2500000000 : ℝ)^2099 ≤ (12855247183289/100000000000000 : ℝ)^1587 := by
    have hnat : (530076561 : ℕ)^2099*100000000000000^1587 ≤ 12855247183289^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530076561 2500000000 12855247183289 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687711823/5000000000 : ℝ)^2099 ≤ (43998522405689/100000000000000 : ℝ)^1587 := by
    have hnat : (2687711823 : ℕ)^2099*100000000000000^1587 ≤ 43998522405689^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687711823 5000000000 43998522405689 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165515889/312500000 : ℝ), (-530076561/2500000000 : ℝ), (2687711823/5000000000 : ℝ)] ![(43146230390167/100000000000000 : ℝ), (12855247183289/100000000000000 : ℝ), (43998522405689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165515889/312500000 : ℝ)|^2099 ≤ (43146230390167/100000000000000 : ℝ)^1587
        have hw : |(165515889/312500000 : ℝ)|=(165515889/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530076561/2500000000 : ℝ)|^2099 ≤ (12855247183289/100000000000000 : ℝ)^1587
        have hw : |(-530076561/2500000000 : ℝ)|=(530076561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687711823/5000000000 : ℝ)|^2099 ≤ (43998522405689/100000000000000 : ℝ)^1587
        have hw : |(2687711823/5000000000 : ℝ)|=(2687711823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42372071/80000000 : ℝ)*x 0 + (5375423337/10000000000 : ℝ)*x 1 + (-2120306089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42372071/80000000 : ℝ)^2099 ≤ (43146234990789/100000000000000 : ℝ)^1587 := by
    have hnat : (42372071 : ℕ)^2099*100000000000000^1587 ≤ 43146234990789^1587*80000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42372071 80000000 43146234990789 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375423337/10000000000 : ℝ)^2099 ≤ (43998519060509/100000000000000 : ℝ)^1587 := by
    have hnat : (5375423337 : ℕ)^2099*100000000000000^1587 ≤ 43998519060509^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375423337 10000000000 43998519060509 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120306089/10000000000 : ℝ)^2099 ≤ (12855245940353/100000000000000 : ℝ)^1587 := by
    have hnat : (2120306089 : ℕ)^2099*100000000000000^1587 ≤ 12855245940353^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120306089 10000000000 12855245940353 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42372071/80000000 : ℝ), (5375423337/10000000000 : ℝ), (-2120306089/10000000000 : ℝ)] ![(43146234990789/100000000000000 : ℝ), (43998519060509/100000000000000 : ℝ), (12855245940353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42372071/80000000 : ℝ)|^2099 ≤ (43146234990789/100000000000000 : ℝ)^1587
        have hw : |(42372071/80000000 : ℝ)|=(42372071/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375423337/10000000000 : ℝ)|^2099 ≤ (43998519060509/100000000000000 : ℝ)^1587
        have hw : |(5375423337/10000000000 : ℝ)|=(5375423337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120306089/10000000000 : ℝ)|^2099 ≤ (12855245940353/100000000000000 : ℝ)^1587
        have hw : |(-2120306089/10000000000 : ℝ)|=(2120306089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (446306071/1000000000 : ℝ)*x 0 + (107619107/250000000 : ℝ)*x 1 + (4304764919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446306071/1000000000 : ℝ)^2099 ≤ (6880608815401/20000000000000 : ℝ)^1587 := by
    have hnat : (446306071 : ℕ)^2099*20000000000000^1587 ≤ 6880608815401^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446306071 1000000000 6880608815401 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107619107/250000000 : ℝ)^2099 ≤ (16399237368093/50000000000000 : ℝ)^1587 := by
    have hnat : (107619107 : ℕ)^2099*50000000000000^1587 ≤ 16399237368093^1587*250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107619107 250000000 16399237368093 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4304764919/10000000000 : ℝ)^2099 ≤ (8199620293879/25000000000000 : ℝ)^1587 := by
    have hnat : (4304764919 : ℕ)^2099*25000000000000^1587 ≤ 8199620293879^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304764919 10000000000 8199620293879 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(446306071/1000000000 : ℝ), (107619107/250000000 : ℝ), (4304764919/10000000000 : ℝ)] ![(6880608815401/20000000000000 : ℝ), (16399237368093/50000000000000 : ℝ), (8199620293879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(446306071/1000000000 : ℝ)|^2099 ≤ (6880608815401/20000000000000 : ℝ)^1587
        have hw : |(446306071/1000000000 : ℝ)|=(446306071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107619107/250000000 : ℝ)|^2099 ≤ (16399237368093/50000000000000 : ℝ)^1587
        have hw : |(107619107/250000000 : ℝ)|=(107619107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4304764919/10000000000 : ℝ)|^2099 ≤ (8199620293879/25000000000000 : ℝ)^1587
        have hw : |(4304764919/10000000000 : ℝ)|=(4304764919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1132174753/5000000000 : ℝ)*x 0 + (5281872143/10000000000 : ℝ)*x 1 + (1056374399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132174753/5000000000 : ℝ)^2099 ≤ (14022791737287/100000000000000 : ℝ)^1587 := by
    have hnat : (1132174753 : ℕ)^2099*100000000000000^1587 ≤ 14022791737287^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132174753 5000000000 14022791737287 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281872143/10000000000 : ℝ)^2099 ≤ (10747151230023/25000000000000 : ℝ)^1587 := by
    have hnat : (5281872143 : ℕ)^2099*25000000000000^1587 ≤ 10747151230023^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281872143 10000000000 10747151230023 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056374399/2000000000 : ℝ)^2099 ≤ (42988603326919/100000000000000 : ℝ)^1587 := by
    have hnat : (1056374399 : ℕ)^2099*100000000000000^1587 ≤ 42988603326919^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056374399 2000000000 42988603326919 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1132174753/5000000000 : ℝ), (5281872143/10000000000 : ℝ), (1056374399/2000000000 : ℝ)] ![(14022791737287/100000000000000 : ℝ), (10747151230023/25000000000000 : ℝ), (42988603326919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1132174753/5000000000 : ℝ)|^2099 ≤ (14022791737287/100000000000000 : ℝ)^1587
        have hw : |(-1132174753/5000000000 : ℝ)|=(1132174753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281872143/10000000000 : ℝ)|^2099 ≤ (10747151230023/25000000000000 : ℝ)^1587
        have hw : |(5281872143/10000000000 : ℝ)|=(5281872143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056374399/2000000000 : ℝ)|^2099 ≤ (42988603326919/100000000000000 : ℝ)^1587
        have hw : |(1056374399/2000000000 : ℝ)|=(1056374399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214500527/400000000 : ℝ)*x 0 + (-2157282621/10000000000 : ℝ)*x 1 + (1056374341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214500527/400000000 : ℝ)^2099 ≤ (10964702528979/25000000000000 : ℝ)^1587 := by
    have hnat : (214500527 : ℕ)^2099*25000000000000^1587 ≤ 10964702528979^1587*400000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214500527 400000000 10964702528979 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157282621/10000000000 : ℝ)^2099 ≤ (13152589659429/100000000000000 : ℝ)^1587 := by
    have hnat : (2157282621 : ℕ)^2099*100000000000000^1587 ≤ 13152589659429^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157282621 10000000000 13152589659429 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056374341/2000000000 : ℝ)^2099 ≤ (42988600205163/100000000000000 : ℝ)^1587 := by
    have hnat : (1056374341 : ℕ)^2099*100000000000000^1587 ≤ 42988600205163^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056374341 2000000000 42988600205163 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214500527/400000000 : ℝ), (-2157282621/10000000000 : ℝ), (1056374341/2000000000 : ℝ)] ![(10964702528979/25000000000000 : ℝ), (13152589659429/100000000000000 : ℝ), (42988600205163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214500527/400000000 : ℝ)|^2099 ≤ (10964702528979/25000000000000 : ℝ)^1587
        have hw : |(214500527/400000000 : ℝ)|=(214500527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157282621/10000000000 : ℝ)|^2099 ≤ (13152589659429/100000000000000 : ℝ)^1587
        have hw : |(-2157282621/10000000000 : ℝ)|=(2157282621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056374341/2000000000 : ℝ)|^2099 ≤ (42988600205163/100000000000000 : ℝ)^1587
        have hw : |(1056374341/2000000000 : ℝ)|=(1056374341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362512659/10000000000 : ℝ)*x 0 + (1056374443/2000000000 : ℝ)*x 1 + (-2157282633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362512659/10000000000 : ℝ)^2099 ≤ (10964701133531/25000000000000 : ℝ)^1587 := by
    have hnat : (5362512659 : ℕ)^2099*25000000000000^1587 ≤ 10964701133531^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362512659 10000000000 10964701133531 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056374443/2000000000 : ℝ)^2099 ≤ (10747151423787/25000000000000 : ℝ)^1587 := by
    have hnat : (1056374443 : ℕ)^2099*25000000000000^1587 ≤ 10747151423787^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056374443 2000000000 10747151423787 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157282633/10000000000 : ℝ)^2099 ≤ (2630517951239/20000000000000 : ℝ)^1587 := by
    have hnat : (2157282633 : ℕ)^2099*20000000000000^1587 ≤ 2630517951239^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157282633 10000000000 2630517951239 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362512659/10000000000 : ℝ), (1056374443/2000000000 : ℝ), (-2157282633/10000000000 : ℝ)] ![(10964701133531/25000000000000 : ℝ), (10747151423787/25000000000000 : ℝ), (2630517951239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362512659/10000000000 : ℝ)|^2099 ≤ (10964701133531/25000000000000 : ℝ)^1587
        have hw : |(5362512659/10000000000 : ℝ)|=(5362512659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056374443/2000000000 : ℝ)|^2099 ≤ (10747151423787/25000000000000 : ℝ)^1587
        have hw : |(1056374443/2000000000 : ℝ)|=(1056374443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2157282633/10000000000 : ℝ)|^2099 ≤ (2630517951239/20000000000000 : ℝ)^1587
        have hw : |(-2157282633/10000000000 : ℝ)|=(2157282633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2124428121/5000000000 : ℝ)*x 0 + (4411846183/10000000000 : ℝ)*x 1 + (4411846721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124428121/5000000000 : ℝ)^2099 ≤ (16118131091793/50000000000000 : ℝ)^1587 := by
    have hnat : (2124428121 : ℕ)^2099*50000000000000^1587 ≤ 16118131091793^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124428121 5000000000 16118131091793 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4411846183/10000000000 : ℝ)^2099 ≤ (677637323271/2000000000000 : ℝ)^1587 := by
    have hnat : (4411846183 : ℕ)^2099*2000000000000^1587 ≤ 677637323271^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411846183 10000000000 677637323271 2000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4411846721/10000000000 : ℝ)^2099 ≤ (3388187162823/10000000000000 : ℝ)^1587 := by
    have hnat : (4411846721 : ℕ)^2099*10000000000000^1587 ≤ 3388187162823^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411846721 10000000000 3388187162823 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124428121/5000000000 : ℝ), (4411846183/10000000000 : ℝ), (4411846721/10000000000 : ℝ)] ![(16118131091793/50000000000000 : ℝ), (677637323271/2000000000000 : ℝ), (3388187162823/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124428121/5000000000 : ℝ)|^2099 ≤ (16118131091793/50000000000000 : ℝ)^1587
        have hw : |(2124428121/5000000000 : ℝ)|=(2124428121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4411846183/10000000000 : ℝ)|^2099 ≤ (677637323271/2000000000000 : ℝ)^1587
        have hw : |(4411846183/10000000000 : ℝ)|=(4411846183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4411846721/10000000000 : ℝ)|^2099 ≤ (3388187162823/10000000000000 : ℝ)^1587
        have hw : |(4411846721/10000000000 : ℝ)|=(4411846721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_8 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-27646873/125000000 : ℝ)*x 0 + (2609066409/5000000000 : ℝ)*x 1 + (2692517713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27646873/125000000 : ℝ)^2099 ≤ (6796790568407/50000000000000 : ℝ)^1587 := by
    have hnat : (27646873 : ℕ)^2099*50000000000000^1587 ≤ 6796790568407^1587*125000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27646873 125000000 6796790568407 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609066409/5000000000 : ℝ)^2099 ≤ (8460762202997/20000000000000 : ℝ)^1587 := by
    have hnat : (2609066409 : ℕ)^2099*20000000000000^1587 ≤ 8460762202997^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609066409 5000000000 8460762202997 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692517713/5000000000 : ℝ)^2099 ≤ (4410260783243/10000000000000 : ℝ)^1587 := by
    have hnat : (2692517713 : ℕ)^2099*10000000000000^1587 ≤ 4410260783243^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692517713 5000000000 4410260783243 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27646873/125000000 : ℝ), (2609066409/5000000000 : ℝ), (2692517713/5000000000 : ℝ)] ![(6796790568407/50000000000000 : ℝ), (8460762202997/20000000000000 : ℝ), (4410260783243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27646873/125000000 : ℝ)|^2099 ≤ (6796790568407/50000000000000 : ℝ)^1587
        have hw : |(-27646873/125000000 : ℝ)|=(27646873/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609066409/5000000000 : ℝ)|^2099 ≤ (8460762202997/20000000000000 : ℝ)^1587
        have hw : |(2609066409/5000000000 : ℝ)|=(2609066409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692517713/5000000000 : ℝ)|^2099 ≤ (4410260783243/10000000000000 : ℝ)^1587
        have hw : |(2692517713/5000000000 : ℝ)|=(2692517713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_9 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661215527/1250000000 : ℝ)*x 0 + (-33069353/156250000 : ℝ)*x 1 + (2692517719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661215527/1250000000 : ℝ)^2099 ≤ (269207188799/625000000000 : ℝ)^1587 := by
    have hnat : (661215527 : ℕ)^2099*625000000000^1587 ≤ 269207188799^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661215527 1250000000 269207188799 625000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33069353/156250000 : ℝ)^2099 ≤ (641212090799/5000000000000 : ℝ)^1587 := by
    have hnat : (33069353 : ℕ)^2099*5000000000000^1587 ≤ 641212090799^1587*156250000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33069353 156250000 641212090799 5000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692517719/5000000000 : ℝ)^2099 ≤ (8820521592483/20000000000000 : ℝ)^1587 := by
    have hnat : (2692517719 : ℕ)^2099*20000000000000^1587 ≤ 8820521592483^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692517719 5000000000 8820521592483 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661215527/1250000000 : ℝ), (-33069353/156250000 : ℝ), (2692517719/5000000000 : ℝ)] ![(269207188799/625000000000 : ℝ), (641212090799/5000000000000 : ℝ), (8820521592483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661215527/1250000000 : ℝ)|^2099 ≤ (269207188799/625000000000 : ℝ)^1587
        have hw : |(661215527/1250000000 : ℝ)|=(661215527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33069353/156250000 : ℝ)|^2099 ≤ (641212090799/5000000000000 : ℝ)^1587
        have hw : |(-33069353/156250000 : ℝ)|=(33069353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692517719/5000000000 : ℝ)|^2099 ≤ (8820521592483/20000000000000 : ℝ)^1587
        have hw : |(2692517719/5000000000 : ℝ)|=(2692517719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_10 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322431051/2500000000 : ℝ)*x 0 + (2692517711/5000000000 : ℝ)*x 1 + (-211643863/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322431051/2500000000 : ℝ)^2099 ≤ (21536575039301/50000000000000 : ℝ)^1587 := by
    have hnat : (1322431051 : ℕ)^2099*50000000000000^1587 ≤ 21536575039301^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322431051 2500000000 21536575039301 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692517711/5000000000 : ℝ)^2099 ≤ (22051303894551/50000000000000 : ℝ)^1587 := by
    have hnat : (2692517711 : ℕ)^2099*50000000000000^1587 ≤ 22051303894551^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692517711 5000000000 22051303894551 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211643863/1000000000 : ℝ)^2099 ≤ (320606053013/2500000000000 : ℝ)^1587 := by
    have hnat : (211643863 : ℕ)^2099*2500000000000^1587 ≤ 320606053013^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211643863 1000000000 320606053013 2500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322431051/2500000000 : ℝ), (2692517711/5000000000 : ℝ), (-211643863/1000000000 : ℝ)] ![(21536575039301/50000000000000 : ℝ), (22051303894551/50000000000000 : ℝ), (320606053013/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322431051/2500000000 : ℝ)|^2099 ≤ (21536575039301/50000000000000 : ℝ)^1587
        have hw : |(1322431051/2500000000 : ℝ)|=(1322431051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692517711/5000000000 : ℝ)|^2099 ≤ (22051303894551/50000000000000 : ℝ)^1587
        have hw : |(2692517711/5000000000 : ℝ)|=(2692517711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211643863/1000000000 : ℝ)|^2099 ≤ (320606053013/2500000000000 : ℝ)^1587
        have hw : |(-211643863/1000000000 : ℝ)|=(211643863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_11 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4484796557/10000000000 : ℝ)*x 0 + (214687809/500000000 : ℝ)*x 1 + (429375611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4484796557/10000000000 : ℝ)^2099 ≤ (17312410623021/50000000000000 : ℝ)^1587 := by
    have hnat : (4484796557 : ℕ)^2099*50000000000000^1587 ≤ 17312410623021^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484796557 10000000000 17312410623021 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214687809/500000000 : ℝ)^2099 ≤ (16343794860229/50000000000000 : ℝ)^1587 := by
    have hnat : (214687809 : ℕ)^2099*50000000000000^1587 ≤ 16343794860229^1587*500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214687809 500000000 16343794860229 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429375611/1000000000 : ℝ)^2099 ≤ (32687589015637/100000000000000 : ℝ)^1587 := by
    have hnat : (429375611 : ℕ)^2099*100000000000000^1587 ≤ 32687589015637^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429375611 1000000000 32687589015637 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4484796557/10000000000 : ℝ), (214687809/500000000 : ℝ), (429375611/1000000000 : ℝ)] ![(17312410623021/50000000000000 : ℝ), (16343794860229/50000000000000 : ℝ), (32687589015637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4484796557/10000000000 : ℝ)|^2099 ≤ (17312410623021/50000000000000 : ℝ)^1587
        have hw : |(4484796557/10000000000 : ℝ)|=(4484796557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214687809/500000000 : ℝ)|^2099 ≤ (16343794860229/50000000000000 : ℝ)^1587
        have hw : |(214687809/500000000 : ℝ)|=(214687809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429375611/1000000000 : ℝ)|^2099 ≤ (32687589015637/100000000000000 : ℝ)^1587
        have hw : |(429375611/1000000000 : ℝ)|=(429375611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_12 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066019699/10000000000 : ℝ)*x 0 + (5437927943/10000000000 : ℝ)*x 1 + (659225979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066019699/10000000000 : ℝ)^2099 ≤ (12421734657499/100000000000000 : ℝ)^1587 := by
    have hnat : (2066019699 : ℕ)^2099*100000000000000^1587 ≤ 12421734657499^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066019699 10000000000 12421734657499 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437927943/10000000000 : ℝ)^2099 ≤ (22338224361829/50000000000000 : ℝ)^1587 := by
    have hnat : (5437927943 : ℕ)^2099*50000000000000^1587 ≤ 22338224361829^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437927943 10000000000 22338224361829 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659225979/1250000000 : ℝ)^2099 ≤ (8580363321851/20000000000000 : ℝ)^1587 := by
    have hnat : (659225979 : ℕ)^2099*20000000000000^1587 ≤ 8580363321851^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659225979 1250000000 8580363321851 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066019699/10000000000 : ℝ), (5437927943/10000000000 : ℝ), (659225979/1250000000 : ℝ)] ![(12421734657499/100000000000000 : ℝ), (22338224361829/50000000000000 : ℝ), (8580363321851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066019699/10000000000 : ℝ)|^2099 ≤ (12421734657499/100000000000000 : ℝ)^1587
        have hw : |(-2066019699/10000000000 : ℝ)|=(2066019699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437927943/10000000000 : ℝ)|^2099 ≤ (22338224361829/50000000000000 : ℝ)^1587
        have hw : |(5437927943/10000000000 : ℝ)|=(5437927943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659225979/1250000000 : ℝ)|^2099 ≤ (8580363321851/20000000000000 : ℝ)^1587
        have hw : |(659225979/1250000000 : ℝ)|=(659225979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_13 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368200483/10000000000 : ℝ)*x 0 + (-108020671/500000000 : ℝ)*x 1 + (2636903869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368200483/10000000000 : ℝ)^2099 ≤ (4392034267941/10000000000000 : ℝ)^1587 := by
    have hnat : (5368200483 : ℕ)^2099*10000000000000^1587 ≤ 4392034267941^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368200483 10000000000 4392034267941 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108020671/500000000 : ℝ)^2099 ≤ (3294460426039/25000000000000 : ℝ)^1587 := by
    have hnat : (108020671 : ℕ)^2099*25000000000000^1587 ≤ 3294460426039^1587*500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108020671 500000000 3294460426039 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636903869/5000000000 : ℝ)^2099 ≤ (343214524783/800000000000 : ℝ)^1587 := by
    have hnat : (2636903869 : ℕ)^2099*800000000000^1587 ≤ 343214524783^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636903869 5000000000 343214524783 800000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368200483/10000000000 : ℝ), (-108020671/500000000 : ℝ), (2636903869/5000000000 : ℝ)] ![(4392034267941/10000000000000 : ℝ), (3294460426039/25000000000000 : ℝ), (343214524783/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368200483/10000000000 : ℝ)|^2099 ≤ (4392034267941/10000000000000 : ℝ)^1587
        have hw : |(5368200483/10000000000 : ℝ)|=(5368200483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108020671/500000000 : ℝ)|^2099 ≤ (3294460426039/25000000000000 : ℝ)^1587
        have hw : |(-108020671/500000000 : ℝ)|=(108020671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636903869/5000000000 : ℝ)|^2099 ≤ (343214524783/800000000000 : ℝ)^1587
        have hw : |(2636903869/5000000000 : ℝ)|=(2636903869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_14 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368200711/10000000000 : ℝ)*x 0 + (5273807641/10000000000 : ℝ)*x 1 + (-432082649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368200711/10000000000 : ℝ)^2099 ≤ (43920345146627/100000000000000 : ℝ)^1587 := by
    have hnat : (5368200711 : ℕ)^2099*100000000000000^1587 ≤ 43920345146627^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368200711 10000000000 43920345146627 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273807641/10000000000 : ℝ)^2099 ≤ (5362726819277/12500000000000 : ℝ)^1587 := by
    have hnat : (5273807641 : ℕ)^2099*12500000000000^1587 ≤ 5362726819277^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273807641 10000000000 5362726819277 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432082649/2000000000 : ℝ)^2099 ≤ (1317784029233/10000000000000 : ℝ)^1587 := by
    have hnat : (432082649 : ℕ)^2099*10000000000000^1587 ≤ 1317784029233^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432082649 2000000000 1317784029233 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368200711/10000000000 : ℝ), (5273807641/10000000000 : ℝ), (-432082649/2000000000 : ℝ)] ![(43920345146627/100000000000000 : ℝ), (5362726819277/12500000000000 : ℝ), (1317784029233/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368200711/10000000000 : ℝ)|^2099 ≤ (43920345146627/100000000000000 : ℝ)^1587
        have hw : |(5368200711/10000000000 : ℝ)|=(5368200711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273807641/10000000000 : ℝ)|^2099 ≤ (5362726819277/12500000000000 : ℝ)^1587
        have hw : |(5273807641/10000000000 : ℝ)|=(5273807641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432082649/2000000000 : ℝ)|^2099 ≤ (1317784029233/10000000000000 : ℝ)^1587
        have hw : |(-432082649/2000000000 : ℝ)|=(432082649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_box_15 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2115079861/5000000000 : ℝ)*x 0 + (552634059/1250000000 : ℝ)*x 1 + (4421071919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115079861/5000000000 : ℝ)^2099 ≤ (32048779896671/100000000000000 : ℝ)^1587 := by
    have hnat : (2115079861 : ℕ)^2099*100000000000000^1587 ≤ 32048779896671^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115079861 5000000000 32048779896671 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552634059/1250000000 : ℝ)^2099 ≤ (2123475803281/6250000000000 : ℝ)^1587 := by
    have hnat : (552634059 : ℕ)^2099*6250000000000^1587 ≤ 2123475803281^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552634059 1250000000 2123475803281 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421071919/10000000000 : ℝ)^2099 ≤ (8493901807917/25000000000000 : ℝ)^1587 := by
    have hnat : (4421071919 : ℕ)^2099*25000000000000^1587 ≤ 8493901807917^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421071919 10000000000 8493901807917 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115079861/5000000000 : ℝ), (552634059/1250000000 : ℝ), (4421071919/10000000000 : ℝ)] ![(32048779896671/100000000000000 : ℝ), (2123475803281/6250000000000 : ℝ), (8493901807917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115079861/5000000000 : ℝ)|^2099 ≤ (32048779896671/100000000000000 : ℝ)^1587
        have hw : |(2115079861/5000000000 : ℝ)|=(2115079861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552634059/1250000000 : ℝ)|^2099 ≤ (2123475803281/6250000000000 : ℝ)^1587
        have hw : |(552634059/1250000000 : ℝ)|=(552634059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421071919/10000000000 : ℝ)|^2099 ≤ (8493901807917/25000000000000 : ℝ)^1587
        have hw : |(4421071919/10000000000 : ℝ)|=(4421071919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(389/625 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29673/50000 : ℝ) ∧ (79993/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4163/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1429/12500 : ℝ) ^ (8395/2048 : ℝ) ≤ (13776183119085661/100000000000000000000 : ℝ) := by
    have hpowers : (1429/12500 : ℝ)^8395 ≤ (13776183119085661/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1429 : ℕ)^8395*100000000000000000000^2048 ≤ 13776183119085661^2048*12500^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1429 12500 13776183119085661 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1429/12500 : ℝ)) (X := (13776183119085661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (32389068066475331/100000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^8395 ≤ (32389068066475331/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14083 : ℕ)^8395*100000000000000000000^2048 ≤ 32389068066475331^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 32389068066475331 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (32389068066475331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013776183119085661/50000000000000000000 : ℝ) ≤ (10000672083024061/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50013776183119085661/50000000000000000000 : ℝ)^2048 ≤ (10000672083024061/10000000000000000 : ℝ)^8395 := by
      have hnat : (50013776183119085661 : ℕ)^2048*10000000000000000^8395 ≤ 10000672083024061^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013776183119085661 50000000000000000000 10000672083024061 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672083024061/10000000000000000 : ℝ)) (X := (50013776183119085661/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126442664099548781/3125000000000000000 : ℝ) ≤ (10001126026671889/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (3126442664099548781/3125000000000000000 : ℝ)^2048 ≤ (10001126026671889/10000000000000000 : ℝ)^8395 := by
      have hnat : (3126442664099548781 : ℕ)^2048*10000000000000000^8395 ≤ 10001126026671889^8395*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126442664099548781 3125000000000000000 10001126026671889 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126026671889/10000000000000000 : ℝ)) (X := (3126442664099548781/3125000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032389068066475331/50000000000000000000 : ℝ) ≤ (10001579970319717/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50032389068066475331/50000000000000000000 : ℝ)^2048 ≤ (10001579970319717/10000000000000000 : ℝ)^8395 := by
      have hnat : (50032389068066475331 : ℕ)^2048*10000000000000000^8395 ≤ 10001579970319717^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032389068066475331 50000000000000000000 10001579970319717 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001579970319717/10000000000000000 : ℝ)) (X := (50032389068066475331/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13776183119085661/100000000000000000000 : ℝ) ≤ ((2409218429502986029/2410000000000000000 : ℝ)+2*(10316901087/6025000000000 : ℝ)*(1429/12500 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (2409218429502986029/2410000000000000000 : ℝ)+2*(10316901087/6025000000000 : ℝ)*(1429/12500 : ℝ)=(10000672083024061/10000000000000000 : ℝ) by norm_num, show 1+2*(13776183119085661/100000000000000000000 : ℝ)=(50013776183119085661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32389068066475331/100000000000000000000 : ℝ)+(13776183119085661/100000000000000000000 : ℝ) ≤ ((2409218429502986029/2410000000000000000 : ℝ)+(10316901087/6025000000000 : ℝ)*((14083/100000 : ℝ)+(1429/12500 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (2409218429502986029/2410000000000000000 : ℝ)+(10316901087/6025000000000 : ℝ)*((14083/100000 : ℝ)+(1429/12500 : ℝ))=(10001126026671889/10000000000000000 : ℝ) by norm_num, show 1+(32389068066475331/100000000000000000000 : ℝ)+(13776183119085661/100000000000000000000 : ℝ)=(3126442664099548781/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32389068066475331/100000000000000000000 : ℝ) ≤ ((2409218429502986029/2410000000000000000 : ℝ)+2*(10316901087/6025000000000 : ℝ)*(14083/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (2409218429502986029/2410000000000000000 : ℝ)+2*(10316901087/6025000000000 : ℝ)*(14083/100000 : ℝ)=(10001579970319717/10000000000000000 : ℝ) by norm_num, show 1+2*(32389068066475331/100000000000000000000 : ℝ)=(50032389068066475331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2409218429502986029/2410000000000000000 : ℝ)*(X 1 0+X 2 0)+(10316901087/6025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (2409218429502986029/2410000000000000000 : ℝ)) (alpha := (10316901087/6025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2409218429502986029/2410000000000000000 : ℝ)*(X 0 1+X 2 1)+(10316901087/6025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (2409218429502986029/2410000000000000000 : ℝ)) (alpha := (10316901087/6025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2409218429502986029/2410000000000000000 : ℝ)*(X 0 2+X 1 2)+(10316901087/6025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (2409218429502986029/2410000000000000000 : ℝ)) (alpha := (10316901087/6025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006568713/5000000000 : ℝ)*X 0 0+(335963997/625000000 : ℝ)*X 0 1+(2687711697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165515889/312500000 : ℝ)*X 1 0+(-530076561/2500000000 : ℝ)*X 1 1+(2687711823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42372071/80000000 : ℝ)*X 2 0+(5375423337/10000000000 : ℝ)*X 2 1+(-2120306089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((446306071/1000000000 : ℝ)*X 0 0+(107619107/250000000 : ℝ)*X 0 1+(4304764919/10000000000 : ℝ)*X 0 2+(446306071/1000000000 : ℝ)*X 1 0+(107619107/250000000 : ℝ)*X 1 1+(4304764919/10000000000 : ℝ)*X 1 2+(446306071/1000000000 : ℝ)*X 2 0+(107619107/250000000 : ℝ)*X 2 1+(4304764919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1132174753/5000000000 : ℝ)*X 0 0+(5281872143/10000000000 : ℝ)*X 0 1+(1056374399/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((214500527/400000000 : ℝ)*X 1 0+(-2157282621/10000000000 : ℝ)*X 1 1+(1056374341/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362512659/10000000000 : ℝ)*X 2 0+(1056374443/2000000000 : ℝ)*X 2 1+(-2157282633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2124428121/5000000000 : ℝ)*X 0 0+(4411846183/10000000000 : ℝ)*X 0 1+(4411846721/10000000000 : ℝ)*X 0 2+(2124428121/5000000000 : ℝ)*X 1 0+(4411846183/10000000000 : ℝ)*X 1 1+(4411846721/10000000000 : ℝ)*X 1 2+(2124428121/5000000000 : ℝ)*X 2 0+(4411846183/10000000000 : ℝ)*X 2 1+(4411846721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-27646873/125000000 : ℝ)*X 0 0+(2609066409/5000000000 : ℝ)*X 0 1+(2692517713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661215527/1250000000 : ℝ)*X 1 0+(-33069353/156250000 : ℝ)*X 1 1+(2692517719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322431051/2500000000 : ℝ)*X 2 0+(2692517711/5000000000 : ℝ)*X 2 1+(-211643863/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4484796557/10000000000 : ℝ)*X 0 0+(214687809/500000000 : ℝ)*X 0 1+(429375611/1000000000 : ℝ)*X 0 2+(4484796557/10000000000 : ℝ)*X 1 0+(214687809/500000000 : ℝ)*X 1 1+(429375611/1000000000 : ℝ)*X 1 2+(4484796557/10000000000 : ℝ)*X 2 0+(214687809/500000000 : ℝ)*X 2 1+(429375611/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2066019699/10000000000 : ℝ)*X 0 0+(5437927943/10000000000 : ℝ)*X 0 1+(659225979/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368200483/10000000000 : ℝ)*X 1 0+(-108020671/500000000 : ℝ)*X 1 1+(2636903869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368200711/10000000000 : ℝ)*X 2 0+(5273807641/10000000000 : ℝ)*X 2 1+(-432082649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2115079861/5000000000 : ℝ)*X 0 0+(552634059/1250000000 : ℝ)*X 0 1+(4421071919/10000000000 : ℝ)*X 0 2+(2115079861/5000000000 : ℝ)*X 1 0+(552634059/1250000000 : ℝ)*X 1 1+(4421071919/10000000000 : ℝ)*X 1 2+(2115079861/5000000000 : ℝ)*X 2 0+(552634059/1250000000 : ℝ)*X 2 1+(4421071919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-389/625 : ℝ) ≤ (-18748934393669818445959469031579/30125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58156053/100000000000000 : ℝ)*(upper0) + (49725543/100000000000000 : ℝ)*(upper1) + (188211853/100000000000000 : ℝ)*(upper2) + (904567/5000000000000 : ℝ)*(upper3) + (96513571/100000000000000 : ℝ)*(upper5) + (992812133285683/25000000000000 : ℝ)*(major0) + (992812133285683/25000000000000 : ℝ)*(major1) + (992812133285683/25000000000000 : ℝ)*(major2) + (6566479811/50000000000000 : ℝ)*(sp1) + (693818267/10000000000000 : ℝ)*(sp3) + (5327434021757799/100000000000000 : ℝ)*(sp4) + (5327420888798177/100000000000000 : ℝ)*(sp5) + (5327434021757799/100000000000000 : ℝ)*(sp6) + (1317900907608819/50000000000000 : ℝ)*(sp7) + (2635808753400307/100000000000000 : ℝ)*(f.failure) + (5327434021757799/100000000000000 : ℝ)*(f.sum) + (4310011468837/602500000000000000000000000 : ℝ)*base66 + (237909429627193/60250000000000000000000000000000 : ℝ)*base68 + (630684357969872807/60250000000000000000000000000000 : ℝ)*base69 + (90460122418627193/60250000000000000000000000000000 : ℝ)*base72 + (98083014912409/1205000000000000000000000000 : ℝ)*base74 + (1020344258698127193/60250000000000000000000000000000 : ℝ)*base76 + (552702065753872807/60250000000000000000000000000000 : ℝ)*base77 + (4191623241491627193/60250000000000000000000000000000 : ℝ)*base80 + (8570641024269/1205000000000000000000000000 : ℝ)*base82 + (1840067/2500000000000000000000 : ℝ)*base90 + (1840067/2500000000000000000000 : ℝ)*base92 + (1840067/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29673/50000 : ℝ) ≤ (14303036892761677888780860422031/24100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188838297/50000000000000 : ℝ)*(upper0) + (36112023/50000000000000 : ℝ)*(upper2) + (146165821/100000000000000 : ℝ)*(upper3) + (85640167/25000000000000 : ℝ)*(upper4) + (4036367871603217/100000000000000 : ℝ)*(major0) + (4036367871603217/100000000000000 : ℝ)*(major1) + (2018183935801609/50000000000000 : ℝ)*(major2) + (5373922890740863/100000000000000 : ℝ)*(sp0) + (1343477928470521/25000000000000 : ℝ)*(sp1) + (1074783569494601/20000000000000 : ℝ)*(sp2) + (83717938901823/3125000000000 : ℝ)*(sp3) + (2521633929/50000000000000 : ℝ)*(sp6) + (11176858779/100000000000000 : ℝ)*(sp9) + (11181468123/20000000000000 : ℝ)*(sp11) + (2679029952198951/100000000000000 : ℝ)*(f.failure) + (5373922890740863/100000000000000 : ℝ)*(f.sum) + (530596839019/241000000000000000000000000 : ℝ)*base66 + (495650751372855293/241000000000000000000000000000000 : ℝ)*base67 + (1562564892170520661/120500000000000000000000000000000 : ℝ)*base69 + (2943622794517855293/241000000000000000000000000000000 : ℝ)*base71 + (195402646491/120500000000000000000000000 : ℝ)*base73 + (1530774649168520661/120500000000000000000000000000000 : ℝ)*base75 + (1805286878057944707/241000000000000000000000000000000 : ℝ)*base78 + (1568328239399055293/241000000000000000000000000000000 : ℝ)*base79 + (1862390786859/1205000000000000000000000000 : ℝ)*base82 + (14831369/2500000000000000000000 : ℝ)*base89 + (14831369/2500000000000000000000 : ℝ)*base91 + (10168631/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79993/100000 : ℝ) ≤ (48197244410355390866769486940629/60250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8233003/50000000000000 : ℝ)*(upper1) + (14362151/100000000000000 : ℝ)*(upper2) + (13793701/100000000000000 : ℝ)*(upper3) + (9343263/100000000000000 : ℝ)*(lower5) + (4503694122122467/100000000000000 : ℝ)*(major0) + (4503694122122467/100000000000000 : ℝ)*(major1) + (1125923530530617/25000000000000 : ℝ)*(major2) + (311595213/100000000000000 : ℝ)*(sp0) + (660753623/6250000000000 : ℝ)*(sp1) + (2326986149/50000000000000 : ℝ)*(sp3) + (2995758842601627/50000000000000 : ℝ)*(sp8) + (5991507424740499/100000000000000 : ℝ)*(sp9) + (5991517996798467/100000000000000 : ℝ)*(sp10) + (298920045133841/10000000000000 : ℝ)*(sp11) + (747301276327677/25000000000000 : ℝ)*(f.failure) + (5991517996798467/100000000000000 : ℝ)*(f.sum) + (444895905797/120500000000000000000000000 : ℝ)*base66 + (3916652817093586457/241000000000000000000000000000000 : ℝ)*base68 + (3942302416831350107/60250000000000000000000000000000 : ℝ)*base70 + (1883211126103586457/241000000000000000000000000000000 : ℝ)*base72 + (831960557751/120500000000000000000000000 : ℝ)*base74 + (1665790130887649893/60250000000000000000000000000000 : ℝ)*base75 + (1903257821158386457/241000000000000000000000000000000 : ℝ)*base78 + (2331087310294386457/241000000000000000000000000000000 : ℝ)*base80 + (1952605977411/301250000000000000000000000 : ℝ)*base82 + (11660963/625000000000000000000 : ℝ)*base89 + (11660963/625000000000000000000 : ℝ)*base91 + (5410963/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-4163/5000 : ℝ) ≤ (-50162689231055319111096486631773/60250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138910867/100000000000000 : ℝ)*(upper1) + (135712329/100000000000000 : ℝ)*(lower2) + (7030939/10000000000000 : ℝ)*(upper3) + (37759379/25000000000000 : ℝ)*(upper5) + (4538986325226443/100000000000000 : ℝ)*(major0) + (4538986325226443/100000000000000 : ℝ)*(major1) + (1134746581306611/25000000000000 : ℝ)*(major2) + (14045321409/100000000000000 : ℝ)*(sp4) + (282192903/5000000000000 : ℝ)*(sp6) + (89885127579/50000000000000 : ℝ)*(sp7) + (6093081780166487/100000000000000 : ℝ)*(sp12) + (761636978185987/12500000000000 : ℝ)*(sp13) + (1523272545407459/25000000000000 : ℝ)*(sp14) + (753112394968059/25000000000000 : ℝ)*(sp15) + (1506314675063697/50000000000000 : ℝ)*(f.failure) + (761636978185987/12500000000000 : ℝ)*(f.sum) + (3947424103167/1205000000000000000000000000 : ℝ)*base66 + (633877217252435153/241000000000000000000000000000000 : ℝ)*base68 + (188739008557187719/60250000000000000000000000000000 : ℝ)*base69 + (1823723947494435153/241000000000000000000000000000000 : ℝ)*base72 + (257017639487/75312500000000000000000000 : ℝ)*base74 + (117971038989937719/60250000000000000000000000000000 : ℝ)*base75 + (1848417929417235153/241000000000000000000000000000000 : ℝ)*base78 + (2305753873255235153/241000000000000000000000000000000 : ℝ)*base80 + (6860696934123/602500000000000000000000000 : ℝ)*base82 + (19021343/1250000000000000000000 : ℝ)*base89 + (19021343/1250000000000000000000 : ℝ)*base91 + (6521343/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1203_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(29673/50000 : ℝ) else (79993/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4163/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1203_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1203_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(29673/50000 : ℝ) else (79993/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4163/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1203_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1203_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(29673/50000 : ℝ) else (79993/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4163/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

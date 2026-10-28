-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_pow_four_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:07.459111+00:00
-- url     : https://prove2.me/submissions/b9726ec5-9e3b-4d0a-a6d8-e920991a69be

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_pow_gaussianReal_zero_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The odd moments of the standard real Gaussian vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith
section Increments
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab]
  exact integral_pow_gaussianReal_zero_readable _ m
/-- Odd moments of a Brownian increment vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]
/-- The second moment of a Brownian increment is its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num
/-- The fourth moment of a Brownian increment is the square of its length, up to the fourth
moment of the standard Gaussian. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 4 ∂P = (b - a) ^ 2 * gaussianFourthMoment := by
  rw [integral_increment_pow W ha hab 4]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
end Increments
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono ((continuous_pow m).comp_aestronglyMeasurable h.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp
section Moments
/-- One step of a fourth-moment recursion. -/
 theorem solution
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS4 : MemLp S 4 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
      = (∫ ω, S ω ^ 4 ∂P)
        + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
        + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * LevyStochCalc.Brownian.Ito.gaussianFourthMoment) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD4 : MemLp (fun ω => W.W b ω - W.W a ω) 4 P := LevyStochCalc.Brownian.Ito.memLp_increment W ha hab 4 (by simp)
  have hU4 : Integrable
      (fun ω => (|S ω| + |W.W b ω - W.W a ω|) ^ 4) P :=
    LevyStochCalc.Brownian.Ito.SimplePredictable.integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) (hS4.abs.add hD4.abs)
  have hpow : ∀ (i j : ℕ), i + j = 4 → ∀ ω,
      |S ω| ^ i * |W.W b ω - W.W a ω| ^ j ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by
    intro i j hij ω
    have hx : |S ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (W.W b ω - W.W a ω)]
    have hy : |W.W b ω - W.W a ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (S ω)]
    calc |S ω| ^ i * |W.W b ω - W.W a ω| ^ j
        ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ i * (|S ω| + |W.W b ω - W.W a ω|) ^ j :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx i)
            (pow_le_pow_left₀ (abs_nonneg _) hy j) (by positivity) (by positivity)
      _ = (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by rw [← pow_add, hij]
  have key : ∀ (K : ℝ), 0 ≤ K → ∀ (A : Ω → ℝ), Measurable A → ∀ (i j : ℕ), i + j = 4 →
      (∀ ω, |A ω| ≤ K * |S ω| ^ i) →
      Integrable (fun ω => A ω * (W.W b ω - W.W a ω) ^ j) P := by
    intro K hK A hAm i j hij hA
    refine (hU4.const_mul K).mono ((hAm.mul (hDm.pow_const j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4)]
    calc |A ω| * |W.W b ω - W.W a ω| ^ j
        ≤ (K * |S ω| ^ i) * |W.W b ω - W.W a ω| ^ j :=
          mul_le_mul_of_nonneg_right (hA ω) (by positivity)
      _ = K * (|S ω| ^ i * |W.W b ω - W.W a ω| ^ j) := by ring
      _ ≤ K * (|S ω| + |W.W b ω - W.W a ω|) ^ 4 :=
          mul_le_mul_of_nonneg_left (hpow i j hij ω) hK
  have hi1 : Integrable (fun ω => S ω ^ 4) P :=
    LevyStochCalc.Brownian.Ito.SimplePredictable.integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) hS4
  have hi2 : Integrable
      (fun ω => (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine key (4 * C) (by positivity) (fun ω => 4 * (S ω ^ 3 * ξ ω))
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 3 1 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num]
    have := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 3, abs_nonneg (ξ ω)]
  have hi3 : Integrable
      (fun ω => (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := by
    refine key (6 * C ^ 2) (by positivity) (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2))
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2 2 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(6 : ℝ)| = 6 from by norm_num]
    have h := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 2, abs_nonneg (ξ ω),
      mul_le_mul h h (abs_nonneg (ξ ω)) hC0]
  have hi4 : Integrable
      (fun ω => (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := by
    refine key (4 * C ^ 3) (by positivity) (fun ω => 4 * (S ω * ξ ω ^ 3))
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 1 3 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num, pow_one]
    have h3 : |ξ ω| ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 3
    nlinarith [mul_nonneg (abs_nonneg (S ω)) (sub_nonneg.mpr h3)]
  have hi5 : Integrable (fun ω => ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4) P := by
    refine key (C ^ 4) (by positivity) (fun ω => ξ ω ^ 4) (hξm.pow_const 4) 0 4 rfl fun ω => ?_
    rw [abs_pow, pow_zero, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 4
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4
      = S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3
        + ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4 := fun ω => by ring
  have hi12 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  have hi123 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := hi12.add hi3
  have hi1234 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := hi123.add hi4
  have hS3ξ : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω ^ 3 * ξ ω)) := by
    have h3 : (fun ω => S ω ^ 3) = S * S * S := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul ((h3 ▸ ((hSad.mul hSad).mul hSad)).mul hξad)
  have hS2ξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) := by
    have h2 : (fun ω => S ω ^ 2) = S * S := by funext ω; simp only [Pi.mul_apply]; ring
    have h2' : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul
      ((h2 ▸ (hSad.mul hSad)).mul (h2' ▸ (hξad.mul hξad)))
  have hSξ3 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω * ξ ω ^ 3)) := by
    have h3 : (fun ω => ξ ω ^ 3) = ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul (hSad.mul (h3 ▸ ((hξad.mul hξad).mul hξad)))
  have hξ4 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 4) := by
    have h4 : (fun ω => ξ ω ^ 4) = ξ * ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact h4 ▸ (((hξad.mul hξad).mul hξad).mul hξad)
  simp_rw [hexp]
  rw [integral_add hi1234 hi5, integral_add hi123 hi4, integral_add hi12 hi3,
    integral_add hi1 hi2,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω ^ 3 * ξ ω)) hS3ξ
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 1,
    LevyStochCalc.Brownian.Ito.integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable W ℱ hℱ ha hab (Y := fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) hS2ξ2
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2,
    LevyStochCalc.Brownian.Ito.integral_increment_sq W ha hab,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω * ξ ω ^ 3)) hSξ3
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 3,
    LevyStochCalc.Brownian.Ito.integral_increment_pow_odd W ha hab (by decide : Odd 3), mul_zero, add_zero,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 4) hξ4
      (hξm.pow_const 4) 4,
    LevyStochCalc.Brownian.Ito.integral_increment_pow_four W ha hab]
  rw [integral_const_mul]
  ring

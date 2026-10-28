-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:04.376766+00:00
-- url     : https://prove2.me/submissions/129502e4-e539-4a3b-9a82-feee4d5f4cc1

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section DirectCross
/-- Borel functionals of the paths of two distinct coordinates are independent. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indepFun_comp_coord (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {φ ψ : (ℝ → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun t => (W.W i).W t ω) (fun ω => ψ fun t => (W.W j).W t ω) P :=
  (W.components_independent.indepFun hij).comp hφ hψ
/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)
/-- Increments of a Brownian motion over two intervals, the second starting after the first
ends, are uncorrelated. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {p q r v : ℝ}
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : 0 ≤ r) (hrv : r < v) :
    ∫ ω, (V.W q ω - V.W p ω) * (V.W v ω - V.W r ω) ∂P = 0 := by
  have hY : StronglyMeasurable[ℱ r] fun ω => V.W q ω - V.W p ω :=
    (((hV.measurable q).mono (ℱ.mono hqr) le_rfl).sub
      ((hV.measurable p).mono (ℱ.mono hpr) le_rfl)).stronglyMeasurable
  have hYm : Measurable fun ω => V.W q ω - V.W p ω :=
    (V.measurable_eval q).sub (V.measurable_eval p)
  have h := Ito.integral_mul_increment_pow_readable V ℱ hV hr hrv hY hYm 1
  rw [Ito.integral_increment_pow_odd V hr hrv odd_one, mul_zero] at h
  simpa only [pow_one] using h
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_zero (a h : ℝ) : affineGrid a h 0 = a := by simp [affineGrid]
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_succ_sub (a h : ℝ) (k : ℕ) : affineGrid a h (k + 1) - affineGrid a h k = h := by
  simp only [affineGrid, Nat.cast_succ]; ring
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono {a h : ℝ} (hh : 0 ≤ h) {k l : ℕ} (hkl : k ≤ l) :
    affineGrid a h k ≤ affineGrid a h l := by
  simp only [affineGrid]
  have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
  nlinarith
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    affineGrid a h k < affineGrid a h (k + 1) := by
  have := affineGrid_succ_sub a h k
  linarith
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.le_affineGrid {a h : ℝ} (hh : 0 ≤ h) (k : ℕ) : a ≤ affineGrid a h k := by
  simpa [affineGrid_zero] using affineGrid_mono (a := a) hh (Nat.zero_le k)
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ affineGrid a h k :=
  ha.trans (le_affineGrid hh k)
/-- The second moment of the sum of cross products of the increments of two distinct
coordinates over the cells of a uniform grid. -/
lemma solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by
  have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
  -- the functional on path space picking out the product of two increments
  have hφ : ∀ k l : ℕ, Measurable fun path : ℝ → ℝ =>
      (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k))
        * (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l)) := fun k l => by
    fun_prop
  have hind : ∀ k l : ℕ, IndepFun
      (fun ω => ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
      (fun ω => ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P :=
    fun k l => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indepFun_comp_coord W hij (hφ k l) (hφ k l)
  have hint2 : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (k l : ℕ), Integrable
      (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P := fun V k l =>
    MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 k) (hglt k).le)
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 l) (hglt l).le)
  have hcov : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P), LevyStochCalc.Brownian.IsBrownianFiltration V ℱ → ∀ k l : ℕ,
      ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P
        = if k = l then h else 0 := by
    intro V hV k l
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [if_neg hkl.ne]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl) (hg0 l) (hglt l)
    · have hsq := LevyStochCalc.Brownian.Ito.integral_increment_sq V (hg0 k) (hglt k)
      rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_succ_sub] at hsq
      have hsq' : ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ∂P
          = ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
      rw [if_pos rfl, hsq', hsq]
    · rw [if_neg hlk.ne']
      rw [show (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
          = fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
            * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) from
        funext fun ω => mul_comm _ _]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk) (hg0 k) (hglt k)
  have hterm : ∀ k l : ℕ,
      ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = if k = l then h ^ 2 else 0 := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    have hmul := (hind k l).integral_mul_eq_mul_integral
      (hint2 (W.W i) k l).1 (hint2 (W.W j) k l).1
    rw [show ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = (∫ ω, ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P)
        * ∫ ω, ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P from hmul,
      hcov (W.W i) (hcoord i) k l, hcov (W.W j) (hcoord j) k l]
    by_cases hkl : k = l
    · simp [hkl, sq]
    · simp [hkl]
  have hint : ∀ k l : ℕ, Integrable
      (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))) P := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    exact (hind k l).integrable_mul (hint2 (W.W i) k l) (hint2 (W.W j) k l)
  have hexp : (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2)
      = fun ω => ∑ k ∈ Finset.range m, ∑ l ∈ Finset.range m,
        (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun x hx => if_pos hx, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

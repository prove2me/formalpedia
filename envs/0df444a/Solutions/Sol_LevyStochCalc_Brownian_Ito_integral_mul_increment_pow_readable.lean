-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:11.186628+00:00
-- url     : https://prove2.me/submissions/46cfa41c-d2ea-4d42-b26e-48522a0e4f68

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Increments
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- A random variable measurable before `a` is independent of every power of the increment
over `(a, b]`. -/
theorem solution (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by
  have hΔ : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hindepσ := hℱ.indep ha hab
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ ℱ a := hY.measurable.comap_le
  have hIF : ProbabilityTheory.IndepFun Y (fun ω => W.W b ω - W.W a ω) P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at hindepσ
    exact hindepσ u v (hYcomap u hu) hv
  have hIF' : ProbabilityTheory.IndepFun Y (fun ω => (W.W b ω - W.W a ω) ^ m) P :=
    hIF.comp measurable_id (measurable_id.pow_const m)
  exact hIF'.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
    (hΔ.pow_const m).aestronglyMeasurable

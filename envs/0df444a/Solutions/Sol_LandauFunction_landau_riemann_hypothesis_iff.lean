-- Prove2me | solution 1 for LandauFunction.landau_riemann_hypothesis_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-20T23:56:13.863918+00:00
-- url     : https://prove2.me/submissions/fa133f00-e2f6-4f2f-99d4-afe3e88c6536

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral
import Theorems.Thm_LandauFunction_landau_of_riemannHypothesis
import Theorems.Thm_LandauFunction_riemannHypothesis_of_landau

/-- **Landau's criterion for the Riemann hypothesis** (Massias–Nicolas–Robin): the two directions
are `LandauFunction.riemannHypothesis_of_landau` and `LandauFunction.landau_of_riemannHypothesis`. -/
theorem solution :
    (∀ᶠ n : ℕ in Filter.atTop,
        Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n)) ↔
      RiemannHypothesis :=
  ⟨LandauFunction.riemannHypothesis_of_landau, LandauFunction.landau_of_riemannHypothesis⟩

-- Prove2me | solution 1 for ItoLemma.coordDeriv_norm_le_fderiv_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:51:33.926728+00:00
-- url     : https://prove2.me/submissions/39b841d6-e312-494a-a4d6-4356f71e4c54

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Evaluating a Fréchet derivative along one coordinate basis
vector cannot exceed the operator norm of the derivative. -/
theorem solution {n : ℕ}
    (g : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (p : Fin n) (z : Fin n → ℝ) :
    ‖LevyStochCalc.coordDeriv g p z‖ ≤ ‖g z‖ := by
  unfold LevyStochCalc.coordDeriv
  have h := (g z).le_opNorm (Pi.single p (1 : ℝ))
  simpa only [Pi.norm_single, norm_one, mul_one] using h

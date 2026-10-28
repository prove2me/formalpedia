-- Prove2me | solution 1 for ItoLemma.fin_two_coordinate_product_gradient_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:44:23.602055+00:00
-- url     : https://prove2.me/submissions/353a09b6-fd24-43f6-9802-08802a2bf072

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The gradient of the coordinate product exchanges the two coordinates. -/
theorem solution (z : Fin 2 → ℝ) :
    LevyStochCalc.coordDeriv
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (0 : Fin 2) z = z 1 ∧
    LevyStochCalc.coordDeriv
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (1 : Fin 2) z = z 0 := by
  constructor <;> simp [LevyStochCalc.coordDeriv]

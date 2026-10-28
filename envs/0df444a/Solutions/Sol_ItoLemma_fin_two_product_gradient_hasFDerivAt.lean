-- Prove2me | solution 1 for ItoLemma.fin_two_product_gradient_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:51:28.981009+00:00
-- url     : https://prove2.me/submissions/2dffd5a4-3072-4c20-ba82-71e87d679c33

import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The gradient of the two-coordinate product has the constant
symmetric mixed Hessian, represented as a continuous linear map. -/
theorem solution (z : Fin 2 → ℝ) :
    HasFDerivAt
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (((ContinuousLinearMap.proj (0 : Fin 2) :
            (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)) +
        ((ContinuousLinearMap.proj (1 : Fin 2) :
            (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))) z := by
  let L₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 2)
  let L₁ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (1 : Fin 2)
  let H : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
    L₀.smulRight L₁ + L₁.smulRight L₀
  change HasFDerivAt (fun x => H x) H z
  exact H.hasFDerivAt

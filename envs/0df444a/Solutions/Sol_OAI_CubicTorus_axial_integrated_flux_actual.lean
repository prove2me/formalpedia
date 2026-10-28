-- Prove2me | solution 1 for OAI.CubicTorus.axial_integrated_flux_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:17:14.836965+00:00
-- url     : https://prove2.me/submissions/e97ecc74-8a63-4bd8-8c71-036fba0a974d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_axialSurface_density_eq_flux
import Theorems.Thm_OAI_CubicTorus_axial_integrated_flux

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SharpSectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_integrated_flux_actual_oai {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (actualAxialFlux E μ H i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  have hh := axial_integrated_flux i ha
  rw [hμ.1] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  filter_upwards [axialSurface_density_eq_flux hE hH i] with t ht
  rw [←ht]
  rfl

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.axial_integrated_flux_actual_oai := @OAI.CubicTorus.axial_integrated_flux_actual_oai

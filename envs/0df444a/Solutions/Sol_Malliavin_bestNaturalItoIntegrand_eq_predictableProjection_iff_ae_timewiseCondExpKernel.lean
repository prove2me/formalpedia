-- Prove2me | solution 1 for Malliavin.bestNaturalItoIntegrand_eq_predictableProjection_iff_ae_timewiseCondExpKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:59.004328+00:00
-- url     : https://prove2.me/submissions/67dcb791-6501-48a3-9dd0-d80a2e10345e

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) ↔
      ∀ᵐ t ∂nonnegativeLebesgueMeasure,
        (fun w ↦
          (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) :
            ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
          fun w ↦ ∫ w',
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F) : ℝ≥0 × W → ℝ) (t, w')
            ∂condExpKernel P (𝓅 t) w := by
  subst 𝓅
  constructor
  · intro hBest
    rw [hBest]
    have hsection :=
      timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural
        hB hsm generated
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))
    filter_upwards [hsection, nonnegativeLebesgueMeasure.ae_ne 0] with t ht ht0
    exact ht (pos_iff_ne_zero.mpr ht0)
  · intro hTimewise
    exact
      bestNaturalItoIntegrand_eq_predictableProjection_of_ae_timewiseCondExpKernel
        hB coordinate coordinate_apply generated hsm rfl F hTimewise
end Malliavin

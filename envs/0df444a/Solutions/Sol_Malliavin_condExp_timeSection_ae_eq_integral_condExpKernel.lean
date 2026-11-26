-- Prove2me | solution 1 for Malliavin.condExp_timeSection_ae_eq_integral_condExpKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:06.533898+00:00
-- url     : https://prove2.me/submissions/ef59212b-4bdf-4b17-bb19-4afe447b6352

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_memLp_timeSection_ae


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      P[(fun ω ↦ U (t, ω)) | 𝓕 t] =ᵐ[P]
        fun ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω := by
  filter_upwards [memLp_timeSection_ae U] with t ht
  exact condExp_ae_eq_integral_condExpKernel (𝓕.le t) (ht.integrable one_le_two)
end Malliavin

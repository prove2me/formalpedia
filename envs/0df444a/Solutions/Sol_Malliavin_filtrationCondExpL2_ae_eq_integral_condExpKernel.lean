-- Prove2me | solution 1 for Malliavin.filtrationCondExpL2_ae_eq_integral_condExpKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:42.413198+00:00
-- url     : https://prove2.me/submissions/3ad03042-3fa2-44e1-9c83-76c2a50cd4a6

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_filtrationCondExpL2_ae_eq_condExp


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
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P]
      fun ω ↦ ∫ y, F y ∂condExpKernel P (𝓕 t) ω :=
  (filtrationCondExpL2_ae_eq_condExp 𝓕 t F).trans
    (condExp_ae_eq_integral_condExpKernel (𝓕.le t) ((Lp.memLp F).integrable one_le_two))
end Malliavin

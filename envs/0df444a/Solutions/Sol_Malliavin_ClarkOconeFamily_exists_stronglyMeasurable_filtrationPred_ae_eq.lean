-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.exists_stronglyMeasurable_filtrationPred_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:09:59.20744+00:00
-- url     : https://prove2.me/submissions/b0732fe5-a9fd-4ccb-9dd5-1865cc0da64d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_ClarkOconeFamily_condExp_brownian_filtrationPred

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace _root_.Malliavin.ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    ∃ Z : W → ℝ, StronglyMeasurable[filtrationPred 𝓕 t] Z ∧ B t =ᵐ[P] Z :=
  ⟨P[B t | filtrationPred 𝓕 t], stronglyMeasurable_condExp,
    (C.condExp_brownian_filtrationPred hat).symm⟩
end _root_.Malliavin.ClarkOconeFamily
end Malliavin

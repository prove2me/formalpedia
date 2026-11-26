-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_brownianChaosTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:31.946822+00:00
-- url     : https://prove2.me/submissions/4afb756a-a49d-41b5-b23d-f612eef3aec5

import Definitions.Def_Malliavin_BrownianChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_naturalItoRange
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_zero_le_centeredPartCLM_ker
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_of_total_submodules


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (htotal : BrownianChaosTotal hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  apply Malliavin.naturalMartingaleRepresentation_of_total_submodules hB hsm hnat
    (fun n => (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
  · exact htotal
  · exact brownianHomogeneousChaos_zero_le_centeredPartCLM_ker hB
  · intro n hn
    exact brownianHomogeneousChaos_le_naturalItoRange hB hsm hnat n hn
end Malliavin.BrownianIteratedConstruction

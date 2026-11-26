-- Prove2me | solution 1 for Malliavin.predictableProjection_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:07.048401+00:00
-- url     : https://prove2.me/submissions/9d704e0a-2042-4e09-8454-df8bafe285c6

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableProjection (P := P) 𝓕 (deterministicTimeEmbedding g) =
      deterministicPredictableEmbedding 𝓕 g := by
  have : Fact (𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓕⟩
  unfold predictableProjection condExpL2
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (deterministicPredictableEmbedding (P := P) 𝓕 g)
end Malliavin

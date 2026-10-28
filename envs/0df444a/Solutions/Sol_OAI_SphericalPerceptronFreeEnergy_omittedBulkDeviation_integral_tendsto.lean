-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:28:38.544243+00:00
-- url     : https://prove2.me/submissions/c9d9b234-7014-40ca-a71e-c01fa5839f8c

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulkDeviationAt_integral_tendsto

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkGoodParameters
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma omittedBulkDeviation_integral_tendsto_oai {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n => ∫ v, omittedBulkDeviation α f n p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  apply bulkDeviationAt_integral_tendsto _ f hα _ p
  intro n
  calc
    _ ≤ (patternCount α (n+1):ℝ) := by exact_mod_cast Nat.sub_le (patternCount α (n+1)) 2
    _ ≤ α*(n+1:ℕ) := Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto_oai := @OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto_oai

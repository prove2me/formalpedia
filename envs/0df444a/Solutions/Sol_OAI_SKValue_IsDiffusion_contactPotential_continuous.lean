-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.contactPotential_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:15.926681+00:00
-- url     : https://prove2.me/submissions/44adb498-bab5-4ba3-ab71-9c104a72ff25

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_moment_difference_integrable

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactVariations
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma IsDiffusion.contactPotential_continuous_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ContinuousOn (contactPotential W γ X) (Icc (0 : ℝ) 1) := by
  change ContinuousOn (fun s : ℝ ↦ ∫ t in s..1,gradientMoment W γ X t-t) (Icc (0 : ℝ) 1)
  have hi : IntegrableOn (fun t ↦ gradientMoment W γ X t-t) (uIcc (0 : ℝ) 1) volume := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ)≤1)).mp
      hX.moment_difference_integrable
  have hc : ContinuousOn (fun s : ℝ ↦ ∫ t in s..1,gradientMoment W γ X t-t) (uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval_left hi
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hc

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.contactPotential_continuous_oai := @OAI.SKValue.IsDiffusion.contactPotential_continuous_oai

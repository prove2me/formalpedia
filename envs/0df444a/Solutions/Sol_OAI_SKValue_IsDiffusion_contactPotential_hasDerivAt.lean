-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:40.091018+00:00
-- url     : https://prove2.me/submissions/15eb5295-67d8-4f86-bd7d-c1f9412be639

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_gradientMoment_continuous
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

lemma IsDiffusion.contactPotential_hasDerivAt_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) :
    HasDerivAt (contactPotential W γ X) (s-gradientMoment W γ X s) s := by
  change HasDerivAt (fun u : ℝ ↦ ∫ t in u..1,gradientMoment W γ X t-t) _ s
  have hc : ContinuousOn (fun t ↦ gradientMoment W γ X t-t) (Ico (0 : ℝ) 1) :=
    hX.gradientMoment_continuous.sub continuousOn_id
  have hns : Ico (0 : ℝ) 1∈𝓝 s := mem_of_superset (Ioo_mem_nhds hs.1 hs.2) Ioo_subset_Ico_self
  have hi : IntervalIntegrable (fun t ↦ gradientMoment W γ X t-t) volume s 1 :=
    hX.moment_difference_integrable.mono_set (by
      rw [uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
      exact Icc_subset_Icc hs.1.le le_rfl)
  have hh : HasDerivAt (fun u : ℝ ↦ ∫ t in u..1,gradientMoment W γ X t-t)
      (-(gradientMoment W γ X s-s)) s := intervalIntegral.integral_hasDerivAt_left hi
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Ico_self) s hs)
        (hc.continuousAt hns)
  simpa only [neg_sub] using hh

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt_oai := @OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt_oai

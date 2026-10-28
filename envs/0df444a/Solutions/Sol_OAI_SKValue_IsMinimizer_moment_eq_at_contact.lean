-- Prove2me | solution 1 for OAI.SKValue.IsMinimizer.moment_eq_at_contact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:00:55.603766+00:00
-- url     : https://prove2.me/submissions/1125758f-5107-46cf-9803-b96dadd43b46

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_contactPotential_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsMinimizer_contactPotential_nonneg

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

lemma IsMinimizer.moment_eq_at_contact_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) (hG : contactPotential W γ X s=0) :
    gradientMoment W γ X s=s := by
  have hm : IsLocalMin (contactPotential W γ X) s := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    rw [hG]
    exact hγ.contactPotential_nonneg hX ⟨ht.1.le,ht.2.le⟩
  have hz := hm.hasDerivAt_eq_zero (hX.contactPotential_hasDerivAt hs)
  linarith

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsMinimizer.moment_eq_at_contact_oai := @OAI.SKValue.IsMinimizer.moment_eq_at_contact_oai

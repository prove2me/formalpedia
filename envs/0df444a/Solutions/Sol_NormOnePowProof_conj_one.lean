-- Prove2me | solution 1 for NormOnePowProof.conj_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:13.190665+00:00
-- url     : https://prove2.me/submissions/dcac43f9-7a66-4536-bde1-80c3e6dbf1be

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
import Theorems.Thm_NormOnePowProof_map_mem_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
namespace NormOnePowProof
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) :
    ∀ x, x ∈ (1 : Submodule (𝓞 E) E) ↔ c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x
  refine ⟨map_mem_one c x, fun hx => ?_⟩
  have := map_mem_one c (c x) hx
  rwa [hc] at this
end NormOnePowProof

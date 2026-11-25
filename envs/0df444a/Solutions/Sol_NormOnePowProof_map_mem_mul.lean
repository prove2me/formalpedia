-- Prove2me | solution 1 for NormOnePowProof.map_mem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:44.263221+00:00
-- url     : https://prove2.me/submissions/93e07358-d8bf-449f-89fa-8d2da870ea6b

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal

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
theorem _root_.solution (c : E →+* E) {P P' Q Q' : Submodule (𝓞 E) E}
    (h : ∀ p ∈ P, c p ∈ Q) (h' : ∀ p ∈ P', c p ∈ Q') : ∀ w ∈ P * P', c w ∈ Q * Q' := by
  intro w hw
  refine Submodule.mul_induction_on (C := fun w => c w ∈ Q * Q') hw ?_ ?_
  · intro p hp q hq
    rw [map_mul]
    exact Submodule.mul_mem_mul (h p hp) (h' q hq)
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
end NormOnePowProof

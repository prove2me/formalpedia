-- Prove2me | solution 1 for NormOnePowProof.map_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:45.874261+00:00
-- url     : https://prove2.me/submissions/936a41c1-e8e1-43f7-a595-cf5e2fcfa402

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
theorem _root_.solution (c : E →+* E) : ∀ x ∈ (1 : Submodule (𝓞 E) E), c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨σ c y, rfl⟩
end NormOnePowProof

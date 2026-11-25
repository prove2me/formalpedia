-- Prove2me | solution 1 for GroundTheory.LocalField.spanZ_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:40.900993+00:00
-- url     : https://prove2.me/submissions/56d380e0-ba16-43b5-9f60-91eb52b89d8b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]
variable (E : Subgroup G → Prop)
variable {E}
namespace GroundTheory.LocalField
theorem _root_.solution {E' : Subgroup G → Prop} (h : ∀ K, E K → E' K) : spanZ E ≤ spanZ E' :=
  Submodule.span_mono fun _ ⟨K, hK, l, hf⟩ ↦ ⟨K, h K hK, l, hf⟩
end GroundTheory.LocalField

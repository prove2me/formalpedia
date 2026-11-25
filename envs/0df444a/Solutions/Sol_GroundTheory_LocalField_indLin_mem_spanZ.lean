-- Prove2me | solution 1 for GroundTheory.LocalField.indLin_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:06.650053+00:00
-- url     : https://prove2.me/submissions/630f5260-87a3-4ba3-93df-b46dfc084f94

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
theorem _root_.solution {K : Subgroup G} (hK : E K) (l : K →* ℂˣ) : indLin K l ∈ spanZ E :=
  Submodule.subset_span ⟨K, hK, l, rfl⟩
end GroundTheory.LocalField

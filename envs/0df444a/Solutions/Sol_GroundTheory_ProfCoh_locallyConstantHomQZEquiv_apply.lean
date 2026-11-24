-- Prove2me | solution 1 for GroundTheory.ProfCoh.locallyConstantHomQZEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:48.166795+00:00
-- url     : https://prove2.me/submissions/7e81c5db-9b2c-4fe0-88b5-4e968da25687

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_CharactersDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
variable {G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (χ : locallyConstantHom G (AddCircle (1 : ℚ)))
    (g : Additive G) :
    locallyConstantHomQZEquiv G χ g = QZ.toAddCircle.symm (χ.1 g) :=
  rfl
end GroundTheory.ProfCoh

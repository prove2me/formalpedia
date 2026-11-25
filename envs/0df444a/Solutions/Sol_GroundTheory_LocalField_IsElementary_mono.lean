-- Prove2me | solution 1 for GroundTheory.LocalField.IsElementary.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:31.514908+00:00
-- url     : https://prove2.me/submissions/608c2904-49c7-4d1e-b85d-fbd0bf45179e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono


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
universe u
variable {G : Type u} [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.LocalField
namespace IsElementary
theorem _root_.solution {H L : Subgroup G} (hH : IsElementary H) (hLH : L ≤ H) : IsElementary L :=
  let ⟨p, hp, hHp⟩ := hH
  ⟨p, hp, hHp.mono hLH⟩
end IsElementary
end GroundTheory.LocalField

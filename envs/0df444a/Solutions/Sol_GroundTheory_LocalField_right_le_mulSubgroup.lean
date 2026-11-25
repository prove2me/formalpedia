-- Prove2me | solution 1 for GroundTheory.LocalField.right_le_mulSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:48.144809+00:00
-- url     : https://prove2.me/submissions/b3b1bb4f-6215-48ae-8068-5882a9c7b61d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime

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
variable {G : Type u} [Group G]
namespace GroundTheory.LocalField
theorem _root_.solution {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    P ≤ mulSubgroup C P hcomm := fun y hy ↦ ⟨1, C.one_mem, y, hy, (one_mul y).symm⟩
end GroundTheory.LocalField

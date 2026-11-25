-- Prove2me | solution 1 for GroundTheory.LocalField.isPGroup_sylowCent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:45.96206+00:00
-- url     : https://prove2.me/submissions/6b14e5e7-467a-4781-b1cc-0d4dd55fa215

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
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit [Fintype G] hp
variable (p x)
namespace GroundTheory.LocalField
theorem _root_.solution : IsPGroup p (sylowCent p x) :=
  (Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))).isPGroup'.map _
end GroundTheory.LocalField

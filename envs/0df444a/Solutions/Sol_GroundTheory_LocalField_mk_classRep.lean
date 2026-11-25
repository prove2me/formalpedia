-- Prove2me | solution 1 for GroundTheory.LocalField.mk_classRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:24.443035+00:00
-- url     : https://prove2.me/submissions/54bf230e-b3c7-413b-b986-1db98825af06

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
namespace GroundTheory.LocalField
theorem _root_.solution (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  Classical.choose_spec c.exists_rep
end GroundTheory.LocalField

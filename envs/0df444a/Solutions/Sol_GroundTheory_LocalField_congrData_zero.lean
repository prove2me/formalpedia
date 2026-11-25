-- Prove2me | solution 1 for GroundTheory.LocalField.congrData_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:23:41.668893+00:00
-- url     : https://prove2.me/submissions/0509ec5b-8f20-4efa-98cb-047fa0e6410c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal

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
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution : CongrData ζ N s a (0 : G → ℂ) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, fun i ↦ i.elim, by simp, by simp⟩
end GroundTheory.LocalField

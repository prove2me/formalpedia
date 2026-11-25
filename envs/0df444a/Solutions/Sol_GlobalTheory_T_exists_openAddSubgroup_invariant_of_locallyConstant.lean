-- Prove2me | solution 1 for GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:58.091622+00:00
-- url     : https://prove2.me/submissions/a01e4760-fde1-4fb4-a312-31bfed4ea1da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSub
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSubStatement
import Theorems.Thm_GlobalTheory_locallyConstant_compactSupport_invariant_openAddSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g → ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  first | exact @GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | exact GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | (intros; apply GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup <;> assumption)
end _root_.GlobalTheory.T

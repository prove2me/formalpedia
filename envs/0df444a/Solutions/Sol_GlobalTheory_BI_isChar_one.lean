-- Prove2me | solution 1 for GlobalTheory.BI.isChar_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:37.458163+00:00
-- url     : https://prove2.me/submissions/9bbb03da-c9c3-4960-a24c-c873d7ac77ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] :
    IsChar K L (fun _ : G => (1 : L)) := by
  refine ⟨1, Representation.trivial K G (Fin 1 → K), fun g => ?_⟩
  simp [Representation.character, Representation.trivial]
end GlobalTheory.BI

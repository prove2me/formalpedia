-- Prove2me | solution 1 for GlobalTheory.dualSubmodule_le_dualSubmodule_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:48.711943+00:00
-- url     : https://prove2.me/submissions/f9e5fb80-c517-4185-b6fe-cb404c7052e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
namespace GlobalTheory
theorem _root_.solution (B : LinearMap.BilinForm ℚ V)
    {M N : Submodule ℤ V} (h : M ≤ N) : B.dualSubmodule N ≤ B.dualSubmodule M :=
  fun _ hx y hy => hx y (h hy)
end GlobalTheory

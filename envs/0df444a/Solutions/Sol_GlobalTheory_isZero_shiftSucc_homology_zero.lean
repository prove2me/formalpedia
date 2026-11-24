-- Prove2me | solution 1 for GlobalTheory.isZero_shiftSucc_homology_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:36.035012+00:00
-- url     : https://prove2.me/submissions/82d6f993-004c-4a1a-b722-c4d043335b1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IsZero ((shiftSucc K).homology 0) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_shiftSucc_X_zero K)
end GlobalTheory

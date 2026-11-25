-- Prove2me | solution 1 for GlobalTheory.Cube.res_upperFace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:44.416773+00:00
-- url     : https://prove2.me/submissions/0b7c1285-e604-48a8-949c-aa3c40d66156

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
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
variable (e : κ ↪o ι) (i : ι)
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) {s t : Finset κ} (h : s ⊆ t) :
    res (upperFace e i A) h =
      res A (Finset.insert_subset_insert i (Finset.map_subset_map.2 h)) := rfl
end GlobalTheory.Cube

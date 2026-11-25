-- Prove2me | solution 1 for GlobalTheory.Cube.sliceSnd_lowerFace_lastTwoEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:36.865362+00:00
-- url     : https://prove2.me/submissions/88c73426-f186-4fda-b7a0-9e12e4959493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Theorems.Thm_GlobalTheory_Cube_map_lastTwoEmb

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
open Cube
variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] {R : Type u} [Ring R]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R) (t : Finset κ) :
    sliceSnd (lowerFace (lastTwoEmb ι κ ν) A) t = sliceSnd A (sumVertex ∅ t) :=
  comap_congr (fun _ _ h => Finset.map_subset_map.2 (sumVertex_mono (subset_refl t) h)) _
    (fun w => Cube.map_lastTwoEmb t w) A
end Cube
end GlobalTheory

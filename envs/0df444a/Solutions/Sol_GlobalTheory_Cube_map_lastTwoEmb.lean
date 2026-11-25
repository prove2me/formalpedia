-- Prove2me | solution 1 for GlobalTheory.Cube.map_lastTwoEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:23.015567+00:00
-- url     : https://prove2.me/submissions/c1586ac7-efc3-48d5-b21d-85ce48954dd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard

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
theorem _root_.solution (t : Finset κ) (w : Finset ν) :
    (sumVertex t w).map (lastTwoEmb ι κ ν).toEmbedding =
      sumVertex (sumVertex (∅ : Finset ι) t) w := by
  rw [← Cube.map_lastTwoEmb_union, Finset.map_empty, Finset.union_empty]
end Cube
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.Cube.upperFace_obj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:20.944674+00:00
-- url     : https://prove2.me/submissions/2db2232e-eca5-48c1-8075-b7bd385776fa

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
theorem _root_.solution (A : Cube.{v} ι R) (s : Finset κ) :
    (upperFace e i A).obj s = A.obj (insert i (s.map e.toEmbedding)) := rfl
end GlobalTheory.Cube

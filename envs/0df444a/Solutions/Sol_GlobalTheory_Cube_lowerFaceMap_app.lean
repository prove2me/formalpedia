-- Prove2me | solution 1 for GlobalTheory.Cube.lowerFaceMap_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:10.904026+00:00
-- url     : https://prove2.me/submissions/5f0ae039-c5a4-425d-919c-02bd84fad3dc

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
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B) (s : Finset κ) :
    (lowerFaceMap e φ).app s = φ.app (s.map e.toEmbedding) := rfl
end GlobalTheory.Cube

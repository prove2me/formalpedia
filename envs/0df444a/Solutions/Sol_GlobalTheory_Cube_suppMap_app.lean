-- Prove2me | solution 1 for GlobalTheory.Cube.suppMap_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:48.86922+00:00
-- url     : https://prove2.me/submissions/c7d45fdc-b208-433d-8b19-6d3949313260

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
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
variable {A B : Cube.{v} ι R} {P P' : Set (Finset ι)} {hP : P.OrdConnected}
  {hP' : P'.OrdConnected}
namespace GlobalTheory.Cube
theorem _root_.solution (φ : A ⟶ B) (h) (s : Finset ι) :
    ((suppMap φ hP hP' h).app s).hom = suppMapApp φ hP hP' s := rfl
end GlobalTheory.Cube

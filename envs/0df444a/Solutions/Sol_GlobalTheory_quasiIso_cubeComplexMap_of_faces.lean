-- Prove2me | solution 1 for GlobalTheory.quasiIso_cubeComplexMap_of_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:23:50.566363+00:00
-- url     : https://prove2.me/submissions/3a89f231-b9a4-4f98-80ea-7d96fa3d8373

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_quasiIso____9254fd874b84

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
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he
namespace GlobalTheory
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B)
    (h₀ : QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)))
    (h₁ : QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ))) : QuasiIso (cubeComplexMap φ) :=
  quasiIso_τ₂ (cubeFaceSequenceMap he φ) (cubeFaceSequence_shortExact he A)
    (cubeFaceSequence_shortExact he B) ((quasiIso_extendMap_iff _ _).2 h₁) h₀
end GlobalTheory

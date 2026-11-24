-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_zero_iff_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:04.444389+00:00
-- url     : https://prove2.me/submissions/bd06084e-b0f8-4559-b5fa-7cd208370367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_isZero_shiftSucc_homology_zero
import Theorems.Thm_P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004

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
theorem _root_.solution (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 0 ↔ Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) 0) := by
  have hS := cubeFaceSequence_shortExact he A
  rw [← mono_cubeFaceSequence_δ_iff he, exactAt_iff_isZero_homology]
  exact ((hS.homology_exact₂ 0).isZero_X₂_iff.trans
    (and_iff_right ((isZero_shiftSucc_homology_zero _).eq_of_src _ _))).trans
    (hS.homology_exact₃ 0 (0 + 1) rfl).mono_g_iff.symm
end GlobalTheory

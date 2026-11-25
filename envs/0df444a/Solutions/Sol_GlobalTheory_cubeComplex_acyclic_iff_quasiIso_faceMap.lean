-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_iff_quasiIso_faceMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:32.392268+00:00
-- url     : https://prove2.me/submissions/0a4942ae-7b14-43b5-9898-101b4dc92aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_zero_iff_faces
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff_faces

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
    (cubeComplex A).Acyclic ↔ QuasiIso (cubeComplexMap (Cube.faceMap e i A)) := by
  constructor
  · intro h
    rw [quasiIso_iff]
    intro p
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := ((cubeComplex_exactAt_succ_iff_faces he A p).1 (h _)).1
    have : Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by
      cases p with
      | zero => exact (cubeComplex_exactAt_zero_iff_faces he A).1 (h _)
      | succ p => exact ((cubeComplex_exactAt_succ_iff_faces he A p).1 (h _)).2
    apply isIso_of_mono_of_epi
  · intro h p
    cases p with
    | zero => exact (cubeComplex_exactAt_zero_iff_faces he A).2 inferInstance
    | succ p =>
      exact (cubeComplex_exactAt_succ_iff_faces he A p).2 ⟨inferInstance, inferInstance⟩
end GlobalTheory

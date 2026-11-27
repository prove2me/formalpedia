-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_of_faces_of_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:48.418888+00:00
-- url     : https://prove2.me/submissions/81948981-d444-46f7-b286-66542de1dbcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_quasiIso_faceMap
import Theorems.Thm_GlobalTheory_quasiIsoAt_zero_cubeComplexMap_iff

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
    (h₀ : ∀ p, (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : ∀ p, (cubeComplex (Cube.upperFace e i A)).ExactAt (p + 1))
    (h : Set.BijOn ((Cube.faceMap e i A).app ∅).hom
      (LinearMap.ker (Cube.aug (Cube.lowerFace e A)))
      (LinearMap.ker (Cube.aug (Cube.upperFace e i A)))) : (cubeComplex A).Acyclic := by
  rw [cubeComplex_acyclic_iff_quasiIso_faceMap he, quasiIso_iff]
  intro p
  cases p with
  | zero => exact (quasiIsoAt_zero_cubeComplexMap_iff _).2 h
  | succ p => exact (quasiIsoAt_iff_exactAt _ _ (h₀ p)).2 (h₁ p)
end GlobalTheory

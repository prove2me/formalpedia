-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_of_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:45.147493+00:00
-- url     : https://prove2.me/submissions/fd14b16a-fcb5-4abd-9341-498df5759b54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_quasiIso_faceMap

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
theorem _root_.solution (A : Cube.{v} ι R)
    (h₀ : (cubeComplex (Cube.lowerFace e A)).Acyclic)
    (h₁ : (cubeComplex (Cube.upperFace e i A)).Acyclic) : (cubeComplex A).Acyclic := by
  rw [cubeComplex_acyclic_iff_quasiIso_faceMap he, quasiIso_iff]
  exact fun p => (quasiIsoAt_iff_exactAt _ p (h₀ p)).2 (h₁ p)
end GlobalTheory

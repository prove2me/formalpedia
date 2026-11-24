-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_succ_of_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:03.780731+00:00
-- url     : https://prove2.me/submissions/f29558e9-3081-4c47-9e24-06fd5cd7e116

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
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ)
    (h₀ : (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : (cubeComplex (Cube.upperFace e i A)).ExactAt p) : (cubeComplex A).ExactAt (p + 1) :=
  (cubeFaceSequence_shortExact he A).exactAt_X₂ (p + 1)
    ((extend_exactAt_iff _ _ (succEmbedding_f p)).2 h₁) h₀
end GlobalTheory

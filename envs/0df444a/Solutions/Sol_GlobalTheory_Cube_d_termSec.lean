-- Prove2me | solution 1 for GlobalTheory.Cube.d_termSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:45.522938+00:00
-- url     : https://prove2.me/submissions/0adf6c24-1f6e-454c-bdc8-c8e44648d57e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_Cube_termUpper_d_zero

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
  {e : κ ↪o ι} {i : ι}
variable (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
include he
namespace GlobalTheory.Cube
theorem _root_.solution {p : ℕ} (y : Term (lowerFace e A) p) :
    d A p (termSec e i A p y) = termSec e i A (p + 1) (d (lowerFace e A) p y) +
      termIncl e i A p ((-1 : ℤ) ^ p • termMap (faceMap e i A) p y) := by
  refine term_ext_faces he A ?_
    (by simp [termLower_d, termLower_termSec he, termLower_termIncl he])
  cases p with
  | zero => simp [termUpper_d_zero, termLower_termSec he]
  | succ p => simp [termUpper_d, termLower_termSec he]
end GlobalTheory.Cube

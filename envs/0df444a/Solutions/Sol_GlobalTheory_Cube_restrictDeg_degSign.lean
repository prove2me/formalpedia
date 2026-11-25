-- Prove2me | solution 1 for GlobalTheory.Cube.restrictDeg_degSign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:38.713975+00:00
-- url     : https://prove2.me/submissions/d90ade85-2952-4372-98b8-4e25c76fc889

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_apply
import Theorems.Thm_GlobalTheory_Cube_degSign_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A p (degSign A x) = (-1 : ℤ) ^ p • restrictDeg A p x := by
  funext s
  rw [restrictDeg_apply, degSign_apply, s.2]
  rfl
end GlobalTheory.Cube

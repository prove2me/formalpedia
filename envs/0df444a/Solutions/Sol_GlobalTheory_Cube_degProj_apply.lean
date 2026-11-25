-- Prove2me | solution 1 for GlobalTheory.Cube.degProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:21.552078+00:00
-- url     : https://prove2.me/submissions/07593556-2a41-4e44-b973-1bb7488e68cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_extend_apply_of_ne


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
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) (s : Finset ι) :
    degProj A p x s = if s.card = p then x s else 0 := by
  by_cases h : s.card = p
  · rw [if_pos h]; exact extend_apply_of_eq A _ h
  · rw [if_neg h]; exact extend_apply_of_ne A _ h
end GlobalTheory.Cube

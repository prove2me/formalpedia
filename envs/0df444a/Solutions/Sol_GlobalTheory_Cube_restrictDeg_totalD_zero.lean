-- Prove2me | solution 1 for GlobalTheory.Cube.restrictDeg_totalD_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:26.248545+00:00
-- url     : https://prove2.me/submissions/90c45191-f380-4ffa-bb53-dbb6a43a525c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_apply

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
variable [LinearOrder ι]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) (x : ∀ s, A.obj s) :
    restrictDeg A 0 (totalD A x) = 0 := by
  funext ⟨t, ht⟩
  obtain rfl := Finset.card_eq_zero.1 ht
  rw [restrictDeg_apply, totalD_apply]
  simp
end GlobalTheory.Cube

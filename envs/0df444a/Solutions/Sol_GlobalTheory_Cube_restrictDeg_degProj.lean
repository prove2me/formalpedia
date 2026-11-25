-- Prove2me | solution 1 for GlobalTheory.Cube.restrictDeg_degProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:22.981879+00:00
-- url     : https://prove2.me/submissions/3035f6f5-178f-4bad-b1ae-3a638363ca9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_apply
import Theorems.Thm_GlobalTheory_Cube_degProj_apply

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
theorem _root_.solution (A : Cube.{v} ι R) (p q : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A p (degProj A q x) = if p = q then restrictDeg A p x else 0 := by
  funext s
  rw [restrictDeg_apply, degProj_apply, s.2]
  split_ifs <;> rfl
end GlobalTheory.Cube

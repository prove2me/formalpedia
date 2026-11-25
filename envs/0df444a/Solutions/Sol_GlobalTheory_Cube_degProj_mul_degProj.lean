-- Prove2me | solution 1 for GlobalTheory.Cube.degProj_mul_degProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:32.057334+00:00
-- url     : https://prove2.me/submissions/36533469-15a8-4f91-90f9-861bfb71a7d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_degProj

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
theorem _root_.solution (A : Cube.{v} ι R) (p q : ℕ) :
    degProj A p * degProj A q = if p = q then degProj A p else 0 := by
  refine LinearMap.ext fun x => ?_
  change extend A p (restrictDeg A p (degProj A q x)) = _
  rw [restrictDeg_degProj]
  split_ifs
  · rfl
  · exact map_zero _
end GlobalTheory.Cube

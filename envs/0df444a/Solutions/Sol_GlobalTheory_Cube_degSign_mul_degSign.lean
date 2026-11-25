-- Prove2me | solution 1 for GlobalTheory.Cube.degSign_mul_degSign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:52.016233+00:00
-- url     : https://prove2.me/submissions/313c26f7-10dd-419f-9288-eb3ae439f4b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
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
theorem _root_.solution (A : Cube.{v} ι R) : degSign A * degSign A = 1 := by
  refine LinearMap.ext fun x => funext fun s => ?_
  rw [Module.End.mul_apply, degSign_apply, degSign_apply, smul_smul, ← mul_pow]
  simp
end GlobalTheory.Cube

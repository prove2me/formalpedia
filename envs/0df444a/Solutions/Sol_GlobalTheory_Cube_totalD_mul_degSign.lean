-- Prove2me | solution 1 for GlobalTheory.Cube.totalD_mul_degSign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:43.918064+00:00
-- url     : https://prove2.me/submissions/a2d94007-af10-4b9b-b3de-2381fbc1c075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_ext_restrictDeg
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_degSign
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_succ
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_zero

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
theorem _root_.solution (A : Cube.{v} ι R) :
    (totalD A : Module.End R _) * degSign A = -(degSign A * totalD A) := by
  refine LinearMap.ext fun x => ext_restrictDeg fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, restrictDeg_degSign]
  cases p with
  | zero => simp [restrictDeg_totalD_zero]
  | succ p =>
    rw [restrictDeg_totalD_succ, restrictDeg_totalD_succ, restrictDeg_degSign, map_zsmul, pow_succ]
    simp
end GlobalTheory.Cube

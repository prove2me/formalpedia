-- Prove2me | solution 1 for GlobalTheory.ClassMin.map_add_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:34.430639+00:00
-- url     : https://prove2.me/submissions/8932e8a9-c814-46fc-8104-eba4c4adcc7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) (a m : X) (n : ℤ) :
    Q (a + n • m) = Q a + n * polar Q a m + n ^ 2 * Q m := by
  rw [QuadraticMap.map_add Q, polar_smul_right, QuadraticMap.map_smul]
  simp only [zsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.ClassMin

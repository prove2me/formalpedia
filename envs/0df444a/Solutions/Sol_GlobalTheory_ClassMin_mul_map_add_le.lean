-- Prove2me | solution 1 for GlobalTheory.ClassMin.mul_map_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:01.576432+00:00
-- url     : https://prove2.me/submissions/d1bf6316-26d3-49f5-9d54-8dbf5281f51c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_map_add_zsmul

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
theorem _root_.solution (hQ : ∀ x, 0 ≤ Q x) (j : ℤ) (a b : X) :
    j * Q (a + b) ≤ (j + 1) * Q a + j * (j + 1) * Q b := by
  have h1 := map_add_zsmul Q a b 1
  have h2 := hQ (a + (-j) • b)
  rw [one_smul] at h1
  rw [map_add_zsmul] at h2
  rw [h1]
  push_cast at h2 ⊢
  nlinarith
end GlobalTheory.ClassMin

-- Prove2me | solution 1 for GlobalTheory.ClassMin.polar_ofIntBilin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:01.908331+00:00
-- url     : https://prove2.me/submissions/f118b78d-1d48-499e-b0eb-b26e60169c1a

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
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution {β : LinearMap.BilinForm ℤ X} (hβ : ∀ x y, β x y = β y x) (x y : X) :
    polar (ofIntBilin β) x y = β x y := by
  simp only [polar, ofIntBilin_apply, map_add, LinearMap.add_apply, hβ y x]
  push_cast
  ring
end GlobalTheory.ClassMin

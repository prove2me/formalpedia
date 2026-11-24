-- Prove2me | solution 1 for GlobalTheory.ClassMin.tendsto_affine_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:41.58801+00:00
-- url     : https://prove2.me/submissions/c05705c8-7803-4426-9c7e-006607edc96a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_finite_affine_sublevel

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
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t)
    (ν : X →+ ℝ) : Tendsto (fun x => t * Q x + ν x) cofinite atTop :=
  tendsto_atTop.mpr fun r => (finite_affine_sublevel hQ ht ν r).subset fun x hx =>
    le_of_not_ge (show ¬ r ≤ t * Q x + ν x from hx)
end GlobalTheory.ClassMin

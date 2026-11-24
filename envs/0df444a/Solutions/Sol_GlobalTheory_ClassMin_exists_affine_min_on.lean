-- Prove2me | solution 1 for GlobalTheory.ClassMin.exists_affine_min_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:49.968599+00:00
-- url     : https://prove2.me/submissions/fcc01088-1014-4280-88e7-a4a85ed4877a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_tendsto_affine_cofinite

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
theorem _root_.solution (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    {S : Set X} (hS : S.Nonempty) : ∃ a ∈ S, ∀ x ∈ S, t * Q a + ν a ≤ t * Q x + ν x :=
  (tendsto_affine_cofinite hQ ht ν).exists_within_forall_le hS
end GlobalTheory.ClassMin

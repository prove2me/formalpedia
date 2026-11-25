-- Prove2me | solution 1 for GlobalTheory.ClassMin.map_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:29.052644+00:00
-- url     : https://prove2.me/submissions/dee8e8ec-f0de-4822-8dad-e662b835a315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_mul_map_add_le

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
theorem _root_.solution (hQ : ∀ x, 0 ≤ Q x) {j : ℤ} (hj : 1 ≤ j) (a b : X) :
    Q (a + b) ≤ (1 + 1 / j) * Q a + (1 + j) * Q b := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast (by omega : (0 : ℤ) < j)
  refine le_of_mul_le_mul_left ((mul_map_add_le hQ j a b).trans_eq ?_) hj'
  field_simp
  ring
end GlobalTheory.ClassMin

-- Prove2me | solution 1 for GlobalTheory.ClassMin.exists_global_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:31.794264+00:00
-- url     : https://prove2.me/submissions/5cf0d712-2a9a-4255-bc4e-481f99c516fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_exists_affine_min_on

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
theorem _root_.solution (hQ : (realExtension Q).PosDef) (ν : X →+ ℝ) {N : ℝ} (hN : 0 < N) :
    ∃ a, ∀ x, Q a / N + ν a ≤ Q x / N + ν x := by
  simpa [div_eq_inv_mul] using exists_affine_min_on hQ (inv_pos.mpr hN) ν Set.univ_nonempty
end GlobalTheory.ClassMin

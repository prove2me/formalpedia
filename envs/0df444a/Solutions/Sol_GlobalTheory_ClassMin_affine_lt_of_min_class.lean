-- Prove2me | solution 1 for GlobalTheory.ClassMin.affine_lt_of_min_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:10.502163+00:00
-- url     : https://prove2.me/submissions/7804276d-bc03-43d8-8a83-fd720cfae755

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_lt_add_zsmul_of_le_add

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
theorem _root_.solution (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {N n : ℤ}
    (hn : 2 ≤ n) {a : X} (ha : ∀ w, t * Q a + ν a ≤ t * Q (a + N • w) + ν (a + N • w)) {w : X}
    (hw : (n * N) • w ≠ 0) :
    t * Q a + ν a < t * Q (a + (n * N) • w) + ν (a + (n * N) • w) := by
  rw [mul_smul] at hw ⊢
  exact lt_add_zsmul_of_le_add hQ ht ν hn (ha w) fun h => hw (by rw [h, smul_zero])
end GlobalTheory.ClassMin

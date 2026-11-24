-- Prove2me | solution 1 for GlobalTheory.ClassMin.affine_lt_of_global_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:09.683706+00:00
-- url     : https://prove2.me/submissions/d1ede19c-3e66-432a-ad19-054a3ac35737

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
theorem _root_.solution (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {N : ℤ}
    (hN : 2 ≤ N) {a : X} (ha : ∀ x, t * Q a + ν a ≤ t * Q x + ν x) {w : X} (hw : w ≠ 0) :
    t * Q a + ν a < t * Q (a + N • w) + ν (a + N • w) :=
  lt_add_zsmul_of_le_add hQ ht ν hN (ha _) hw
end GlobalTheory.ClassMin

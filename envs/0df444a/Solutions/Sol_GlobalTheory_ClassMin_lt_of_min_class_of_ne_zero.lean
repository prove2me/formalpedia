-- Prove2me | solution 1 for GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:39.651799+00:00
-- url     : https://prove2.me/submissions/7b9f710b-24f4-428c-a530-63da3e84c75a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_eq_zero_of_zsmul_eq_zero
import Theorems.Thm_GlobalTheory_ClassMin_lt_of_min_class

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
theorem _root_.solution (hQ : Q.PosDef) {N n : ℤ} (hN : N ≠ 0) (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : w ≠ 0) : Q a < Q (a + (n * N) • w) :=
  lt_of_min_class hQ hn ha fun h =>
    hw (eq_zero_of_zsmul_eq_zero hQ (mul_ne_zero (by omega) hN) h)
end GlobalTheory.ClassMin

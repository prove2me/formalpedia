-- Prove2me | solution 1 for GlobalTheory.ClassMin.lt_of_min_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:46.640198+00:00
-- url     : https://prove2.me/submissions/8f53a148-584a-4c6a-a64d-53cab8f92859

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_affine_lt_of_min_class

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
theorem _root_.solution (hQ : Q.PosDef) {N n : ℤ} (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : (n * N) • w ≠ 0) :
    Q a < Q (a + (n * N) • w) := by
  simpa using affine_lt_of_min_class hQ one_pos 0 hn (by simpa using ha) hw
end GlobalTheory.ClassMin

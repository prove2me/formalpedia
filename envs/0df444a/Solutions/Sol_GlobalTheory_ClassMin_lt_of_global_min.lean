-- Prove2me | solution 1 for GlobalTheory.ClassMin.lt_of_global_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:45.752077+00:00
-- url     : https://prove2.me/submissions/086bc1ff-0a40-4d94-a062-db73b6abff30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_affine_lt_of_global_min

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
theorem _root_.solution (hQ : Q.PosDef) (ν : X →+ ℝ) {N : ℤ} (hN : 2 ≤ N) {a : X}
    (ha : ∀ x, Q a / N + ν a ≤ Q x / N + ν x) {w : X} (hw : w ≠ 0) :
    Q a / N + ν a < Q (a + N • w) / N + ν (a + N • w) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : (0 : ℤ) < N)
  simp only [div_eq_inv_mul] at ha ⊢
  exact affine_lt_of_global_min hQ (inv_pos.mpr hN') ν hN ha hw
end GlobalTheory.ClassMin

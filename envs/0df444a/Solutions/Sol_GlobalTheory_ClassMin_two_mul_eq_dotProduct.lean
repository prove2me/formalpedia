-- Prove2me | solution 1 for GlobalTheory.ClassMin.two_mul_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:37.137706+00:00
-- url     : https://prove2.me/submissions/c4d6eb97-4660-4005-80ce-79af17dc93ec

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
variable {X : Type*} [AddCommGroup X] {ι : Type*}
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
namespace GlobalTheory.ClassMin
theorem _root_.solution [Fintype ι] (Q : QuadraticMap ℤ X ℝ) (e : Module.Basis ι ℤ X) (a : X) :
    2 * Q a = (fun i => (e.repr a i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (e.repr a i : ℝ)) := by
  have := polar_sum_smul Q e (e.repr a) (e.repr a)
  rw [e.sum_repr, polar_self, two_smul] at this
  rw [two_mul, this]
  simp
end GlobalTheory.ClassMin

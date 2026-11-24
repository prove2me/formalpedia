-- Prove2me | solution 1 for GlobalTheory.HermFrame.mdel_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:35.216859+00:00
-- url     : https://prove2.me/submissions/ad88b77d-0244-4d58-98e9-1d9e27cf9590

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_del_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt 1 A z)
    (h' : MContDiffAt 1 B z) (ξ : E) :
    mdel (fun x => A x * B x) z ξ = A z * mdel B z ξ + mdel A z ξ * B z := by
  ext a b
  simp only [mdel_apply, mul_apply, Matrix.add_apply]
  rw [del_sum fun c _ => (h.diff a c).fun_mul (h'.diff c b), ← Finset.sum_add_distrib,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => del_mul (h.diff a c) (h'.diff c b) ξ
end GlobalTheory.HermFrame

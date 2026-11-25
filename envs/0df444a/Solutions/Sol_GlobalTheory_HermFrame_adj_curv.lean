-- Prove2me | solution 1 for GlobalTheory.HermFrame.adj_curv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:21.986337+00:00
-- url     : https://prove2.me/submissions/d3827b24-0ee1-451c-ba9c-24b765830af3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_conjTranspose_mdel
import Theorems.Thm_GlobalTheory_HermFrame_conjTranspose_mddbar
import Theorems.Thm_GlobalTheory_HermFrame_curv_eq
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
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
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) : adj (H z) (H z) (curv H z ξ η) = curv H z η ξ := by
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have e : ∀ M : Matrix n n ℂ, Mᵀᴴ = Mᴴᵀ := fun _ => rfl
  have e1 : (mdbar H z η)ᴴ = mdel H z η := by
    rw [← conjTranspose_mdel hh, conjTranspose_conjTranspose]
  rw [adj, curv_eq h hu, curv_eq h hu]
  simp only [conjTranspose_sub, conjTranspose_mul, hh.self_of_nhds.transpose.inv.eq, e, e1,
    conjTranspose_mdel hh, conjTranspose_mddbar h hh, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, nonsing_inv_mul _ hu', Matrix.mul_one]
end GlobalTheory.HermFrame

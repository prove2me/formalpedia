-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_curv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:36.459819+00:00
-- url     : https://prove2.me/submissions/9b3e5b64-4726-402d-b265-f1a6a416be2d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_adj_curv
import Theorems.Thm_GlobalTheory_HermFrame_form_adj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hu : IsUnit (H z).det) (ξ η : E) (v w : n → ℂ) :
    form (H z) (curv H z ξ η *ᵥ v) w = form (H z) v (curv H z η ξ *ᵥ w) := by
  rw [form_adj hh.self_of_nhds hu hh.self_of_nhds, adj_curv h hh hu]
end GlobalTheory.HermFrame

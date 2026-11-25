-- Prove2me | solution 1 for GlobalTheory.HermFrame.IsHermFrame.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:50:56.402879+00:00
-- url     : https://prove2.me/submissions/8150bd7e-7004-4193-bcd5-17788139b3e3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_of_mContDiffAt

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
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HermFrame
namespace IsHermFrame
theorem _root_.solution (h : IsHermFrame U H) : IsHermFrame U fun x => dualGram (H x) :=
  .of_mContDiffAt h.isOpen (fun z hz => ((h.mContDiffAt hz).inv (h.isUnit z hz)).transpose)
    (fun z hz => (h.herm z hz).inv.transpose)
    fun z hz => by
      rw [dualGram, det_transpose]; exact isUnit_nonsing_inv_det _ (h.isUnit z hz)
end IsHermFrame
end GlobalTheory.HermFrame

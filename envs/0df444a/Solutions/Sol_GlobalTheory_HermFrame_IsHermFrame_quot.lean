-- Prove2me | solution 1 for GlobalTheory.HermFrame.IsHermFrame.quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:00.726482+00:00
-- url     : https://prove2.me/submissions/252e507a-405f-4097-a065-0cd620fad329

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_of_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_isUnit_det_quotGram


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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HermFrame
namespace IsHermFrame
theorem _root_.solution (h : IsHermFrame U H) (hu : ∀ z ∈ U, IsUnit (subGram (H z)).det) :
    IsHermFrame U fun x => quotGram (H x) :=
  .of_mContDiffAt h.isOpen (fun z hz => (h.mContDiffAt hz).quotGram (hu z hz))
    (fun z hz => isHermitian_quotGram (h.herm z hz))
    fun z hz => isUnit_det_quotGram (h.isUnit z hz) (hu z hz)
end IsHermFrame
end GlobalTheory.HermFrame

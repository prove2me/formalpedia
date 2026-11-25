-- Prove2me | solution 1 for GlobalTheory.norm_pderivIter_le_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:58.964494+00:00
-- url     : https://prove2.me/submissions/586f6d67-a012-4037-bb73-ac4e9fd8b495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_PderivIterEqPderivListOfDifferentiableOn
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn
import Theorems.Thm_GlobalTheory_norm_pderivIter_le_of_analyticAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ} {r : ι → ℝ}
    {M : ℝ} (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hsub : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → z ∈ U)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k :=
  norm_pderivIter_le_of_analyticAt α hr hα
    (fun z hz => SCV.analyticOnNhd_of_differentiableOn hU hF z (hsub z hz)) hM
end GlobalTheory

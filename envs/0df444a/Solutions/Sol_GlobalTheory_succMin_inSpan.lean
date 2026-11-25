-- Prove2me | solution 1 for GlobalTheory.succMin_inSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:46.207309+00:00
-- url     : https://prove2.me/submissions/ec5e3497-372d-4248-bf39-b292e7ab0d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMin_comap_linearIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) (i : ℕ) : succMin (inSpan L) i = succMin L i :=
  succMin_comap_linearIsometry (span ℝ (L : Set E)).subtypeₗᵢ
    (fun x hx => ⟨⟨x, subset_span hx⟩, rfl⟩) i
end GlobalTheory

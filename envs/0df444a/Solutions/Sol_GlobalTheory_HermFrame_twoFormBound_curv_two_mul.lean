-- Prove2me | solution 1 for GlobalTheory.HermFrame.twoFormBound_curv_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:31.697456+00:00
-- url     : https://prove2.me/submissions/500384e3-dec1-4b89-860b-2e1e4ef790eb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_two
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_eventually_herm
import Theorems.Thm_GlobalTheory_HermFrame_isSesq_curv
import Theorems.Thm_GlobalTheory_HermFrame_form_curv
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_le_of_diagonal


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
variable {ι : Type*} [Fintype ι]
variable [Fintype n]
variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}
namespace GlobalTheory.HermFrame
theorem _root_.solution [DecidableEq n] (hH : IsPosFrame U H)
    (hG : ∀ z ∈ U, (G z).PosSemidef) (hC : 0 ≤ C)
    (h : ∀ z ∈ U, ∀ ξ v, ‖form (H z) (curv H z ξ ξ *ᵥ v) v‖ ≤
      C * gnorm (G z) ξ ^ 2 * gnorm (H z) v ^ 2) : TwoFormBound U H G (curv H) (2 * C) :=
  fun z hz =>
    have h' := hH.isHermFrame
    ⟨hH.posDef z hz, hG z hz, opNorm_le_of_diagonal (hH.posDef z hz) (hG z hz)
      (isSesq_curv (h'.two hz) (h'.isUnit z hz))
      (fun ξ => form_curv (h'.two hz) (h'.eventually_herm hz) (h'.isUnit z hz) ξ ξ) hC (h z hz)⟩
end GlobalTheory.HermFrame

-- Prove2me | solution 1 for GlobalTheory.HermFrame.IsPosFrame.quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:42:33.189544+00:00
-- url     : https://prove2.me/submissions/faa294a1-be29-44d4-810f-3e0024352cf8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_isPosFrame
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_quot
import Theorems.Thm_GlobalTheory_HermFrame_posDef_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_posDef_subGram


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
namespace IsPosFrame
theorem _root_.solution (h : IsPosFrame U H) : IsPosFrame U fun x => quotGram (H x) :=
  (h.isHermFrame.quot fun z hz =>
    (isUnit_iff_isUnit_det _).1 (posDef_subGram (h.posDef z hz)).isUnit).isPosFrame
    fun z hz => posDef_quotGram (h.posDef z hz)
end IsPosFrame
end GlobalTheory.HermFrame

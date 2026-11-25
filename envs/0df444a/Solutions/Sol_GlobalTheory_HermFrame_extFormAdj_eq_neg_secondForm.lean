-- Prove2me | solution 1 for GlobalTheory.HermFrame.extFormAdj_eq_neg_secondForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:28.994647+00:00
-- url     : https://prove2.me/submissions/f6b5ddcf-a996-4706-80ac-ccb4b3e11e8b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_secondFormAdj
import Theorems.Thm_GlobalTheory_HermFrame_adj_adj
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_subGram
import Theorems.Thm_GlobalTheory_HermFrame_isUnit_det_quotGram
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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) : extFormAdj H z ξ = -secondForm H z ξ := by
  have hz := hh.self_of_nhds
  rw [extFormAdj, extForm_eq_neg_secondFormAdj h hh hu hs, secondFormAdj,
    ← adj_adj (isHermitian_subGram hz) hs (isHermitian_quotGram hz) (isUnit_det_quotGram hu hs)
      (secondForm H z ξ),
    adj_adj (isHermitian_quotGram hz) (isUnit_det_quotGram hu hs) (isHermitian_subGram hz) hs]
  simp [adj]
end GlobalTheory.HermFrame

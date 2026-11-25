-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_secondFormAdj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:56.428326+00:00
-- url     : https://prove2.me/submissions/302b093e-2e42-4592-9044-f3d988fb608e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_form_secondForm
import Theorems.Thm_GlobalTheory_HermFrame_conj_form
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_subGram


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
namespace GlobalTheory.HermFrame
theorem _root_.solution (hh : (H z).IsHermitian) (hu : IsUnit (subGram (H z)).det) (ξ : E)
    (s : m → ℂ) : form (subGram (H z)) (-(secondFormAdj H z ξ * secondForm H z ξ) *ᵥ s) s =
      -form (quotGram (H z)) (secondForm H z ξ *ᵥ s) (secondForm H z ξ *ᵥ s) := by
  rw [← conj_form (isHermitian_quotGram hh), form_secondForm hh hu,
    conj_form (isHermitian_subGram hh), mulVec_mulVec, neg_mulVec, form, form, neg_dotProduct]
end GlobalTheory.HermFrame

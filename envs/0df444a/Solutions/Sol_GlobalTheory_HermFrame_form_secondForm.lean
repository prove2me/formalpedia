-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_secondForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:38.819294+00:00
-- url     : https://prove2.me/submissions/bca99604-29e7-4a92-ab5a-4c8ced71dc0f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_form_adj
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
    (s : m → ℂ) (q : l → ℂ) : form (quotGram (H z)) (secondForm H z ξ *ᵥ s) q =
      form (subGram (H z)) s (secondFormAdj H z ξ *ᵥ q) :=
  form_adj (isHermitian_subGram hh) hu (isHermitian_quotGram hh) _ s q
end GlobalTheory.HermFrame

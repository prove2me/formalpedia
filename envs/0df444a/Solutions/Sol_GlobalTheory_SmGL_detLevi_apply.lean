-- Prove2me | solution 1 for GlobalTheory.SmGL.detLevi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:36.65486+00:00
-- url     : https://prove2.me/submissions/2721bc91-fbd3-4f3f-8848-8e2277f2d860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_apply
import Theorems.Thm_GlobalTheory_SmGL_det_leviEmb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) (g : Levi k m) :
    detLevi e χ g = ∏ a, (χ * absPow k (-(modExp m a : ℂ) / 2)) (GeneralLinearGroup.det (g a)) := by
  simp [detLevi, det_leviEmb, deltaHalf_apply, neg_div, absPow_neg, Finset.prod_mul_distrib]
end GlobalTheory.SmGL

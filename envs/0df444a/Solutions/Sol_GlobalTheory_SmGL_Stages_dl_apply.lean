-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.dl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:14.392717+00:00
-- url     : https://prove2.me/submissions/8dc88c1e-8888-4bad-8421-e3d1f71fa0f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution (e : a ⊕ b ≃ n) (q : parab k (two e)) :
    dl e q = absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det (pr e q).1) *
      absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det (pr e q).2) := by
  rw [← deltaHalf_two]
  exact congrArg (deltaHalf k (Two a b)) ((leviTwo k a b).apply_symm_apply _).symm
end GlobalTheory.SmGL.Stages

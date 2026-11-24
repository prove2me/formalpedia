-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.dat_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:22.271105+00:00
-- url     : https://prove2.me/submissions/1f7c2a7f-783c-458c-acf6-a5b45641be16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_dat_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_tauFst_apply

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
theorem _root_.solution (e : a ⊕ b ≃ n) (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (q : parab k (two e)) (y : V₁ ⊗[ℂ] V₂) :
    TensorProduct.comm ℂ V₁ V₂ (dat e (extTensor π₁ π₂) q y) =
      TensorProduct.map (π₂ (pr e q).2) (tauFst e π₁ q) (TensorProduct.comm ℂ V₁ V₂ y) := by
  induction y with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f x =>
    rw [dat_apply, extTensor_tmul, map_smul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
      TensorProduct.map_tmul, ← TensorProduct.tmul_smul, tauFst_apply]
end GlobalTheory.SmGL.Stages

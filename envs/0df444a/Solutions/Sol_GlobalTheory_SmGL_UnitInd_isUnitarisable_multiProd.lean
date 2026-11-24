-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:12:01.226458+00:00
-- url     : https://prove2.me/submissions/61f9e6f7-efa4-4e2a-9435-fd9b0d61b995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_piTensor
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_parInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} (h : ∀ a, IsUnitarisable (π a)) :
    IsUnitarisable (multiProd e π) :=
  isUnitarisable_parInd _ (isUnitarisable_piTensor h)
end GlobalTheory.SmGL.UnitInd

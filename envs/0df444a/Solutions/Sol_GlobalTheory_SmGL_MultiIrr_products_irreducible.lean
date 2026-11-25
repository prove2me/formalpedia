-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.products_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:05.208812+00:00
-- url     : https://prove2.me/submissions/9d7260dd-f09d-4ea4-b7d1-fcf7786e2428

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind_Lower_fadf1cb588da
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_multiProd
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_multiProd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_parInd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (s : ℕ) (d : Fin s → ℕ) (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, Fin (d a)) ≃ n)
      (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
      (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
      (∀ a, IsSmooth (σ a)) → (∀ a, (σ a).IsIrreducible) → (∀ a, IsUnitarisable (σ a)) →
      IsSmooth (multiProd e σ) ∧ (multiProd e σ).IsIrreducible ∧ IsUnitarisable (multiProd e σ)) ∧
    ∀ (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
      (e : a ⊕ b ≃ n) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL a k) V) (π₂ : Representation ℂ (GL b k) W),
      IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
      IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
      (ind₂ e (extTensor π₁ π₂)).IsIrreducible ∧ (ind₂Lower e (extTensor π₁ π₂)).IsIrreducible :=
  ⟨fun _ _ _ _ _ e _ _ _ _ hs hi hu => ⟨isSmooth_parInd _ _, isIrreducible_multiProd H e hs hi hu,
      UnitInd.isUnitarisable_multiProd e hu⟩,
    fun _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ s₁ i₁ u₁ s₂ i₂ u₂ =>
      ⟨isIrreducible_ind₂ H e s₁ i₁ u₁ s₂ i₂ u₂, isIrreducible_ind₂Lower H e s₁ i₁ u₁ s₂ i₂ u₂⟩⟩
end GlobalTheory.SmGL.MultiIrr

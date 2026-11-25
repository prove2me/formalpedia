-- Prove2me | solution 1 for GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:36.065777+00:00
-- url     : https://prove2.me/submissions/3412e537-f697-45fc-ab36-d79d945896a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartProdInl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartProdInlStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_prod_inl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_prod_inl | exact GlobalTheory.UnitLemma.Desc.chi_prod_inl | (intros; apply GlobalTheory.UnitLemma.Desc.chi_prod_inl <;> assumption)
end _root_.GlobalTheory.T

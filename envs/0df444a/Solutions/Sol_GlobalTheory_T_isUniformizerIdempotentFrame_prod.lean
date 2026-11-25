-- Prove2me | solution 1 for GlobalTheory.T.isUniformizerIdempotentFrame_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:43.713393+00:00
-- url     : https://prove2.me/submissions/10a63b7b-6111-48b1-9710-33b59853a7cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProdStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_isFrame_prod


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
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isFrame_prod | exact GlobalTheory.UnitLemma.Desc.isFrame_prod | (intros; apply GlobalTheory.UnitLemma.Desc.isFrame_prod <;> assumption)
end _root_.GlobalTheory.T

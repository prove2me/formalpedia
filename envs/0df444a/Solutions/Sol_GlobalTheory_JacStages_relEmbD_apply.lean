-- Prove2me | solution 1 for GlobalTheory.JacStages.relEmbD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:56.936029+00:00
-- url     : https://prove2.me/submissions/89e13957-6bbd-4596-845a-05ccd4f10570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacStages
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.JacStages
theorem _root_.solution (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmbD k f g i = leviEmb k (f i) (g i) := rfl
end GlobalTheory.JacStages

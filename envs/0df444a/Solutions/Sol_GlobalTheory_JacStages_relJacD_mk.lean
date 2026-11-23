-- Prove2me | solution 1 for GlobalTheory.JacStages.relJacD_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:52.368831+00:00
-- url     : https://prove2.me/submissions/abdf630b-22ca-4f78-bc0b-fc51481da713

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
variable {k}
namespace GlobalTheory.JacStages
theorem _root_.solution (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := rfl
end GlobalTheory.JacStages

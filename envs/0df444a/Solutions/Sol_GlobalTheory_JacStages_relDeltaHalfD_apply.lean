-- Prove2me | solution 1 for GlobalTheory.JacStages.relDeltaHalfD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:14.864882+00:00
-- url     : https://prove2.me/submissions/267925c4-3569-45e3-bea7-c2e1a2b8086c

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
theorem _root_.solution (g : ∀ i, Levi k (c i)) :
    relDeltaHalfD k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalfD, MonoidHom.finsetProd_apply]
end GlobalTheory.JacStages

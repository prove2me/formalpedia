-- Prove2me | solution 1 for GlobalTheory.JacStages.curryML_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:51.099861+00:00
-- url     : https://prove2.me/submissions/8cc75242-b01d-490e-a5c0-204e34719c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.JacStages
variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]
namespace GlobalTheory.JacStages
theorem _root_.solution (x : ∀ p, M p) : curryML M x = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := rfl
end GlobalTheory.JacStages

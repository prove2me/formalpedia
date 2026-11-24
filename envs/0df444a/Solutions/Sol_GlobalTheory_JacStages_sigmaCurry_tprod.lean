-- Prove2me | solution 1 for GlobalTheory.JacStages.sigmaCurry_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:44.880639+00:00
-- url     : https://prove2.me/submissions/d5d3fa24-f69c-428c-a06f-670dff2e5129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
import Theorems.Thm_GlobalTheory_JacStages_curryML_apply
import Theorems.Thm_GlobalTheory_JacStages_sigmaCurry_eq_lift

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
variable [Finite α] [∀ a, Finite (β a)]
namespace GlobalTheory.JacStages
theorem _root_.solution (x : ∀ p, M p) :
    sigmaCurry M (tprod ℂ x) = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  have h := LinearMap.congr_fun (sigmaCurry_eq_lift M) (tprod ℂ x)
  simpa [curryML_apply] using h
end GlobalTheory.JacStages

-- Prove2me | solution 1 for GlobalTheory.JacStages.sigmaCurry_eq_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:08.20646+00:00
-- url     : https://prove2.me/submissions/5bd05d40-9aa3-4624-90ec-a3a64981da46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
import Theorems.Thm_GlobalTheory_JacStages_curryML_apply

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
theorem _root_.solution : (sigmaCurry M : (⨂[ℂ] p, M p) →ₗ[ℂ] _) = lift (curryML M) := by
  apply (sigBasis M).ext
  intro q
  rw [LinearEquiv.coe_coe, sigmaCurry, Basis.equiv_apply]
  simp only [sigBasis, nestBasis, Basis.piTensorProduct_apply, lift.tprod, curryML_apply]
  rfl
end GlobalTheory.JacStages

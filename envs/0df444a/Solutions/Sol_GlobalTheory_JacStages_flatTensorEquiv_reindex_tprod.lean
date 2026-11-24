-- Prove2me | solution 1 for GlobalTheory.JacStages.flatTensorEquiv_reindex_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:29.139979+00:00
-- url     : https://prove2.me/submissions/1878b4a7-3cd8-4374-b9f5-4aec437024d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
import Theorems.Thm_GlobalTheory_JacStages_sigmaCurry_tprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.JacStages.sigmaCurry_tprod

set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.JacStages
variable {s : ℕ} {t : Fin s → ℕ}
namespace GlobalTheory.JacStages
theorem _root_.solution (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv (tprod ℂ x)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [flatTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sigmaCurry_tprod]
end GlobalTheory.JacStages

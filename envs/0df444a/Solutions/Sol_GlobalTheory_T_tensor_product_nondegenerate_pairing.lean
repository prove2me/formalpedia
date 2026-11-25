-- Prove2me | solution 1 for GlobalTheory.T.tensor_product_nondegenerate_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:24.25507+00:00
-- url     : https://prove2.me/submissions/cd80e06e-3912-484d-873d-a9159d66ce28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairingStatement
import Theorems.Thm_GlobalTheory_tensor_pairing_separating


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type) [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)] [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ), (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) → ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)), (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧ ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  first | exact @GlobalTheory.tensor_pairing_separating | exact GlobalTheory.tensor_pairing_separating | (intros; apply GlobalTheory.tensor_pairing_separating <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.T.latticeCount_prod_of_idempotent_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:23:58.776889+00:00
-- url     : https://prove2.me/submissions/32b165a3-90f6-4cba-b631-09097b824c8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparableStatement
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_N_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  first | exact @GlobalTheory.UnitLemma.ProdCount.N_prod | exact GlobalTheory.UnitLemma.ProdCount.N_prod | (intros; apply GlobalTheory.UnitLemma.ProdCount.N_prod <;> assumption)
end _root_.GlobalTheory.T

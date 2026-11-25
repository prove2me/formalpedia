-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.N_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:09.590378+00:00
-- url     : https://prove2.me/submissions/a24b1602-7926-4045-9972-94ab0e20a8be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_N_prod_of_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ :=
  fun _ B₁ B₂ he _ x₁ x₂ _ _ _ _ => N_prod_of_idem B₁ B₂ he x₁ x₂
end GlobalTheory.UnitLemma.ProdCount

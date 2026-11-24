-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ResDeg.card_residueField_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:15.428656+00:00
-- url     : https://prove2.me/submissions/c2ddb378-13fb-4e2a-9174-cc9656fbbf84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
import Theorems.Thm_GlobalTheory_UnitLemma_ResDeg_card_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ResDeg
theorem _root_.solution : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl
end GlobalTheory.UnitLemma.ResDeg

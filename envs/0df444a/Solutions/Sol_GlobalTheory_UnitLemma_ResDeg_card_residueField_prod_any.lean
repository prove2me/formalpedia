-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:16.175046+00:00
-- url     : https://prove2.me/submissions/00e9eb09-6ecd-4b66-8de1-5891fba985d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProd
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
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
namespace GlobalTheory.UnitLemma.ResDeg
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl
end GlobalTheory.UnitLemma.ResDeg

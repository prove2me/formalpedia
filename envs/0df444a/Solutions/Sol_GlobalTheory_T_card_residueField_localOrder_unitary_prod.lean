-- Prove2me | solution 1 for GlobalTheory.T.card_residueField_localOrder_unitary_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:52.905263+00:00
-- url     : https://prove2.me/submissions/31756c4e-0bd6-48b6-8e96-08369251370f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProdStatement
import Theorems.Thm_GlobalTheory_UnitLemma_ResDeg_card_residueField_prod_any


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any <;> assumption)
end _root_.GlobalTheory.T

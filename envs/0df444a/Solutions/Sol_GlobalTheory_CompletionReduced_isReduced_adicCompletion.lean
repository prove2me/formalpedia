-- Prove2me | solution 1 for GlobalTheory.CompletionReduced.isReduced_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:38:39.127951+00:00
-- url     : https://prove2.me/submissions/e113cddd-964c-4163-a02b-34c19d4390b4

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
import Theorems.Thm_GlobalTheory_CompletionReduced_isReduced_of_dim_le
import Theorems.Thm_GlobalTheory_T_ringKrullDim_finite_of_essFiniteType_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionReduced
namespace GlobalTheory.CompletionReduced
theorem _root_.solution : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ
end GlobalTheory.CompletionReduced

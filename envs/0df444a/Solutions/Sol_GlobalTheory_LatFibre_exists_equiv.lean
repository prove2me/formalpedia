-- Prove2me | solution 1 for GlobalTheory.LatFibre.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:57.954877+00:00
-- url     : https://prove2.me/submissions/ea7d5801-9180-4c67-894c-c22e1349dd2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand
import Theorems.Thm_GlobalTheory_LatFibre_fibreMap_injective
import Theorems.Thm_GlobalTheory_LatFibre_fibreMap_surjective
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_eisClass_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.LatFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LatFibre
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (fibreMap 𝔞 𝔟) ⟨fibreMap_injective 𝔞 𝔟, fibreMap_surjective 𝔞 𝔟⟩, ?_⟩
  intro k hk σ z x
  exact eisClass_mk 𝔞 𝔟 hk σ z (pairOf x)
end GlobalTheory.LatFibre

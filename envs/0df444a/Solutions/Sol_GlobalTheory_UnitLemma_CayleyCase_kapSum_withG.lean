-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.kapSum_withG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:30:23.749588+00:00
-- url     : https://prove2.me/submissions/e6c3007e-b5b4-4a05-b671-030af060b08c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_N_withG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution (B₁ B₂ : InvAlg K) (Y₁ : B₁.A) (Y₂ : B₂.A)
    (h : ∀ L : Submodule K.O (B₁.A × B₂.A), (∀ y ∈ L, (B₁.g, B₂.g) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L)) :
    InvAlg.kapSum (withG B₁ Y₁) (withG B₂ Y₂) = InvAlg.kapSum B₁ B₂ := by
  show ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (withG (B₁.prod B₂) (Y₁, Y₂)).N k.rep =
    ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep
  exact finsum_congr fun k => by rw [N_withG (B₁.prod B₂) (Y₁, Y₂) h]
end GlobalTheory.UnitLemma.CayleyCase

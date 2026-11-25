-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.stSum_withG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:30:43.795042+00:00
-- url     : https://prove2.me/submissions/bbe1c704-c8f4-477f-8e25-01fd9b930f8d

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
theorem _root_.solution (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) :
    (withG B Y).stSum = B.stSum := by
  show ∑ᶠ k : B.Cl, (withG B Y).N k.rep = ∑ᶠ k : B.Cl, B.N k.rep
  exact finsum_congr fun k => N_withG B Y h _
end GlobalTheory.UnitLemma.CayleyCase

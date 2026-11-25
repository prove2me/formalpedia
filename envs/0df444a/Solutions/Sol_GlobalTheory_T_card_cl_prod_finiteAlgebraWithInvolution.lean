-- Prove2me | solution 1 for GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:29.143703+00:00
-- url     : https://prove2.me/submissions/37c912e0-67f7-4ed2-834d-59bb8b69248b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolutionStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_ClProd_card_cl_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | exact GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | (intros; apply GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod <;> assumption)
end _root_.GlobalTheory.T

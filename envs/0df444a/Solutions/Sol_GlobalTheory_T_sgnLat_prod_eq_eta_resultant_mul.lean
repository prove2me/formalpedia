-- Prove2me | solution 1 for GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:24.308947+00:00
-- url     : https://prove2.me/submissions/70d0fb49-f246-45c4-b63a-62c03110cdc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMulStatement
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_sgnLat_prod


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
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin, (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) * B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | exact GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | (intros; apply GlobalTheory.UnitLemma.SgnProd.sgnLat_prod <;> assumption)
end _root_.GlobalTheory.T

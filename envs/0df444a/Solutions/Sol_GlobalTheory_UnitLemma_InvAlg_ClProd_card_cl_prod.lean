-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:58.596184+00:00
-- url     : https://prove2.me/submissions/c369517d-09ec-4cf3-b20e-1301b28d875f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.InvAlg GlobalTheory.UnitLemma.InvAlg.ClProd
variable {K : UQ} (B₁ B₂ : InvAlg K)
namespace GlobalTheory.UnitLemma.InvAlg.ClProd
theorem _root_.solution (K : UQ) (B₁ B₂ : InvAlg K) :
    Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  rw [Nat.card_congr (clEquiv B₁ B₂), Nat.card_prod]
end GlobalTheory.UnitLemma.InvAlg.ClProd

-- Prove2me | solution 1 for GlobalTheory.LatPair.card_withLat_eq_card_withKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:36.553257+00:00
-- url     : https://prove2.me/submissions/940904c3-1c24-46d6-8876-c59892a6d29e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLatticeExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SumWithLatKerEqMulSumWithKerLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
open scoped Pointwise
open GlobalTheory GlobalTheory.LatPair
namespace GlobalTheory.LatPair
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} (L : Submodule (↥𝒪[k]) (n → k))
    [Submodule.IsLattice k L] : (withLat L).card = (withKer L).card := by
  classical
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := (Module.Free.chooseBasis 𝓀[k] (Red L)).toDualEquiv
  have e' : {x : Red L // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} :=
    e.toEquiv.subtypeEquiv (fun x => by simp)
  refine Finset.card_eq_of_equiv ?_
  exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
    ((latEquiv L).symm.trans (e'.symm.trans ((kerEquiv L q).trans
      (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))
end GlobalTheory.LatPair

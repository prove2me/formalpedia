-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:33.373036+00:00
-- url     : https://prove2.me/submissions/bc2efcc1-19a3-40b6-b78d-c2b9a3ebeca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution : valuation k (resCard k : k) < 1 := by
  have hres : IsLocalRing.residue 𝒪[k] (resCard k : 𝒪[k]) = 0 := by
    let := Fintype.ofFinite 𝓀[k]
    rw [map_natCast, resCard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hnu : ¬ IsUnit (resCard k : 𝒪[k]) := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres
  have hlt := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hnu
  simpa using hlt
end GlobalTheory.RootEx.UnipPow

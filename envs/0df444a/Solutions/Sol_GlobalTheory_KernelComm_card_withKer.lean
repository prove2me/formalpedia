-- Prove2me | solution 1 for GlobalTheory.KernelComm.card_withKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:36.876308+00:00
-- url     : https://prove2.me/submissions/86df364b-66b2-46fc-9397-9f708898e761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
namespace GlobalTheory.KernelComm
theorem _root_.solution (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
      Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
  simp [hc]
end GlobalTheory.KernelComm

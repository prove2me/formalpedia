-- Prove2me | solution 1 for GlobalTheory.PairOp.GsStar_mul_Gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:48.6498+00:00
-- url     : https://prove2.me/submissions/ddbba79c-1964-4c44-b63b-3b3525be6eea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_commute_sum
import Theorems.Thm_GlobalTheory_PairOp_GsStar_dia
import Theorems.Thm_GlobalTheory_PairOp_Gs_mul_GsStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution (hχ : χ ≠ 1) :
    (GsStar χ * Gs χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm := by
  have hc : (GsStar χ * Gs χ : Module.End ℂ (Form k n M)) = Gs χ * GsStar χ := by
    unfold Gs
    exact commute_sum (fun c => GsStar_dia χ c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d
  rw [hc, Gs_mul_GsStar hχ]
end GlobalTheory.PairOp

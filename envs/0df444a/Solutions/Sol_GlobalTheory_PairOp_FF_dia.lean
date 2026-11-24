-- Prove2me | solution 1 for GlobalTheory.PairOp.FF_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:55.962414+00:00
-- url     : https://prove2.me/submissions/4791bd82-d4ce-4628-8ff0-1247124ac6d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_cross_dia
import Theorems.Thm_GlobalTheory_PairOp_sumOp_dia

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
namespace GlobalTheory.PairOp
theorem _root_.solution (c : 𝓀[k]ˣ) : (FF q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF q χ := by
  unfold FF
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withLat.mp hQ)]
end GlobalTheory.PairOp

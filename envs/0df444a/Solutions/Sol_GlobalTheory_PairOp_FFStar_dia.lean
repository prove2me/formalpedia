-- Prove2me | solution 1 for GlobalTheory.PairOp.FFStar_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:39.583828+00:00
-- url     : https://prove2.me/submissions/af542acb-75b5-4be7-9507-897a7451931e

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
theorem _root_.solution (c : 𝓀[k]ˣ) : (FFStar q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar q χ := by
  unfold FFStar
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withKer.mp hQ).symm]
end GlobalTheory.PairOp

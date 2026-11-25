-- Prove2me | solution 1 for GlobalTheory.PairOp.pairOperatorStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:20.803124+00:00
-- url     : https://prove2.me/submissions/f0eca624-0c23-4417-93ae-bf4b4a8ca1e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_vanishing
import Theorems.Thm_GlobalTheory_PairOp_operatorIdentities
import Theorems.Thm_GlobalTheory_PairOp_adjointIdentities
import Theorems.Thm_GlobalTheory_LatPair_resChar_ne_one


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
theorem _root_.solution : PairOperatorStatement := by
  intro k _ _ _ _ ϖ ψ hψ n _ _
  exact ⟨fun M _ _ => ⟨vanishing ϖ, operatorIdentities ϖ (resChar_ne_one hψ ϖ)⟩, adjointIdentities ϖ hψ⟩
end GlobalTheory.PairOp

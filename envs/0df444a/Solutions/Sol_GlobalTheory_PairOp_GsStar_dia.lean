-- Prove2me | solution 1 for GlobalTheory.PairOp.GsStar_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:54.909695+00:00
-- url     : https://prove2.me/submissions/270b397e-b944-4da8-a91e-cbb0fb18d06b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_dia_dia
import Theorems.Thm_GlobalTheory_PairOp_commute_sum

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
theorem _root_.solution (c : 𝓀[k]ˣ) : (GsStar χ * dia c : Module.End ℂ (Form k n M)) = dia c * GsStar χ := by
  unfold GsStar
  exact (commute_sum (fun d => dia_dia c d) _ (fun d : 𝓀[k]ˣ => χ (-(d : 𝓀[k]))) fun d => d⁻¹).symm
end GlobalTheory.PairOp

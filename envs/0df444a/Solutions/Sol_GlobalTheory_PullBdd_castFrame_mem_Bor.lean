-- Prove2me | solution 1 for GlobalTheory.PullBdd.castFrame_mem_Bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:07.84687+00:00
-- url     : https://prove2.me/submissions/07dd1380-19e6-45a2-8732-afd72a716839

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PullBdd
theorem _root_.solution {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) : castFrame h b ∈ Bor Ψ' r := by
  subst h; exact hb
end GlobalTheory.PullBdd

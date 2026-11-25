-- Prove2me | solution 1 for GlobalTheory.PullBdd.castFrame_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:03.452825+00:00
-- url     : https://prove2.me/submissions/db40de72-3fcf-4d71-b15b-952e9f90f373

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
theorem _root_.solution {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (β : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact β x) = lact β (castFrame h x) := rfl
end GlobalTheory.PullBdd

-- Prove2me | solution 1 for GlobalTheory.PullBdd.castFrame_mem_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:08.975838+00:00
-- url     : https://prove2.me/submissions/eece8d08-0e42-4c12-bc9d-8def44e344f0

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
theorem _root_.solution {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E}
    {p0 : ℕ} {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx
end GlobalTheory.PullBdd

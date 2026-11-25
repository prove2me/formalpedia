-- Prove2me | solution 1 for GlobalTheory.PullBdd.pull_isBddSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:35.731543+00:00
-- url     : https://prove2.me/submissions/7fd38873-56d3-44d9-b0c5-df1ed3ded9de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
import Theorems.Thm_GlobalTheory_PullBdd_isBddSec_transport

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
namespace GlobalTheory.PullBdd
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type)
    [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ),
    F ∈ M.SS la → ∀ (h : U) (c : C),
      (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  intro E _ _ _ r U C _ _ M la F hF h c
  have hY := (hF (h • c)).1
  exact isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData
    ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm])
    (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c)
    (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt (M.comp_Ψ (h • c)) la)
    (fun γ hγ => M.χ_one c _ γ hγ) (fun γ hγ => M.χ_one (h • c) _ γ hγ) _ hY
end GlobalTheory.PullBdd

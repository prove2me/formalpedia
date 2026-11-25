-- Prove2me | solution 1 for GlobalTheory.AbLaw.h1Zero_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:44.45093+00:00
-- url     : https://prove2.me/submissions/0bf54a0d-0220-49f2-b0bc-3c1e8de18a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_firstCohomologyVanishes_pull_of_isIso
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_firstCohomologyVanishes_of_iso_of_isGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e →
    M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M' := by
  rintro X X' e M M' he hM hM' ⟨w, hw⟩ h0
  refine H1Iso.firstCohomologyVanishes_of_iso_of_isGen ?_ hM' w hw (H1Iso.firstCohomologyVanishes_pull_of_isIso e M h0)
  apply top_unique
  intro x _
  have hx : e.base x ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, le_pull M e le_rfl hi⟩
end GlobalTheory.AbLaw

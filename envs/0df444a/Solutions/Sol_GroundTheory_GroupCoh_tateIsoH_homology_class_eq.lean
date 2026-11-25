-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateIsoH_homology_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:10.522597+00:00
-- url     : https://prove2.me/submissions/a79a6fd1-167a-4fe0-96ba-2c9d2b77f682

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep k G) (n : ℕ) [NeZero n] :
    ∃ C : (tateComplex A).cycles n ⟶ cocycles A n,
      (tateComplex A).homologyπ n ≫ (tateIsoH A n n rfl).hom = C ≫ π A n ∧
        C ≫ iCocycles A n = (tateComplex A).iCycles n := by
  refine ⟨?C, ?h1, ?h2⟩
  case h1 =>
    dsimp only [tateIsoH, CochainComplex.ConnectData.homologyIsoPos]
    simp only [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]
    rw [HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc,
      HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc]
  case h2 =>
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc]
    simp [CochainComplex.ConnectData.restrictionGEIso]
end GroundTheory.GroupCoh

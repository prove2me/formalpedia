-- Prove2me | solution 1 for GlobalTheory.lattice_part_congr_of_phiRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:42.285511+00:00
-- url     : https://prove2.me/submissions/9f728ae9-ce4c-46c6-829f-e6fc16a1b48f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LatticePartCongrOfPhiRel
import Theorems.Thm_GlobalTheory_PhiLattice_zero_of_phiVal
import Theorems.Thm_GlobalTheory_FamFree_exists_fam_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → ∃ z : D.X, p'.y = p.y + n • z := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hn 0
  obtain ⟨t, h, h'⟩ := H s
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p w hw] at h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p' w' hw'] at h'
  have h0 : ¬ ∀ j, (s.s 0).f j = 0 := (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩
  obtain ⟨z, hz⟩ := (hs (p'.y - p.y)).1 fun h1 =>
    h0 (PhiLattice.zero_of_phiVal p p' w w' h h' (by rw [zero_add, sub_add_cancel]) h1)
  exact ⟨z, by rw [zero_add] at hz; rw [hz, add_sub_cancel]⟩
end GlobalTheory

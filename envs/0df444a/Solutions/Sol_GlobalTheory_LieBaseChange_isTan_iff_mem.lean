-- Prove2me | solution 1 for GlobalTheory.LieBaseChange.isTan_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:17.653868+00:00
-- url     : https://prove2.me/submissions/d461f8b4-83de-4667-9d33-fcd6165c4ea0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Theorems.Thm_GlobalTheory_SqZero_comp_eq_one_of_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_mem_redKer_of_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieBaseChange
open GlobalTheory.SqZero
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
namespace GlobalTheory.LieBaseChange
theorem _root_.solution (w : sp (R₀ := R') (DualNumber R') ⟶ (Over.pullback (fB R R')).obj G) :
    IsTan w ↔ pushR G w ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)) := by
  have e : IsTan w ↔ spMap ((fstD R').restrictScalars R) ≫ pushR G w = 1 := by
    rw [← pushR_spMap, IsTan]
    exact ⟨fun h => by rw [h, pushR_one], fun h => pushR_inj G (by rw [h, pushR_one])⟩
  rw [e]
  exact ⟨mem_redKer_of_section _ ((Algebra.ofId R' (DualNumber R')).restrictScalars R)
    (fun a => rfl), fun h => comp_eq_one_of_mem_redKer h _ fun a ha => ha⟩
end GlobalTheory.LieBaseChange

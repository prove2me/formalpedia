-- Prove2me | solution 1 for GlobalTheory.gtBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:22.24731+00:00
-- url     : https://prove2.me/submissions/1df5512d-3afc-4939-b672-865d457c12b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Theorems.Thm_GlobalTheory_GtBaseChange_lbIso_refl
import Theorems.Thm_GlobalTheory_GtBaseChange_isGt_extBC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GtBaseChange
namespace GlobalTheory
theorem _root_.solution : GtBaseChangeSt := by
  rintro S S' f E G _ ⟨d⟩
  refine ⟨extBC f E, AddEquiv.refl _, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 _)), fun χ => ?_,
    isGt_extBC f E G d⟩
  exact LBIso.chartPull (chartPullPull (E.O χ).L _ _ (Category.id_comp _).symm) (chartPullPull _ _ _ rfl)
    (lbIso_refl (E.O χ).isLB)
end GlobalTheory

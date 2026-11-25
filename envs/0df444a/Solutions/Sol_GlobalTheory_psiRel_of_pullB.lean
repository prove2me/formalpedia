-- Prove2me | solution 1 for GlobalTheory.psiRel_of_pullB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:21.002466+00:00
-- url     : https://prove2.me/submissions/a43a0a64-1add-4d6d-a7c2-6ead8d9dd7d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PullBValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ThetaPsiRelationOfPullbackExtensionField
import Theorems.Thm_GlobalTheory_pullB_values
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  intro R _ _ D F _ _ f s₀ h hψ χ T ρ κ y z J hJ
  have a := pullB_values R D F _ _ 1 f s₀ h χ T ρ y z J hJ
  have b := pullB_values R D F _ _ 1 f s₀ h 0 T ρ (y * cT D T χ) z J hJ
  have c := hψ χ T (ρ ≫ toUnit _) κ y z J hJ
  exact a.trans (c.trans (congrArg _ b.symm))
end GlobalTheory

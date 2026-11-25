-- Prove2me | solution 1 for GlobalTheory.ThetaLin.gs_scal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:12.914822+00:00
-- url     : https://prove2.me/submissions/73b4efc5-594f-4af8-bc76-eeffa3763c28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ThetaLin
namespace GlobalTheory.ThetaLin
theorem _root_.solution {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
end GlobalTheory.ThetaLin

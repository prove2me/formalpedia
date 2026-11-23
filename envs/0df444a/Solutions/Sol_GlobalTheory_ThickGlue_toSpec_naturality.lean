-- Prove2me | solution 1 for GlobalTheory.ThickGlue.toSpec_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:33.665411+00:00
-- url     : https://prove2.me/submissions/7eeff12c-4f82-436b-9dbd-08d10b01581c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings

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
open GlobalTheory GlobalTheory.ThickGlue
namespace GlobalTheory.ThickGlue
theorem _root_.solution {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U V : B₀.Opens} (h : U ≤ V) :
    B₀.homOfLE h ≫ toSpec p V = toSpec p U ≫ Spec.map (𝒜.map (homOfLE h).op) := by
  simp only [toSpec, Category.assoc]
  rw [← Spec.map_comp, p.naturality, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
end GlobalTheory.ThickGlue

-- Prove2me | solution 1 for GlobalTheory.gs_comp_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:49.312395+00:00
-- url     : https://prove2.me/submissions/3f7b9d8b-cc0c-4637-905a-24356a209659

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm
end GlobalTheory

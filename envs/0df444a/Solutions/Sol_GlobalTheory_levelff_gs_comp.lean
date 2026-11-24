-- Prove2me | solution 1 for GlobalTheory.levelff_gs_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:44.317075+00:00
-- url     : https://prove2.me/submissions/e9b983be-b73b-4f61-874c-6368012c1a94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfFaithfullyFlatBase

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
theorem _root_.solution {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm
end GlobalTheory

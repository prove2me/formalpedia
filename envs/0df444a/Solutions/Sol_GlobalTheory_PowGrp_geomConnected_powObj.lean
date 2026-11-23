-- Prove2me | solution 1 for GlobalTheory.PowGrp.geomConnected_powObj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:38.774113+00:00
-- url     : https://prove2.me/submissions/fc58fe27-c413-4ee4-982e-090e5fd3092e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
import Theorems.Thm_GlobalTheory_PowGrp_prop_powObj
import Theorems.Thm_GlobalTheory_PowGrp_geomConnected_of_isIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowGrp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
attribute [local instance] smooth_isMultiplicative
namespace GlobalTheory.PowGrp
theorem _root_.solution (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom] :
    ∀ n : ℕ, GeometricallyConnected (powObj G n).hom
  | 0 => geomConnected_of_isIso (𝟙 S)
  | n + 1 => by
    have := solution G n
    have : Smooth (powObj G n).hom := prop_powObj @Smooth G ‹_› n
    show GeometricallyConnected (pullback.fst G.hom (powObj G n).hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
end GlobalTheory.PowGrp

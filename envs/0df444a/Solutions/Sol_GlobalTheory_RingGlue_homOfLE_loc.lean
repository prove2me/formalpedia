-- Prove2me | solution 1 for GlobalTheory.RingGlue.homOfLE_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:11.396631+00:00
-- url     : https://prove2.me/submissions/bec76e95-d735-4248-8846-008ef5b49f92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps

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
open GlobalTheory GlobalTheory.RingGlue
namespace GlobalTheory.RingGlue
theorem _root_.solution {Y B : Scheme.{0}} {W W' : Y.Opens} {V V' : B.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (ψ : Γ(B, V) ⟶ Γ(Y, W)) (ψ' : Γ(B, V') ⟶ Γ(Y, W'))
    (h : W' ≤ W) (e : V' ≤ V)
    (H : B.presheaf.map (homOfLE e).op ≫ ψ' = ψ ≫ Y.presheaf.map (homOfLE h).op) :
    Y.homOfLE h ≫ loc hV ψ = loc hV' ψ' := by
  unfold loc
  rw [← IsAffineOpen.map_fromSpec hV hV' (homOfLE e).op, ← Spec.map_comp_assoc, H,
    Spec.map_comp_assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
end GlobalTheory.RingGlue

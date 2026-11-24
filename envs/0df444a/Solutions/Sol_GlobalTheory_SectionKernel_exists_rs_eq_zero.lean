-- Prove2me | solution 1 for GlobalTheory.SectionKernel.exists_rs_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:28.527183+00:00
-- url     : https://prove2.me/submissions/4ef5c52f-7850-4a4b-951f-41bee9db6a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
namespace GlobalTheory.SectionKernel
theorem _root_.solution {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom a = 0) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ rs X hV a = 0 := by
  obtain ⟨V, hxV, i, i', e⟩ := X.presheaf.germ_eq x hx hx a 0 (h.trans (map_zero _).symm)
  exact ⟨V, i.le, hxV, e.trans (map_zero _)⟩
end GlobalTheory.SectionKernel

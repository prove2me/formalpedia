-- Prove2me | solution 1 for GlobalTheory.UU.BiTransport.toBase_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:53.16887+00:00
-- url     : https://prove2.me/submissions/9ee9deac-b4e9-428d-99e8-4fc3d18efdaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
namespace GlobalTheory.UU.BiTransport
theorem _root_.solution {A : Over S} {A₀ : Over S₀} {E : A₀.left ⟶ A.left} (hE : IsPullback E A₀.hom A.hom ρ)
    (hw : E ≫ A.hom = A₀.hom ≫ ρ) {T : Over S₀} (x : Over.mk (T.hom ≫ ρ) ⟶ A) : ∃ x₀ : T ⟶ A₀, toBase hw x₀ = x :=
  ⟨Over.homMk (hE.lift x.left T.hom (Over.w x)) (hE.lift_snd _ _ _), Over.OverMorphism.ext (hE.lift_fst _ _ _)⟩
end GlobalTheory.UU.BiTransport

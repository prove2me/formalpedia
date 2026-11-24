-- Prove2me | solution 1 for GlobalTheory.FlatThickenings.flat_of_flat_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:04.127799+00:00
-- url     : https://prove2.me/submissions/b35ccdce-d79b-401c-a707-8491d123a130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient
import Theorems.Thm_GlobalTheory_FlatThickenings_flat_chart

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings
namespace GlobalTheory.FlatThickenings
theorem _root_.solution :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [LocallyOfFiniteType B.hom] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → Flat B.hom := by
  intro V _ _ _ B _ Y b hb hY
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
  exact IsZariskiLocalAtSource.of_openCover (P := @Flat) B.left.affineOpenCover.openCover
    fun i =>
      have : IsOpenImmersion (B.left.affineOpenCover.f i) := B.left.affineOpenCover.map_prop i
      flat_chart B.hom Y b hb hY (B.left.affineOpenCover.f i)
end GlobalTheory.FlatThickenings

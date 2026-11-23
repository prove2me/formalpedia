-- Prove2me | solution 1 for GlobalTheory.SecLift.inducing_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:24.664822+00:00
-- url     : https://prove2.me/submissions/45eec362-6dc7-4ac6-8ea9-5b312d162994

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g)
    {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X}
    {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) :
    Topology.IsInducing j := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
  exact j.isClosedEmbedding.isInducing
end GlobalTheory.SecLift

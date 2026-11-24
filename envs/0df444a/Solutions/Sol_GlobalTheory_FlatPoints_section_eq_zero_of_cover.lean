-- Prove2me | solution 1 for GlobalTheory.FlatPoints.section_eq_zero_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:55.788626+00:00
-- url     : https://prove2.me/submissions/43dcb7fc-d121-434e-9bb6-049dc8bc7e5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlatPoints
namespace GlobalTheory.FlatPoints
theorem _root_.solution {X : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}}
    (u : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (u i)] (hu : ∀ x : X, ∃ i z, u i z = x)
    (W : X.Opens) (f : Γ(X, W)) (h : ∀ i, ((u i).app W).hom f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W f 0 fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := hu x
  have hinj : Function.Injective ((u i).stalkMap z).hom :=
    (asIso ((u i).stalkMap z)).commRingCatIsoToRingEquiv.injective
  change (X.presheaf.germ W _ hx).hom f = (X.presheaf.germ W _ hx).hom 0
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, h i]
  simp
end GlobalTheory.FlatPoints

-- Prove2me | solution 1 for GlobalTheory.PsiInPull.res_toOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:14.554677+00:00
-- url     : https://prove2.me/submissions/1812deb7-e0da-48d8-b45e-821dcf83a53b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg

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
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {R : Type} [CommRing R] {U V : (Spec (CommRingCat.of R)).Opens} (h : U ≤ V) (a : R) :
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE h).op).hom (DegPre.toOpen V a) = DegPre.toOpen U a := by
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end GlobalTheory.PsiInPull

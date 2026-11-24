-- Prove2me | solution 1 for GlobalTheory.NearFibreIso.isIso_fibre_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:44.375069+00:00
-- url     : https://prove2.me/submissions/fe328303-c3e3-42fc-b43b-69c38b6e2423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_DenseFibreIso_isIso_of_fibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
namespace GlobalTheory.NearFibreIso
theorem _root_.solution {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Y}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) :
    IsIso (pullback.snd f' (pullback.fst (g ≫ s) t)) := by
  have H' : IsPullback (pullback.snd f' (pullback.fst (g ≫ s) t))
      (pullback.fst f' (pullback.fst (g ≫ s) t) ≫ g') (pullback.fst (g ≫ s) t ≫ g) f :=
    (IsPullback.of_hasPullback _ _).flip.paste_vert H
  refine DenseFibreIso.isIso_of_fibre s f t H' (pullback.snd _ _) ?_
  rw [Category.assoc, pullback.condition]
end GlobalTheory.NearFibreIso

-- Prove2me | solution 1 for GlobalTheory.SS.GI.Via.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:11.579944+00:00
-- url     : https://prove2.me/submissions/b6ab6032-ef45-4316-99ac-d740a36a105a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_over_ext_of_schemeTheoreticallyDominant
import Theorems.Thm_GlobalTheory_schemeTheoreticallyDominant_fractionField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
namespace Via
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [Flat u] {g g' : W ⟶ N.Y.left}
    (h : Via M N f u g) (h' : Via M N f u g') : g = g' := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  have := N.sep
  let Y : Over (Sp R) := Over.mk (u ≫ M.Y.hom)
  have : Flat Y.hom := inferInstanceAs (Flat (u ≫ M.Y.hom))
  have hp := ((IsPullback.of_hasPullback u M.j).paste_vert (isPullback_j M))
  have : IsSchemeTheoreticallyDominant (pullback.fst u M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have e := over_ext_of_schemeTheoreticallyDominant (Y := Y) (X := N.Y) (pullback.fst u M.j)
    (a := Over.homMk g h.1) (b := Over.homMk g' h'.1)
    ((h.2 _ _ _ pullback.condition).trans (h'.2 _ _ _ pullback.condition).symm)
  exact congr(($e).left)
end Via
end GlobalTheory.SS.GI

-- Prove2me | solution 1 for GlobalTheory.SS.Model.hom_ext_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:14.512919+00:00
-- url     : https://prove2.me/submissions/899f6e29-c642-4339-922e-d2770ee30629

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Theorems.Thm_GlobalTheory_SS_Model_quasiCompact_j
import Theorems.Thm_GlobalTheory_SS_Model_dominant_j
import Theorems.Thm_GlobalTheory_over_ext_of_schemeTheoreticallyDominant


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
open GlobalTheory GlobalTheory.SS
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS
namespace Model
theorem _root_.solution (M : Model R A) {P X : Scheme.{0}} (p : P ⟶ M.Y.left) [Flat p]
    (s : X ⟶ Sp R) [IsSeparated s] {a b : P ⟶ X} (hab : a ≫ s = b ≫ s)
    (h : pullback.fst p M.j ≫ a = pullback.fst p M.j ≫ b) : a = b := by
  have := M.dominant_j
  have := M.quasiCompact_j
  have : IsSchemeTheoreticallyDominant (pullback.fst p M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p M.j).flip
  have : IsSeparated (Over.mk s).hom := ‹_›
  have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (a ≫ s)) (X := Over.mk s)
    (pullback.fst p M.j) (a := Over.homMk a rfl) (b := Over.homMk b hab.symm) h
  exact congr(($this).left)
end Model
end GlobalTheory.SS

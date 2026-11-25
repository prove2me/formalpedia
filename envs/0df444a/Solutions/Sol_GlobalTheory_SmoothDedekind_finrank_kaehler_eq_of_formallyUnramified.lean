-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.finrank_kaehler_eq_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:07.251812+00:00
-- url     : https://prove2.me/submissions/310dcfad-0fad-49cd-8233-ff42558dd672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe

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
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution (R V L : Type*) [CommRing R] [CommRing V]
    [CommRing L] [Algebra R V] [Algebra V L] [Algebra R L] [IsScalarTower R V L]
    [Algebra.FormallyUnramified R V] :
    Module.finrank L Ω[L⁄R] = Module.finrank L Ω[L⁄V] := by
  refine (LinearEquiv.ofBijective (KaehlerDifferential.map R V L L)
    ⟨?_, KaehlerDifferential.map_surjective R V L⟩).finrank_eq
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R V L x).mp hx
  rw [Subsingleton.elim y 0, map_zero]
end GlobalTheory.SmoothDedekind

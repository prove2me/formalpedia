-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.cov_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:04.696791+00:00
-- url     : https://prove2.me/submissions/673aa3bf-29ff-40b4-b62a-f7b71658432c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp
import Theorems.Thm_GlobalTheory_SS_Smoothening_genOpen_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_single
import Theorems.Thm_GlobalTheory_SS_Smoothening_not_dvd_of_unit
import Theorems.Thm_GlobalTheory_SS_Smoothening_exists_lift
import Theorems.Thm_GlobalTheory_SS_Smoothening_cov_of_generic
import Theorems.Thm_GlobalTheory_SS_Dil_exists_lift
import Theorems.Thm_P2M_GlobalTheory_T_exists_smooth_of_defect_zero__f4ea9e03efcc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R : Type} (K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)
include hπ
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π 0 : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R', _, _, a, ha⟩
  obtain ⟨f, hf, hs⟩ := GlobalTheory.T.exists_smooth_of_defect_zero' R π hπ B hB R' a (hE R' a ha).1 (hE R' a ha).2
  exact ⟨f, fun h => not_dvd_of_unit (hE R' a ha).1 hf (h R' a ha),
    Cov.single _ hs (genOpen_away f) fun R'' _ _ b hb => exists_lift f b hb.2⟩
end GlobalTheory.SS.Smoothening

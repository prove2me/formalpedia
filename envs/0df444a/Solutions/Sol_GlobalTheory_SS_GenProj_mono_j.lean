-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.mono_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:53.160409+00:00
-- url     : https://prove2.me/submissions/2bf9857f-8b78-484d-875f-135c7f2fd23f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.GenProj
theorem _root_.solution [IsFractionRing R K] (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : Mono (pullback.fst M.Y.hom (spMap (algebraMap R K))) := inferInstance
  exact mono_comp' inferInstance this
end GlobalTheory.SS.GenProj

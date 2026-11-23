-- Prove2me | solution 1 for GlobalTheory.SS.SectionTranslation.j_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:12.321797+00:00
-- url     : https://prove2.me/submissions/4d4019e5-93f3-4ed0-a363-63cc4ff19def

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.SectionTranslation
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.SectionTranslation
theorem _root_.solution (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w M.e.inv
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    (asIso M.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]
end GlobalTheory.SS.SectionTranslation

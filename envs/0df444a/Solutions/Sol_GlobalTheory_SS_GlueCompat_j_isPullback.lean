-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.j_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:08.987201+00:00
-- url     : https://prove2.me/submissions/f3c81f79-5aa5-4c81-8215-c815b631b4be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : M.e.inv.left ≫ pullback.snd M.Y.hom (spMap (algebraMap R K)) = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w M.e.inv
  have := (IsPullback.of_horiz_isIso ⟨h⟩).paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
  rw [Category.id_comp] at this
  exact this
end GlobalTheory.SS.GlueCompat

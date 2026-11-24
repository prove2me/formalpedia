-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.app_cstR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:17:59.429008+00:00
-- url     : https://prove2.me/submissions/1bd09ae9-21f6-487e-a980-8a1dc3f7874e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Model_j_hom


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have h : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U =
      (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE M.j M.Y.hom ⊤ U _ le_top le_rfl).trans ?_
    simp only [M.j_hom]
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  refine Eq.trans congr($h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ?_
  exact congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm
end GlobalTheory.SS.OrdTwist

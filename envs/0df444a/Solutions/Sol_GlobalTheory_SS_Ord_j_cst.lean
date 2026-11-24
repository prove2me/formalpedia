-- Prove2me | solution 1 for GlobalTheory.SS.Ord.j_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:25.970877+00:00
-- url     : https://prove2.me/submissions/438c8060-809f-4916-bb77-68584b8f7b56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.Ord
theorem _root_.solution (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cst M U r) = cstK A _ (algebraMap R K r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  have h1 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (M.j ≫ M.Y.hom).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top
      = (A.hom ≫ spMap (algebraMap R K)).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    exact (Scheme.Hom.comp_appLE A.hom (spMap (algebraMap R K)) ⊤ _ _).symm
  have h3 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [h1, h2]; simp only [M.j_hom]
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h3
  exact h4.trans (congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm)
end GlobalTheory.SS.Ord

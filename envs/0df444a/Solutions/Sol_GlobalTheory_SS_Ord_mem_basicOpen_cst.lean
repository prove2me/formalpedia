-- Prove2me | solution 1 for GlobalTheory.SS.Ord.mem_basicOpen_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:02.997493+00:00
-- url     : https://prove2.me/submissions/121980e1-2903-418b-a44b-7b699714694b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cst
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff


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
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R}
omit [IsFractionRing R K]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (U : M.Y.left.Opens) (x : M.Y.left) :
    x ∈ M.Y.left.basicOpen (cst M U π) ↔ x ∈ U ∧ x ∉ M.sp := by
  rw [← rs_cst M (le_top : U ≤ ⊤)]
  refine (SetLike.ext_iff.1 (M.Y.left.basicOpen_res (cst M ⊤ π) (homOfLE (le_top : U ≤ ⊤)).op) x).trans ?_
  refine and_congr_right fun _ => ?_
  have e : cst M ⊤ π = M.Y.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)) (M.Y.hom.app_eq_appLE (U := ⊤)).symm
  rw [e]
  exact not_iff_not.1 (by rw [not_not]; exact DvrModel.notMem_basicOpen_iff M.Y.hom hπ x)
end GlobalTheory.SS.Ord

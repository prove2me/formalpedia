-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_j_eq_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:38:49.423933+00:00
-- url     : https://prove2.me/submissions/e241985e-9e27-4575-9eaf-fe28b8bccac1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_injective
import Theorems.Thm_GlobalTheory_SS_Ord_rs_rs
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j

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
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens)
    (f : Γ(A.left, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (W : M.Y.left.Opens) (hW : W ≤ U), x ∈ W ∧
      ∃ s, (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) : ∃ s, (M.j.app U).hom s = f := by
  choose W hW hx s hs using h
  have hc : U ≤ ⨆ x : U, W x.1 x.2 := fun x h => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, h⟩, hx x h⟩
  obtain ⟨g, hg, -⟩ := M.Y.left.sheaf.existsUnique_gluing' (fun x : U => W x.1 x.2) U
    (fun x => homOfLE (hW x.1 x.2)) hc (fun x => s x.1 x.2) (fun x y => by
      apply j_app_injective M
      refine (rs_j M inf_le_left _).symm.trans (Eq.trans ?_ (rs_j M inf_le_right _))
      rw [hs, hs, rs_rs, rs_rs])
  refine ⟨g, A.left.sheaf.eq_of_locally_eq' (fun x : U => M.j ⁻¹ᵁ W x.1 x.2) (M.j ⁻¹ᵁ U)
    (fun x => homOfLE (M.j.preimage_mono (hW x.1 x.2)))
    (fun y h => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨M.j y, h⟩, hx _ h⟩) _ _ fun x => ?_⟩
  refine (rs_j M (hW x.1 x.2) g).trans (Eq.trans ?_ (hs x.1 x.2))
  exact congrArg _ (hg x)
end GlobalTheory.SS.Ord

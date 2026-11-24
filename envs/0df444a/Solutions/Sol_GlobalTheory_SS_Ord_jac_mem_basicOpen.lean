-- Prove2me | solution 1 for GlobalTheory.SS.Ord.jac_mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:35.546279+00:00
-- url     : https://prove2.me/submissions/d20ce809-76d1-4da8-9fa5-1cad38c6a344

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_det_mem
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac

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
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (M : Model R A) (D : I → VF A) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (g : Γ(M.Y.left, U)) (N : AddSubgroup Γ(A.left, M.j ⁻¹ᵁ M.Y.left.basicOpen g))
    (hN : ∀ s, ∀ x ∈ N, (M.j.app (M.Y.left.basicOpen g)).hom s * x ∈ N)
    (h : ∀ t : I → Γ(M.Y.left, U), rs _ (M.j.preimage_mono (M.Y.left.basicOpen_le g))
      (jac D (M.j ⁻¹ᵁ U) fun i => (M.j.app U).hom (t i)) ∈ N) (t : I → Γ(M.Y.left, M.Y.left.basicOpen g)) :
    jac D _ (fun i => (M.j.app (M.Y.left.basicOpen g)).hom (t i)) ∈ N := by
  have hl := hU.isLocalization_basicOpen g
  refine det_mem (rs _ (M.Y.left.basicOpen_le g)) (M.j.app _).hom (fun i => (D i).D _)
    (fun i => (D i).leibniz _) (fun x => ?_) N hN (fun t => ?_) t
  · obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    exact ⟨b, c, IsLocalization.map_units _ c, e⟩
  · have := h t
    rw [rs_jac] at this
    simp only [rs_j M (M.Y.left.basicOpen_le g)] at this
    exact this
end GlobalTheory.SS.Ord

-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_pow_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:23.054943+00:00
-- url     : https://prove2.me/submissions/adffad57-87e3-4849-970e-f956fd3eef39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_rs_rs
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_mem_basicOpen_cst
import Theorems.Thm_GlobalTheory_SS_Ord_mem_range_j
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_surjective
import Theorems.Thm_GlobalTheory_SS_Model_le_refl


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
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (f : Γ(A.left, M.j ⁻¹ᵁ U)) :
    ∃ (k : ℕ) (b : Γ(M.Y.left, U)), (M.j.app U).hom b = (M.j.app U).hom (cst M U π) ^ k * f := by
  have hW := M.Y.left.basicOpen_le (cst M U π)
  have hl := hU.isLocalization_basicOpen (cst M U π)
  obtain ⟨x, hx⟩ := j_app_surjective M (U := M.Y.left.basicOpen (cst M U π))
    (fun x hx => ((mem_basicOpen_cst hπ M U x).1 hx).2) (rs _ (M.j.preimage_mono hW) f)
  obtain ⟨⟨b, _, k, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers (cst M U π)) x
  have hle : M.j ⁻¹ᵁ U ≤ M.j ⁻¹ᵁ M.Y.left.basicOpen (cst M U π) := fun y hy =>
    (mem_basicOpen_cst hπ M U _).2 ⟨hy, (mem_range_j M _).1 ⟨y, rfl⟩⟩
  refine ⟨k, b, ?_⟩
  have e' : x * rs _ hW (cst M U π ^ k) = rs _ hW b := e
  have := congrArg (fun z => rs _ hle ((M.j.app _).hom z)) e'
  simp only [map_mul, hx, ← rs_j M hW, rs_rs] at this
  have hid : ∀ z : Γ(A.left, M.j ⁻¹ᵁ U), rs A.left (le_refl (M.j ⁻¹ᵁ U)) z = z := fun z => by
    simp [rs]
  simp only [hid, map_pow] at this
  rw [← this, _root_.mul_comm]
end GlobalTheory.SS.Ord

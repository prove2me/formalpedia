-- Prove2me | solution 1 for GlobalTheory.GlueFn.existsUnique_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:25.515082+00:00
-- url     : https://prove2.me/submissions/ffb94b5e-4889-4d37-9c90-e1b38984429d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Theorems.Thm_GlobalTheory_GlueFn_le_of_forall_point
import Theorems.Thm_GlobalTheory_GlueFn_ext_val
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.GlueFn
namespace GlobalTheory.GlueFn
theorem _root_.solution {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {E : Type}
    (e : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (he : Function.Surjective e) (O : X.left.Opens) (ψ : E → ℂ)
    (h : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → ∃ (O' : X.left.Opens) (a : Γ(X.left, O')), O' ≤ O ∧
      ⊤ ≤ (e z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (e z').left ⁻¹ᵁ O' → valAt' (e z').left O' a = ψ z') :
    ∃! a : Γ(X.left, O), ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → valAt' (e z).left O a = ψ z := by
  choose U c hUO hzU hc using h
  have hcov : O ≤ ⨆ p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O}, U p.1 p.2 := by
    refine le_of_forall_point fun x hx => ?_
    obtain ⟨z, rfl⟩ := he x
    exact top_le_preimage_mono _ (le_iSup (fun p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O} => U p.1 p.2) ⟨z, hx⟩) (hzU z hx)
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.left.sheaf
    (fun p : {z // ⊤ ≤ (e z).left ⁻¹ᵁ O} => U p.1 p.2) O (fun p => homOfLE (hUO p.1 p.2)) hcov
    (fun p => c p.1 p.2) (by
      intro p q
      refine ext_val e he (U p.1 p.2 ⊓ U q.1 q.2) _ _ fun z hz => ?_
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      exact ((valAt'_map _ _ _ hz).trans (hc _ _ z h1)).trans
        ((valAt'_map _ _ _ hz).trans (hc _ _ z h2)).symm)
  have hval : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → valAt' (e z).left O s = ψ z := fun z hz => by
    rw [← hc z hz z (hzU z hz), ← hs ⟨z, hz⟩]
    exact (valAt'_map _ _ _ (hzU z hz)).symm
  exact ⟨s, hval, fun t ht => ext_val e he O t s fun z hz => (ht z hz).trans (hval z hz).symm⟩
end GlobalTheory.GlueFn

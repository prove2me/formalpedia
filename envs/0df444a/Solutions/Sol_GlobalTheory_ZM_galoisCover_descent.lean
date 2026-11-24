-- Prove2me | solution 1 for GlobalTheory.ZM.galoisCover_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:03.283504+00:00
-- url     : https://prove2.me/submissions/bc10f7bf-e7a5-4677-a6f0-344714cda699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GaloisCoverDescentAndCartesianSquares
import Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_exists_local_geom
import Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_existsUnique_desc
import Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_isPullback
import Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩
end GlobalTheory.ZM

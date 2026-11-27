-- Prove2me | solution 1 for GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:29.930385+00:00
-- url     : https://prove2.me/submissions/44498f6c-bf92-47a6-8e4d-8209f7fc28f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_GlobalTheory_smooth_square_hom
import Theorems.Thm_GlobalTheory_smooth_cube_hom
import Theorems.Thm_GlobalTheory_smooth_fourthPower_hom
import Theorems.Thm_GlobalTheory_geometricallyConnected_square_hom
import Theorems.Thm_GlobalTheory_geometricallyConnected_cube_hom
import Theorems.Thm_GlobalTheory_geometricallyConnected_fourthPower_hom
import Theorems.Thm_GlobalTheory_geometricallyIntegral_square_hom
import Theorems.Thm_GlobalTheory_geometricallyIntegral_cube_hom
import Theorems.Thm_GlobalTheory_geometricallyIntegral_fourthPower_hom
import Theorems.Thm_GlobalTheory_isIntegral_square_left
import Theorems.Thm_GlobalTheory_isIntegral_cube_left
import Theorems.Thm_GlobalTheory_isIntegral_fourthPower_left
import Theorems.Thm_GlobalTheory_isIntegral_specialFibre_of_smooth
import Theorems.Thm_GlobalTheory_isIntegral_genericFibre_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution :
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f],
      GeometricallyIntegral f ∧ (IsIntegral S → IsIntegral X)) ∧
    (∀ {S : Scheme.{u}} (A : Over S) [GrpObj A], IsAbelianScheme A ∨ IsSemiAbelian A →
      ∀ T ∈ [A, G2 A, G3 A, G4 A],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ {S : Scheme.{u}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom],
      ∀ T ∈ [G, G2 G, G3 G, G4 G],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
      [Smooth G.hom] [GeometricallyConnected G.hom], ∀ T ∈ [G, G2 G, G3 G, G4 G],
        IsIntegral T.left ∧ IsLocallyNoetherian T.left ∧
        IsIntegral (pullback T.hom (spMap (IsLocalRing.residue V))) ∧
        IsIntegral (pullback T.hom (spMap (algebraMap V (FractionRing V))))) := by
  have key : ∀ {S : Scheme.{u}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom],
      ∀ T ∈ [G, G2 G, G3 G, G4 G],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left) := by
    intro S G _ _ T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact ⟨geometricallyIntegral_of_smooth _,
        fun _ ↦ isIntegral_of_smooth_of_geometricallyConnected T.hom⟩
    · exact ⟨geometricallyIntegral_square_hom G, fun _ ↦ isIntegral_square_left G⟩
    · exact ⟨geometricallyIntegral_cube_hom G, fun _ ↦ isIntegral_cube_left G⟩
    · exact ⟨geometricallyIntegral_fourthPower_hom G, fun _ ↦ isIntegral_fourthPower_left G⟩
  refine ⟨fun f _ _ ↦ ⟨geometricallyIntegral_of_smooth f,
    fun _ ↦ isIntegral_of_smooth_of_geometricallyConnected f⟩, ?_, key, ?_⟩
  · rintro S A _ (h | h)
    all_goals
      have := h.smooth
      have := h.geomConnected
      exact key A
  · intro V _ _ _ G _ _ T hT
    obtain ⟨_, _⟩ : Smooth T.hom ∧ GeometricallyConnected T.hom := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact ⟨‹_›, ‹_›⟩
      · exact ⟨smooth_square_hom G, geometricallyConnected_square_hom G⟩
      · exact ⟨smooth_cube_hom G, geometricallyConnected_cube_hom G⟩
      · exact ⟨smooth_fourthPower_hom G, geometricallyConnected_fourthPower_hom G⟩
    exact ⟨isIntegral_of_smooth_of_geometricallyConnected T.hom,
      LocallyOfFiniteType.isLocallyNoetherian T.hom, isIntegral_specialFibre_of_smooth T.hom,
      isIntegral_genericFibre_of_smooth (FractionRing V) T.hom⟩
end GlobalTheory

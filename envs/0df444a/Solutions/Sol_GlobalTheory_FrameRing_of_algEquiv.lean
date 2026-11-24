-- Prove2me | solution 1 for GlobalTheory.FrameRing_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:48.958461+00:00
-- url     : https://prove2.me/submissions/803cb5fd-e375-469a-9d9f-ee784619979e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameRingOverTestRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {J : Type} (m : J → ℕ) {R A B : Type} [CommRing R] [Algebra K R]
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (π : R →ₐ[K] A)
    (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ) (h : FrameRing m π X s) (e : A ≃ₐ[K] B) :
    FrameRing m ((e : A →ₐ[K] B).comp π) (fun τ => (X τ).map e) (Units.map (e : A →* B) s) := by
  refine ⟨fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := (h.1 τ).map (e : A →+* B)
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨k, ⟨h1, h2, h3⟩, hu⟩ := h.2 T ψ g a hg
    refine ⟨k.comp (e.symm : B →ₐ[K] A), ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · rw [← h1]; ext x; simp
    · rw [← h2 τ]; ext i j; simp
    · rw [← h3]; simp
    · rintro k' ⟨h1', h2', h3'⟩
      have : k'.comp (e : A →ₐ[K] B) = k := by
        refine hu _ ⟨?_, fun τ => ?_, ?_⟩
        · rw [← h1']; rfl
        · rw [← h2' τ]; ext i j; simp
        · rw [← h3']; simp
      rw [← this]; ext x; simp
end GlobalTheory

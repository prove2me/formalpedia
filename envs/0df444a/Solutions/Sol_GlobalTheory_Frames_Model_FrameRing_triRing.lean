-- Prove2me | solution 1 for GlobalTheory.Frames.Model.FrameRing.triRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:39.436064+00:00
-- url     : https://prove2.me/submissions/d3efe2e8-8d19-4aec-8288-6e3a4815a423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
variable {m R}
namespace GlobalTheory.Frames.Model
namespace FrameRing
theorem _root_.solution {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) :
    let I : Ideal A := Ideal.span {x | ∃ τ i j, i < j ∧ x = X τ i j}
    TriRing m ((Ideal.Quotient.mkₐ K I).comp π) (fun τ => (X τ).map (Ideal.Quotient.mk I))
      (Units.map (Ideal.Quotient.mk I).toMonoidHom s) := by
  intro I
  have hX : ∀ τ i j, i < j → Ideal.Quotient.mk I (X τ i j) = 0 := fun τ i j hij =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨τ, i, j, hij, rfl⟩)
  refine ⟨fun τ i => ?_, fun τ i j hij => hX τ i j hij, ?_⟩
  ·
    have hd : IsUnit ((X τ).map (Ideal.Quotient.mk I)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (h.1 τ).map _
    rw [Matrix.det_of_isLowerTriangular _ (by intro i j hij; exact hX τ i j hij)] at hd
    exact IsUnit.prod_univ_iff.1 hd i
  · intro T _ _ ψ g a hd hl
    have hg : ∀ τ, IsUnit (g τ).det := fun τ => by
      rw [Matrix.det_of_isLowerTriangular _ (by intro i j hij; exact hl τ i j hij)]
      exact IsUnit.prod_univ_iff.2 (hd τ)
    obtain ⟨k, ⟨hk1, hk2, hk3⟩, hku⟩ := h.2 T ψ g a hg
    have hkX : ∀ τ i j, k (X τ i j) = g τ i j := fun τ i j => congrFun (congrFun (hk2 τ) i) j
    have hle : I ≤ RingHom.ker (k : A →+* T) := by
      apply Ideal.span_le.2
      rintro _ ⟨τ, i, j, hij, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact (hkX τ i j).trans (hl τ i j hij)
    have hI : ∀ x ∈ I, k x = 0 := fun x hx => RingHom.mem_ker.1 (hle hx)
    refine ⟨Ideal.Quotient.liftₐ I k hI, ⟨?_, fun τ => ?_, hk3⟩, ?_⟩
    · ext r
      exact AlgHom.congr_fun hk1 r
    · ext i j
      exact hkX τ i j
    · rintro k' ⟨h1, h2, h3⟩
      apply Ideal.Quotient.algHom_ext
      rw [Ideal.Quotient.liftₐ_comp]
      apply hku
      refine ⟨?_, fun τ => ?_, h3⟩
      · rw [AlgHom.comp_assoc]
        exact h1
      · ext i j
        exact congrFun (congrFun (h2 τ) i) j
end FrameRing
end GlobalTheory.Frames.Model

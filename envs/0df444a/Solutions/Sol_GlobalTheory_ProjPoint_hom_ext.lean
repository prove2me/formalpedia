-- Prove2me | solution 1 for GlobalTheory.ProjPoint.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:25.22746+00:00
-- url     : https://prove2.me/submissions/1f5449a9-521a-44d8-a7c5-cc52d8abad8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) {Y : Scheme.{u}}
    {g₁ g₂ : Spec (.of B) ⟶ Y}
    (h : ∀ (C : Type u) [CommRing C] (ψ : B →+* C) (f : A) (n : ℕ), 0 < n → f ∈ 𝒜 n →
      IsUnit (ψ (φ f)) →
      Spec.map (CommRingCat.ofHom ψ) ≫ g₁ = Spec.map (CommRingCat.ofHom ψ) ≫ g₂) : g₁ = g₂ := by
  let s : {f : A // ∃ n, 0 < n ∧ f ∈ 𝒜 n} → (CommRingCat.of B) := fun f => φ f.1
  have hs : Ideal.span (Set.range s) = ⊤ := by
    rw [_root_.eq_top_iff, ← hφ, Ideal.map_le_iff_le_comap, toIdeal_irrelevant_le]
    intro i hi x hx
    exact Ideal.subset_span ⟨⟨x, i, hi, hx⟩, rfl⟩
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨n, hn, hf⟩ := i.2
  exact h (Localization.Away (φ i.1)) (algebraMap B _) i.1 n hn hf
    (IsLocalization.Away.algebraMap_isUnit _)
end GlobalTheory.ProjPoint

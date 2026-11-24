-- Prove2me | solution 1 for GlobalTheory.normalization_basicOpen_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:16.046899+00:00
-- url     : https://prove2.me/submissions/574ab924-37ae-4170-af9c-0ab5092d5e39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (U X : Scheme.{0}) (f : U ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra;
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V ''
        (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  classical
  set B := f.normalizationDiagram.obj (Opposite.op V.1) with hB
  set ι := f.normalizationOpenCover.f V with hι
  set j := f.toNormalization with hj
  have key : ∀ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j →
      letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
      Algebra.FiniteType Γ(X, V.1) (Localization.Away b) := by
    intro b hb
    letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
    let g : Spec (.of (Localization.Away b)) ⟶ Spec B :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
    have hg : Set.range (g ≫ ι) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      apply hb
      have : g z ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this
    let h := IsOpenImmersion.lift j (g ≫ ι) hg
    have hh : h ≫ j = g ≫ ι := IsOpenImmersion.lift_fac _ _ _
    haveI : LocallyOfFiniteType (h ≫ j) := by rw [hh]; infer_instance
    haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h j
    have e : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫
        V.2.fromSpec := by
      rw [← f.toNormalization_fromNormalization, reassoc_of% hh, hι, f.ι_fromNormalization,
        ← Spec.map_comp_assoc]
      congr 2
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec) := by
      rw [← e]; infer_instance
    haveI := locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b)))) V.2.fromSpec
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    exact RingHom.finiteType_algebraMap.mp this
  have hcov : ∀ x : U, f x ∈ V.1 → ∃ b : B,
      (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j ∧
        j x ∈ ι '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
    intro x hx
    have hx' : j x ∈ Set.range ι := by
      have h1 : j x ∈ f.fromNormalization ⁻¹ᵁ V.1 := by
        show f.fromNormalization (j x) ∈ V.1
        rw [← Scheme.Hom.comp_apply, hj, f.toNormalization_fromNormalization]
        exact hx
      rw [f.fromNormalization_preimage V] at h1
      exact h1
    obtain ⟨y, hy⟩ := hx'
    have hO : IsOpen (ι ⁻¹' Set.range j) := j.isOpenEmbedding.isOpen_range.preimage ι.continuous
    obtain ⟨_, ⟨b, rfl⟩, hyb, hbO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show y ∈ ι ⁻¹' Set.range j from ⟨x, hy.symm⟩) hO
    exact ⟨b, hbO, y, hyb, hy⟩
  have hK : IsCompact (f ⁻¹' (V.1 : Set X)) := f.isCompact_preimage V.2.isCompact
  let T := {b : B // (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun b : T => j ⁻¹' (ι '' (PrimeSpectrum.basicOpen b.1 : Set (PrimeSpectrum B))))
    (fun b => (ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen b.1).2).preimage
      j.continuous)
    (by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := hcov x hx
      exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    exact key b'.1 b'.2
  · intro x hx
    obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨b.1, Finset.mem_image_of_mem _ hbt, hxb⟩
end GlobalTheory

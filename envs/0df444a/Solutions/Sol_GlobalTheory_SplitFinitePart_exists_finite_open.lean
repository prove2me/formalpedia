-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.exists_finite_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:49.211967+00:00
-- url     : https://prove2.me/submissions/d3daaebd-2c39-4978-954f-ba0eccfafc78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom
import Theorems.Thm_GlobalTheory_SplitFinitePart_exists_section_of_isIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [LocallyQuasiFinite π]
    [IsSeparated π] [QuasiCompact π] [LocallyOfFiniteType π]
    (hs : ∀ z : Z, π z = genericPoint (Sp R) →
      ∃ γ : Sp K ⟶ Z, γ ≫ π = spMap (algebraMap R K) ∧ z ∈ Set.range γ) (p : Sp R) :
    ∃ (W : (Sp R).Opens) (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme), p ∈ W ∧ ρ ≫ W.ι = H.ι ≫ π ∧ IsFinite ρ ∧
      (∀ z : Z, π z = p → z ∈ H) ∧
      ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s := by
  let j := π.toNormalization
  let g := π.fromNormalization
  have hjg : j ≫ g = π := π.toNormalization_fromNormalization
  have hjg' : ∀ z, g (j z) = π z := fun z => by rw [← Scheme.Hom.comp_apply, hjg]
  let I : Type := π ⁻¹' {genericPoint (Sp R)}
  have : Finite I := π.finite_preimage_singleton _
  choose γ hγ hγ' using fun i : I => hs i.1 i.2
  choose s hs1 hs2 using fun i : I => exists_section_of_isIntegralHom g (γ i ≫ j) (by rw [Category.assoc, hjg, hγ])
  have hgs : ∀ i y, g (s i y) = y := fun i y => by rw [← Scheme.Hom.comp_apply, hs1]; rfl
  have hcl : ∀ i, IsClosed (Set.range (s i)) := fun i => by
    have : IsClosedImmersion (s i ≫ g) := by rw [hs1]; infer_instance
    have : IsClosedImmersion (s i) := IsClosedImmersion.of_comp _ g
    exact (s i).isClosedEmbedding.isClosed_range
  have hcov : ∀ z : Z, ∃ i, s i (π z) = j z := fun z => by
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap π (genericPoint_specializes (π z))
    obtain ⟨a, ha⟩ := hγ' ⟨z', e⟩
    have h1 : j z' ∈ Set.range (s ⟨z', e⟩) :=
      ⟨spMap (algebraMap R K) a, by rw [← Scheme.Hom.comp_apply, hs2, Scheme.Hom.comp_apply, ha]⟩
    obtain ⟨y, hy⟩ := (hz'.map j.continuous).mem_closed (hcl _) h1
    refine ⟨⟨z', e⟩, ?_⟩
    rw [← hjg', ← hy, hgs]
  let good : I → Prop := fun i => s i p ∈ Set.range j
  let U : π.normalization.Opens := ⟨Set.range j \ ⋃ i : {i // ¬ good i}, Set.range (s i.1),
    j.isOpenEmbedding.isOpen_range.sdiff (isClosed_iUnion_of_finite fun i => hcl i.1)⟩
  let W : (Sp R).Opens := ⟨⋂ i : {i // good i}, s i.1 ⁻¹' U,
    isOpen_iInter_of_finite fun i => U.isOpen.preimage (s i.1).continuous⟩
  have hU : ∀ n, n ∈ Set.range j → g n = p → n ∈ U := fun n hn hp => ⟨hn, fun h => by
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp h
    apply i.2
    have : y = p := by rw [← hp, ← hy, hgs]
    subst this
    change s i.1 y ∈ Set.range j
    rw [hy]; exact hn⟩
  have hpW : p ∈ W := Set.mem_iInter.mpr fun i => hU _ i.2 (hgs _ _)
  have hgood : ∀ i y, s i y ∈ U → good i := fun i y h => by
    by_contra hn
    exact h.2 (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, y, rfl⟩)
  have hWU : ∀ i, good i → ∀ y ∈ W, s i y ∈ U := fun i hi y hy => Set.mem_iInter.mp hy ⟨i, hi⟩
  let H : Z.Opens := j ⁻¹ᵁ U ⊓ π ⁻¹ᵁ W
  have hle : H ≤ j ⁻¹ᵁ (g ⁻¹ᵁ W) := fun z hz => by
    change g (j z) ∈ W
    rw [hjg']; exact hz.2
  let a := j.resLE _ H hle
  have ha : a ≫ (g ⁻¹ᵁ W).ι = H.ι ≫ j := j.resLE_comp_ι hle
  have ha' : ∀ z, (a z).1 = j z.1 := fun z => by
    have := congrArg (fun φ : H.toScheme ⟶ _ => φ z) ha
    exact this
  have : IsOpenImmersion (a ≫ (g ⁻¹ᵁ W).ι) := by rw [ha]; infer_instance
  have : IsOpenImmersion a := IsOpenImmersion.of_comp _ (g ⁻¹ᵁ W).ι
  have hr : Set.range a = (g ⁻¹ᵁ W).ι ⁻¹' ⋃ i : {i // good i}, Set.range (s i.1) := by
    ext n
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨i, hi⟩ := hcov z.1
      exact Set.mem_iUnion.mpr ⟨⟨i, hgood i _ (by rw [hi]; exact z.2.1)⟩, π z.1, hi.trans (ha' z).symm⟩
    · intro hn
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hn
      have hy' : s i y = n.1 := hy
      have hyW : y ∈ W := by
        rw [← hgs i y, hy']; exact n.2
      have h1 := hWU i.1 i.2 y hyW
      obtain ⟨z, hz⟩ := h1.1
      refine ⟨⟨z, show j z ∈ U from hz ▸ h1, show π z ∈ W by rw [← hjg', hz, hgs]; exact hyW⟩, Subtype.ext ?_⟩
      exact (ha' _).trans (hz.trans hy')
  have : IsClosedImmersion a := IsClosedImmersion.of_isPreimmersion _ (by
    rw [hr]
    exact (isClosed_iUnion_of_finite fun i : {i // good i} => hcl i.1).preimage (g ⁻¹ᵁ W).ι.continuous)
  have hρ : (a ≫ g ∣_ W) ≫ W.ι = H.ι ≫ π := by
    rw [Category.assoc, morphismRestrict_ι, reassoc_of% ha, hjg]
  refine ⟨W, H, a ≫ g ∣_ W, hpW, hρ, ?_, fun z hz => ⟨hU _ ⟨z, rfl⟩ ((hjg' z).trans hz), show π z ∈ W from hz ▸ hpW⟩,
    fun z hz => ?_⟩
  · have : LocallyOfFiniteType ((a ≫ g ∣_ W) ≫ W.ι) := by rw [hρ]; infer_instance
    have : LocallyOfFiniteType (a ≫ g ∣_ W) := locallyOfFiniteType_of_comp _ W.ι
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, this⟩
  · obtain ⟨i, hi⟩ := hcov z
    have hg := hgood i (π z) (by rw [hi]; exact hz.1)
    have hsub : Set.range (W.ι ≫ s i) ⊆ Set.range j := by
      rintro _ ⟨w, rfl⟩
      exact (hWU i hg w.1 w.2).1
    have hl := IsOpenImmersion.lift_fac j (W.ι ≫ s i) hsub
    have hl' : ∀ w : W.toScheme, j (IsOpenImmersion.lift j (W.ι ≫ s i) hsub w) = s i w.1 := fun w => by
      rw [← Scheme.Hom.comp_apply, hl]; rfl
    refine ⟨IsOpenImmersion.lift j (W.ι ≫ s i) hsub, ?_, fun w => ⟨?_, ?_⟩, ⟨π z, hz.2⟩, ?_⟩
    · refine (congrArg (_ ≫ ·) hjg.symm).trans ?_
      simp only [reassoc_of% hl, hs1, Category.comp_id]
    · change j _ ∈ U
      rw [hl']; exact hWU i hg w.1 w.2
    · change π _ ∈ W
      rw [← hjg', hl', hgs]; exact w.2
    · apply j.isOpenEmbedding.injective
      exact (hl' _).trans hi
end GlobalTheory.SplitFinitePart

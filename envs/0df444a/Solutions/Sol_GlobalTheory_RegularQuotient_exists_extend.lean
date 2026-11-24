-- Prove2me | solution 1 for GlobalTheory.RegularQuotient.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:55:13.218284+00:00
-- url     : https://prove2.me/submissions/cc6acf0d-c91a-4927-bbd9-4df92939c42e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientSpanRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.RegularQuotient
open IsLocalRing Matrix
namespace GlobalTheory.RegularQuotient
namespace _root_.GlobalTheory.RegularQuotient
theorem _root_.solution (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by
  set N : Submodule (ResidueField Λ) (CotangentSpace Λ) :=
    Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i))
    with hN
  let b := Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)
  have hsurj : Function.Surjective
      fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y) :=
    (Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective
  choose s hs using fun j => hsurj (b j)
  refine ⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance,
    fun j => (s j : Λ), ?_, ?_⟩
  · have htop : Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤ := by
      set P := Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))
      have hNP : N ≤ P := by
        rw [hN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩
      have hmap : Submodule.map N.mkQ P = ⊤ := by
        rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩
      rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP] at hmap
      exact hmap
    rw [IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
    have key := congrArg (Submodule.map (maximalIdeal Λ).subtype) htop
    rw [← Submodule.span_image, Submodule.map_subtype_top, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at key
    exact key
  · rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin,
      ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]
end _root_.GlobalTheory.RegularQuotient
end GlobalTheory.RegularQuotient

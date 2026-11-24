-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_dominating_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:34.407498+00:00
-- url     : https://prove2.me/submissions/2e5a40ab-1c6f-44a9-a640-b165ea751d1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_valuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : LocalSubring.range (algebraMap R L) ≤ W.toLocalSubring)
    {s t : Set L} (hsf : s.Finite) (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W)
    (ht : ∀ x ∈ t, x ∈ W.nonunits)
    (h0 : (∃ r ∈ maximalIdeal R, algebraMap R L r ≠ 0) ∨ ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by
  rw [localSubring_range_le_valuationSubring_iff] at hW
  obtain ⟨g, hg⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  have hgm : ∀ r ∈ g, r ∈ maximalIdeal R := fun r hr => hg ▸ Ideal.subset_span hr
  obtain ⟨V, hV, h1, h2, h3⟩ := exists_discreteValuationSubring_of_valuationSubring W hW.1
    (t := algebraMap R L '' g ∪ t) hsf ((g.finite_toSet.image _).union htf) hs
    (by
      rintro x (⟨r, hr, rfl⟩ | hx)
      · exact hW.2 r (hgm r hr)
      · exact ht x hx)
    (by
      rcases h0 with ⟨r, hr, hr0⟩ | ⟨x, hx, hx0⟩
      · by_contra hn
        apply hr0
        have : maximalIdeal R ≤ RingHom.ker (algebraMap R L) := by
          rw [← hg, Ideal.span_le]
          intro a ha
          by_contra h
          exact hn ⟨_, Or.inl ⟨a, ha, rfl⟩, h⟩
        exact this hr
      · exact ⟨x, Or.inr hx, hx0⟩)
  refine ⟨V, hV, ?_, h2, fun x hx => h3 x (Or.inr hx)⟩
  rw [localSubring_range_le_valuationSubring_iff]
  refine ⟨h1, fun r hr => ?_⟩
  have : maximalIdeal R ≤ (maximalIdeal V).comap ((algebraMap R L).codRestrict V h1) := by
    rw [← hg, Ideal.span_le]
    intro a ha
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 a⟩)).mp (h3 _ (Or.inl ⟨a, ha, rfl⟩))
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 r⟩)).mpr (this hr)
end GlobalTheory

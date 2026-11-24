-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:46.691449+00:00
-- url     : https://prove2.me/submissions/cb1e5966-1aa0-4cba-b756-62186eee3c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_subring

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
variable {L : Type*} [Field L]
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : ∀ r, algebraMap R L r ∈ W) {s t : Set L} (hsf : s.Finite)
    (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W) (ht : ∀ x ∈ t, x ∈ W.nonunits) (h0 : ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ r, algebraMap R L r ∈ V) ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by
  classical
  obtain ⟨x₀, hx₀, hx₀0⟩ := h0
  obtain ⟨y, hyt, hy⟩ := Set.exists_max_image t W.valuation htf ⟨x₀, hx₀⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx₀0 (by simpa using hy x₀ hx₀)
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff R L).mp inferInstance
  let g : L → L := fun e => if e ∈ W then e else e⁻¹
  let G : Set L := g '' σ ∪ s ∪ (fun x => x / y) '' t ∪ {y}
  have hG : G.Finite :=
    (((σ.finite_toSet.image _).union hsf).union (htf.image _)).union (Set.finite_singleton _)
  let W' : Subalgebra R L := { W.toSubring with algebraMap_mem' := hW }
  let B := Algebra.adjoin R G
  have hBW : B ≤ W' := by
    refine Algebra.adjoin_le ?_
    rintro x (((⟨e, -, rfl⟩ | hx) | ⟨e, he, rfl⟩) | rfl)
    · change g e ∈ W
      simp only [g]
      split_ifs with h
      · exact h
      · exact (W.mem_or_inv_mem e).resolve_left h
    · exact hs x hx
    · change e / y ∈ W
      rw [← W.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ (hy e he) zero_le
    · exact W.nonunits_subset (ht _ hyt)
  have hBft : Algebra.FiniteType R B := .adjoin_of_finite hG
  have hBn : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hBn' : IsNoetherianRing B.toSubring := hBn
  have hyB : y ∈ B := Algebra.subset_adjoin (Or.inr rfl)
  have hfrac : ∀ z : L, ∃ c ∈ B.toSubring, c ≠ 0 ∧ c * z ∈ B.toSubring := by
    let F := Subfield.closure (B : Set L)
    let F' : Subalgebra R L :=
      { F.toSubring with algebraMap_mem' := fun r => Subfield.subset_closure (B.algebraMap_mem r) }
    have h1 : Algebra.adjoin R (σ : Set L) ≤ F' := by
      refine Algebra.adjoin_le fun e he => ?_
      have h2 : g e ∈ F :=
        Subfield.subset_closure (Algebra.subset_adjoin (Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩))))
      change e ∈ F
      simp only [g] at h2
      split_ifs at h2 with h
      · exact h2
      · simpa using F.inv_mem h2
    intro z
    obtain ⟨u, hu, hu', hzu⟩ := hσ z
    have hz : z ∈ F := by
      have := F.div_mem (h1 hzu) (h1 hu)
      rwa [mul_div_cancel_right₀ _ hu'.ne_zero] at this
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (B : Set L) = B.toSubring := Subring.closure_eq B.toSubring
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨1, one_mem _, one_ne_zero, by simp⟩
    · exact ⟨b, hb, hb0, by rwa [mul_div_cancel₀ _ hb0]⟩
  have hy1 : y⁻¹ ∉ B.toSubring := fun h =>
    ((W.mem_nonunits_iff_or.mp (ht y hyt)).resolve_left hy0) (hBW h)
  obtain ⟨V, hV, hBV, hyV⟩ :=
    exists_discreteValuationSubring_of_subring B.toSubring hfrac hyB hy0 hy1
  refine ⟨V, hV, fun r => hBV (B.algebraMap_mem r),
    fun x hx => hBV (Algebra.subset_adjoin (Or.inl (Or.inl (Or.inr hx)))), fun x hx => ?_⟩
  have h1 : x / y ∈ V := hBV (Algebra.subset_adjoin (Or.inl (Or.inr ⟨x, hx, rfl⟩)))
  rw [V.mem_nonunits_iff] at hyV ⊢
  rw [← V.valuation_le_one_iff] at h1
  rw [← div_mul_cancel₀ x hy0, map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le hyV
end GlobalTheory

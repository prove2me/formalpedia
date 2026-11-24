-- Prove2me | solution 1 for Mader.induce_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:51.0947+00:00
-- url     : https://prove2.me/submissions/ef09a37a-c3a2-4876-8c39-56cb91d9727b

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
public import Theorems.Thm_Mader_no_split

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)
namespace Mader
theorem _root_.solution {S : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hbig : k + 1 < S.card) (T : Set (S : Set V)) (hT : T.ncard < k + 1) :
    ((G.induce (S : Set V)).induce Tᶜ).Connected := by
  classical
  set H := G.induce (S : Set V) with hH
  have hnonempty : Nonempty (Tᶜ : Set (S : Set V)) := by
    by_contra hcon
    rw [not_nonempty_iff, Set.isEmpty_coe_sort, Set.compl_empty_iff] at hcon
    rw [hcon, Set.ncard_univ, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hT
    omega
  rw [connected_iff]
  refine ⟨?_, hnonempty⟩
  by_contra hpre
  simp only [Preconnected, not_forall] at hpre
  obtain ⟨u, w, huw⟩ := hpre
  let X : Finset V := S.filter (fun v => ∃ h : v ∈ S, (⟨v, h⟩ : (S : Set V)) ∈ T)
  let U₁ : Finset V := S.filter (fun v => ∃ h : v ∈ S, ∃ h' : (⟨v, h⟩ : (S : Set V)) ∈ Tᶜ,
      (H.induce Tᶜ).Reachable u ⟨⟨v, h⟩, h'⟩)
  let U₂ : Finset V := (S \ X) \ U₁
  apply no_split G hm hmin hP hdeg (X := X) (U₁ := U₁) (U₂ := U₂)
  · have hXT : (X : Set V) = Subtype.val '' T := by
      ext v
      simp only [X, coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨_, h, hT⟩
        exact ⟨⟨v, h⟩, hT, rfl⟩
      · rintro ⟨⟨v', hv'⟩, hT, rfl⟩
        exact ⟨hv', hv', hT⟩
    have h := Set.ncard_coe_finset X
    rw [hXT, Set.ncard_image_of_injective _ Subtype.val_injective] at h
    omega
  · ext v
    simp only [mem_union, U₂, mem_sdiff]
    constructor
    · intro hv
      by_cases h1 : v ∈ U₁
      · exact Or.inl (Or.inl h1)
      by_cases h2 : v ∈ X
      · exact Or.inr h2
      exact Or.inl (Or.inr ⟨⟨hv, h2⟩, h1⟩)
    · rintro ((h | h) | h)
      · exact (mem_filter.1 h).1
      · exact h.1.1
      · exact (mem_filter.1 h).1
  · exact disjoint_left.2 fun a h1 h2 => (mem_sdiff.1 h2).2 h1
  · refine disjoint_left.2 fun a h1 h2 => ?_
    obtain ⟨_, h, h', _⟩ := mem_filter.1 h1
    obtain ⟨_, h2', hT'⟩ := mem_filter.1 h2
    exact h' hT'
  · exact disjoint_left.2 fun a h1 h2 => (mem_sdiff.1 (mem_sdiff.1 h1).1).2 h2
  · exact ⟨u.1.1, mem_filter.2 ⟨u.1.2, u.1.2, u.2, Reachable.refl _⟩⟩
  · refine ⟨w.1.1, mem_sdiff.2 ⟨mem_sdiff.2 ⟨w.1.2, fun h => ?_⟩, fun h => ?_⟩⟩
    · obtain ⟨_, h2, hT'⟩ := mem_filter.1 h
      exact w.2 hT'
    · obtain ⟨_, h2, h', hr⟩ := mem_filter.1 h
      exact huw hr
  · intro a ha b hb hadj
    obtain ⟨_, haS, haT, hr⟩ := mem_filter.1 ha
    obtain ⟨hbSX, hbU⟩ := mem_sdiff.1 hb
    obtain ⟨hbS, hbX⟩ := mem_sdiff.1 hbSX
    have hbT : (⟨b, hbS⟩ : (S : Set V)) ∈ Tᶜ := fun h => hbX (mem_filter.2 ⟨hbS, hbS, h⟩)
    apply hbU
    refine mem_filter.2 ⟨hbS, hbS, hbT, hr.trans (Adj.reachable ?_)⟩
    simpa [hH] using hadj
end Mader

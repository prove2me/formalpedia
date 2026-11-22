-- Prove2me | solution 1 for HousingImprove.distinct_improvers
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:27:15.550525+00:00
-- url     : https://prove2.me/submissions/5ac7be0d-380d-45cd-9762-a4d9a7aa01d6

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement

set_option autoImplicit false

universe u

open HousingImprove

namespace HousingImprove.DistinctProof

theorem along_inv' {N : Type*} (p : N) : ∀ (qs : List N) (H H' : Market N),
    ImprovesAlong p qs H H' →
    H'.lt p = H.lt p ∧
      ∀ q, q ≠ p →
        (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧
        (∀ a, H'.lt q p a → H.lt q p a) := by
  intro qs
  induction qs with
  | nil =>
    intro H H' h
    simp only [ImprovesAlong] at h
    subst h
    exact ⟨rfl, fun q _ => ⟨fun _ _ _ _ => Iff.rfl, fun _ h => h, fun _ h => h⟩⟩
  | cons r qs ih =>
    intro H H' h
    obtain ⟨H₁, h1, h2⟩ := h
    obtain ⟨ih0, ih⟩ := ih H₁ H' h2
    obtain ⟨hrp, hsame, hi, hii, hiii⟩ := h1
    refine ⟨by rw [ih0, hsame p (Ne.symm hrp)], fun q hq => ?_⟩
    obtain ⟨j1, j2, j3⟩ := ih q hq
    by_cases hc : q = r
    · subst hc
      exact ⟨fun a b ha hb => (j1 a b ha hb).trans (hi a b ha hb),
        fun a h => j2 a (hii a h), fun a h => hiii a (j3 a h)⟩
    · rw [hsame q hc] at j1 j2 j3
      exact ⟨j1, j2, j3⟩

theorem construct {N : Type*} (p : N) (H' H : Market N)
    (hcond : ∀ q, q ≠ p → (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧ (∀ a, H'.lt q p a → H.lt q p a)) :
    ∀ (L : List N), (∀ q ∈ L, q ≠ p) → L.Nodup → ∀ H₀ : Market N,
      (∀ c, c ∉ L → H₀.lt c = H'.lt c) → (∀ c ∈ L, H₀.lt c = H.lt c) →
        ImprovesAlong p L H₀ H' := by
  classical
  intro L
  induction L with
  | nil =>
    intro _ _ H₀ h1 _
    have : H₀.lt = H'.lt := funext fun c => h1 c (by simp)
    show H' = H₀
    cases H₀
    cases H'
    cases this
    rfl
  | cons q L ih =>
    intro hp hnd H₀ h1 h2
    have hq : q ≠ p := hp q (by simp)
    have hqL : q ∉ L := (List.nodup_cons.mp hnd).1
    have h2q : H₀.lt q = H.lt q := h2 q (by simp)
    let H₁ : Market N :=
      { lt := fun c => if c = q then H'.lt q else H₀.lt c
        isStrictOrder := fun c => by
          by_cases h : c = q
          · simp only [if_pos h]
            exact H'.isStrictOrder q
          · simp only [if_neg h]
            exact H₀.isStrictOrder c }
    have hH₁q : H₁.lt q = H'.lt q := by
      show (if q = q then H'.lt q else H₀.lt q) = H'.lt q
      rw [if_pos rfl]
    have hH₁c : ∀ c, c ≠ q → H₁.lt c = H₀.lt c := by
      intro c hc
      show (if c = q then H'.lt q else H₀.lt c) = H₀.lt c
      rw [if_neg hc]
    refine ⟨H₁, ⟨hq, hH₁c, ?_, ?_, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [hH₁q, h2q]
      exact (hcond q hq).1 a b ha hb
    · intro a h
      rw [hH₁q]
      rw [h2q] at h
      exact (hcond q hq).2.1 a h
    · intro a h
      rw [hH₁q] at h
      rw [h2q]
      exact (hcond q hq).2.2 a h
    · apply ih (fun r hr => hp r (List.mem_cons_of_mem _ hr)) (List.nodup_cons.mp hnd).2 H₁
      · intro c hc
        by_cases hcq : c = q
        · rw [hcq, hH₁q]
        · rw [hH₁c c hcq]
          exact h1 c (by simp [hcq, hc])
      · intro c hc
        have hcq : c ≠ q := fun h => hqL (h ▸ hc)
        rw [hH₁c c hcq]
        exact h2 c (List.mem_cons_of_mem _ hc)

end HousingImprove.DistinctProof

open HousingImprove.DistinctProof in
theorem solution {N : Type u} [Fintype N] (p : N) (H H' : Market N) :
    (IsPImprovement p H H' ↔
      H'.lt p = H.lt p ∧
      ∀ q, q ≠ p →
        (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧
        (∀ a, H'.lt q p a → H.lt q p a)) ∧
    (IsPImprovement p H H' → ∃ qs : List N, qs.Nodup ∧ ImprovesAlong p qs H H') := by
  classical
  have hfwd : IsPImprovement p H H' → (H'.lt p = H.lt p ∧
      ∀ q, q ≠ p →
        (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧
        (∀ a, H'.lt q p a → H.lt q p a)) := fun ⟨qs, h⟩ => along_inv' p qs H H' h
  have hbwd : (H'.lt p = H.lt p ∧
      ∀ q, q ≠ p →
        (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧
        (∀ a, H'.lt q p a → H.lt q p a)) →
      ∃ qs : List N, qs.Nodup ∧ ImprovesAlong p qs H H' := by
    rintro ⟨h0, hcond⟩
    refine ⟨(Finset.univ.filter (fun q => q ≠ p)).toList, Finset.nodup_toList _, ?_⟩
    apply construct p H' H hcond _ (fun q hq => by simpa using hq) (Finset.nodup_toList _) H
    · intro c hc
      have : c = p := by
        by_contra h
        exact hc (by simp [h])
      rw [this, h0]
    · intro c _
      rfl
  refine ⟨⟨hfwd, fun h => ?_⟩, fun h => hbwd (hfwd h)⟩
  obtain ⟨qs, _, hqs⟩ := hbwd h
  exact ⟨qs, hqs⟩

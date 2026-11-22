-- Prove2me | solution 1 for HousingImprove.init_subAllocation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:25:34.372657+00:00
-- url     : https://prove2.me/submissions/13f76f4b-e181-425b-abec-ec9218487009

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_Step

set_option autoImplicit false

universe u

open HousingImprove

namespace HousingImprove.InitSubProof

theorem along_inv {N : Type*} (p : N) : ∀ (qs : List N) (H H' : Market N),
    ImprovesAlong p qs H H' →
    (∀ c x y, x ≠ p → y ≠ p → (H'.lt c x y ↔ H.lt c x y)) ∧
    (∀ c x, H'.lt c p x → H.lt c p x) ∧
    (H'.lt p = H.lt p) := by
  intro qs
  induction qs with
  | nil =>
    intro H H' h
    simp only [ImprovesAlong] at h
    subst h
    exact ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ h => h, rfl⟩
  | cons q qs ih =>
    intro H H' h
    obtain ⟨H₁, h1, h2⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := ih H₁ H' h2
    obtain ⟨hqp, hsame, hi, hii, hiii⟩ := h1
    refine ⟨?_, ?_, ?_⟩
    · intro c x y hx hy
      rw [ih1 c x y hx hy]
      by_cases hc : c = q
      · subst hc
        exact hi x y hx hy
      · rw [hsame c hc]
    · intro c x hx
      have := ih2 c x hx
      by_cases hc : c = q
      · subst hc
        exact hiii x this
      · rw [hsame c hc] at this
        exact this
    · rw [ih3, hsame p (Ne.symm hqp)]

end HousingImprove.InitSubProof

open HousingImprove.InitSubProof in
theorem solution {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) :
    IsSubAllocation (tildeMarket H' p Q) Set.univ (hmInit X Q).Y ∧
    subSources Set.univ (hmInit X Q).Y = {u | ∃ q ∈ Q, u = Sum.inl (X q)} ∧
    subSinks Set.univ (hmInit X Q).Y = Set.range Sum.inr := by
  classical
  obtain ⟨qs, hqs⟩ := hH
  obtain ⟨inv1, inv2, inv3⟩ := along_inv p qs H H' hqs
  have hacc : ∀ a, ¬ H'.lt a (X a) a := by
    intro a
    have h0 : ¬ H.lt a (X a) a := hX.1 a
    by_cases hXa : X a = p
    · intro h
      rw [hXa] at h h0
      exact h0 (inv2 a a h)
    · by_cases ha : a = p
      · subst ha
        rw [inv3]
        exact h0
      · rw [inv1 a (X a) a hXa ha]
        exact h0
  have hQ' : ∀ a ∈ Q, a ≠ p ∧ H'.lt a (X a) p := fun a ha => hQ.2 ha
  have hYpos : ∀ a (h : a ∈ Q), (hmInit X Q).Y (Sum.inl a) = some (Sum.inr ⟨a, h⟩) := by
    intro a h
    simp [hmInit, h]
  have hYneg : ∀ a, a ∉ Q → (hmInit X Q).Y (Sum.inl a) = some (Sum.inl (X a)) := by
    intro a h
    simp [hmInit, h]
  have hYinr : ∀ q, (hmInit X Q).Y (Sum.inr q) = none := by
    intro q
    simp [hmInit]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    refine ⟨Set.mem_univ _, Set.mem_univ _, ?_⟩
    cases a with
    | inr q => rw [hYinr] at hab; cases hab
    | inl a =>
      by_cases haQ : a ∈ Q
      · rw [hYpos a haQ] at hab
        obtain rfl := Option.some.inj hab
        simp only [Market.Acceptable, tildeMarket, tildeAcc, tildeRel, tildeIota]
        rintro (⟨_, _, h⟩ | ⟨h1, _⟩)
        · exact hacc a ((H'.isStrictOrder a).trans _ _ _ (hQ' a haQ).2 h)
        · exact h1 trivial
      · rw [hYneg a haQ] at hab
        obtain rfl := Option.some.inj hab
        simp only [Market.Acceptable, tildeMarket, tildeAcc, tildeRel, tildeIota]
        rintro (⟨_, _, h⟩ | ⟨h1, _⟩)
        · exact hacc a h
        · exact h1 ⟨hacc a, fun h => haQ h.1⟩
  · intro a b c ha hb
    cases a with
    | inr q => rw [hYinr] at ha; cases ha
    | inl a =>
      cases b with
      | inr q => rw [hYinr] at hb; cases hb
      | inl b =>
        by_cases haQ : a ∈ Q <;> by_cases hbQ : b ∈ Q
        · rw [hYpos a haQ] at ha
          rw [hYpos b hbQ] at hb
          have := (Option.some.inj ha).trans (Option.some.inj hb).symm
          simp only [Sum.inr.injEq, Subtype.mk.injEq] at this
          rw [this]
        · rw [hYpos a haQ] at ha
          rw [hYneg b hbQ] at hb
          have := (Option.some.inj ha).trans (Option.some.inj hb).symm
          cases this
        · rw [hYneg a haQ] at ha
          rw [hYpos b hbQ] at hb
          have := (Option.some.inj ha).trans (Option.some.inj hb).symm
          cases this
        · rw [hYneg a haQ] at ha
          rw [hYneg b hbQ] at hb
          have := (Option.some.inj ha).trans (Option.some.inj hb).symm
          simp only [Sum.inl.injEq] at this
          rw [X.injective this]
  · ext u
    simp only [subSources, Set.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · intro hu
      cases u with
      | inr q =>
        exact absurd (hYpos q.1 q.2) (hu (Sum.inl q.1))
      | inl b =>
        by_cases hQb : X.symm b ∈ Q
        · exact ⟨X.symm b, hQb, by simp⟩
        · have := hYneg (X.symm b) hQb
          simp only [Equiv.apply_symm_apply] at this
          exact absurd this (hu _)
    · rintro ⟨q, hq, rfl⟩ a
      cases a with
      | inr r => rw [hYinr]; simp
      | inl a =>
        by_cases haQ : a ∈ Q
        · rw [hYpos a haQ]; simp
        · rw [hYneg a haQ]
          intro h
          simp only [Option.some.injEq, Sum.inl.injEq] at h
          exact haQ (X.injective h ▸ hq)
  · ext v
    simp only [subSinks, Set.mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_range]
    cases v with
    | inl a =>
      constructor
      · intro h
        by_cases haQ : a ∈ Q
        · rw [hYpos a haQ] at h; cases h
        · rw [hYneg a haQ] at h; cases h
      · rintro ⟨q, hq⟩
        cases hq
    | inr q =>
      exact ⟨fun _ => ⟨q, rfl⟩, fun _ => hYinr q⟩

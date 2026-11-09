-- Prove2me | solution 1 for HousingImprove.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:38:08.636712+00:00
-- url     : https://prove2.me/submissions/c54403c2-225b-4c1b-9e58-89f289ccc991

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_Step

universe u

open HousingImprove in
theorem solution {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) (s₁ s₂ : HMState Q) (h₁ : HMReachable H' X p Q s₁)
    (h₁₂ : Relation.ReflTransGen (HMStep H' p Q) s₁ s₂) (a : Tilde Q) (ha : a ∉ s₂.R)
    (b₁ b₂ : Tilde Q) (hb₁ : s₁.Y a = some b₁) (hb₂ : s₂.Y a = some b₂) :
    b₁ = b₂ ∨ (tildeMarket H' p Q).lt a b₁ b₂ := by
  classical
  let Inv : HMState Q → Prop := fun s =>
    a ∈ s.R ∨ ∃ b, s.Y a = some b ∧ (b₁ = b ∨ (tildeMarket H' p Q).lt a b₁ b)
  have key : ∀ s0 s0', HMStep H' p Q s0 s0' → Inv s0 → Inv s0' := by
    intro s0 s0' hst
    induction hst with
    | step2a a' u u' _ _ hAug _ hYa =>
      intro hinv
      rcases hinv with hR | ⟨b, hb, hrel⟩
      · exact Or.inl hR
      · right
        by_cases hEq : a' = a
        · rw [hEq] at hAug hYa ⊢
          refine ⟨u, by simp, ?_⟩
          obtain ⟨-, -, -, hdisj⟩ := hAug
          rcases hdisj with ⟨hsink, -⟩ | ⟨c, hc, hlt⟩
          · have := hsink.2; rw [hb] at this; exact absurd this (by simp)
          · rw [hb] at hc
            have hbc : b = c := Option.some.inj hc
            subst hbc
            rcases hrel with h | h
            · subst h; exact Or.inr hlt
            · exact Or.inr (((tildeMarket H' p Q).isStrictOrder a).trans _ _ _ h hlt)
        · refine ⟨b, ?_, hrel⟩
          show Function.update s0.Y a' (some u) a = some b
          rw [Function.update_of_ne (Ne.symm hEq)]
          exact hb
    | step2b a' u _ _ _ haV =>
      intro hinv
      rcases hinv with hR | ⟨b, hb, hrel⟩
      · exact Or.inl hR
      · right
        by_cases hEq : a' = a
        · rw [hEq] at haV
          have := haV.2
          rw [hb] at this
          exact absurd this (by simp)
        · refine ⟨b, ?_, hrel⟩
          show Function.update s0.Y a' (some u) a = some b
          rw [Function.update_of_ne (Ne.symm hEq)]
          exact hb
    | step3 u u' _ _ _ _ _ =>
      intro hinv
      rcases hinv with hR | ⟨b, hb, hrel⟩
      · exact Or.inl (Set.mem_insert_of_mem _ hR)
      · by_cases hEq : u = a
        · left
          show a ∈ insert u s0.R
          rw [hEq]
          exact Set.mem_insert _ _
        · right
          refine ⟨b, ?_, hrel⟩
          show Function.update s0.Y u none a = some b
          rw [Function.update_of_ne (Ne.symm hEq)]
          exact hb
  have hAll : ∀ s, Relation.ReflTransGen (HMStep H' p Q) s₁ s → Inv s := by
    intro s hs
    induction hs with
    | refl => exact Or.inr ⟨b₁, hb₁, Or.inl rfl⟩
    | tail _ hst ih => exact key _ _ hst ih
  have hInv : Inv s₂ := hAll s₂ h₁₂
  rcases hInv with hR | ⟨b, hb, hrel⟩
  · exact absurd hR ha
  · rw [hb₂] at hb
    have : b₂ = b := Option.some.inj hb
    subst this
    exact hrel

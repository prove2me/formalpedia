-- Prove2me | solution 1 for IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/716134a0-3258-559a-9e34-8ff1abdffaf2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq

set_option autoImplicit false

universe u

namespace NoethIdem29

variable {B : Type u} [CommRing B]

structure Good (f : B) (s : Finset B) : Prop where
  idem : ∀ e ∈ s, IsIdempotentElem e
  ne : ∀ e ∈ s, e ≠ 0
  le : ∀ e ∈ s, e * f = e
  prim : ∀ e ∈ s, ∀ x : B, IsIdempotentElem x → x * e = 0 ∨ x * e = e
  ortho : ∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → e * e' = 0
  sum : ∑ e ∈ s, e = f

theorem good_zero : Good (0 : B) ∅ :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem good_prim {f : B} (hf : IsIdempotentElem f) (hf0 : f ≠ 0)
    (hprim : ∀ x : B, IsIdempotentElem x → x * f = 0 ∨ x * f = f) : Good f {f} :=
  ⟨by simpa using hf, by simpa using hf0, by simpa using hf.eq, by simpa using hprim,
    by simp, by simp⟩

theorem good_union [DecidableEq B] {f₁ f₂ : B} {s₁ s₂ : Finset B} (h₁ : Good f₁ s₁) (h₂ : Good f₂ s₂)
    (h12 : f₁ * f₂ = 0) : Good (f₁ + f₂) (s₁ ∪ s₂) := by
  have hcross : ∀ e ∈ s₁, ∀ e' ∈ s₂, e * e' = 0 := fun e he e' he' => by
    have : e * e' = (e * f₁) * (e' * f₂) := by rw [h₁.le e he, h₂.le e' he']
    rw [this]
    calc e * f₁ * (e' * f₂) = e * e' * (f₁ * f₂) := by ring
      _ = 0 := by rw [h12, mul_zero]
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact h₁.ne e he (by simpa [(h₁.idem e he).eq] using hcross e he e he')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rcases Finset.mem_union.mp he with h | h; exacts [h₁.idem e h, h₂.idem e h]
  · intro e he; rcases Finset.mem_union.mp he with h | h; exacts [h₁.ne e h, h₂.ne e h]
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · rw [mul_add, h₁.le e h, ← h₂.sum, Finset.mul_sum, Finset.sum_eq_zero (fun e' he' => hcross e h e' he'), add_zero]
    · rw [mul_add, h₂.le e h, ← h₁.sum, Finset.mul_sum,
        Finset.sum_eq_zero (fun e' he' => by rw [mul_comm]; exact hcross e' he' e h), zero_add]
  · intro e he; rcases Finset.mem_union.mp he with h | h; exacts [h₁.prim e h, h₂.prim e h]
  · intro e he e' he' hne
    rcases Finset.mem_union.mp he with h | h <;> rcases Finset.mem_union.mp he' with h' | h'
    · exact h₁.ortho e h e' h' hne
    · exact hcross e h e' h'
    · rw [mul_comm]; exact hcross e' h' e h
    · exact h₂.ortho e h e' h' hne
  · rw [Finset.sum_union hdisj, h₁.sum, h₂.sum]

theorem exists_good [IsNoetherianRing B] (f : B) (hf : IsIdempotentElem f) : ∃ s : Finset B, Good f s := by
  classical

  suffices H : ∀ I : Ideal B, ∀ f : B, IsIdempotentElem f → Ideal.span {1 - f} = I → ∃ s : Finset B, Good f s from
    H _ f hf rfl
  intro I
  induction I using (wellFounded_gt (α := Ideal B)).induction with
  | _ I ih =>
  intro f hf hI
  by_cases hf0 : f = 0
  · exact ⟨∅, hf0 ▸ good_zero⟩
  by_cases hprim : ∀ x : B, IsIdempotentElem x → x * f = 0 ∨ x * f = f
  · exact ⟨{f}, good_prim hf hf0 hprim⟩
  push Not at hprim
  obtain ⟨x, hx, hx0, hxf⟩ := hprim

  set f₁ := x * f with hf₁
  set f₂ := f - x * f with hf₂
  have hf₁i : IsIdempotentElem f₁ := hx.mul hf
  have hf₁f : f₁ * f = f₁ := by rw [hf₁, mul_assoc, hf.eq]
  have hf₂i : IsIdempotentElem f₂ := by
    change f₂ * f₂ = f₂
    rw [hf₂, sub_mul, mul_sub, mul_sub, hf.eq, hf₁f, mul_comm f f₁, hf₁f, hf₁i.eq, sub_self, sub_zero]
  have hf₂f : f₂ * f = f₂ := by rw [hf₂, sub_mul, hf.eq, hf₁f]
  have h12 : f₁ * f₂ = 0 := by rw [hf₂, mul_sub, hf₁f, hf₁i.eq, sub_self]
  have hsum : f₁ + f₂ = f := by rw [hf₂]; ring

  have hgt : ∀ g : B, IsIdempotentElem g → g * f = g → g ≠ f → Ideal.span {1 - g} > I := by
    intro g hg hgf hgne
    rw [← hI]
    refine lt_of_le_of_ne ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨1 - f, by rw [mul_sub, mul_one, sub_mul, one_mul, hgf]; ring⟩
    · intro heq
      have : (1 - g) ∈ Ideal.span {1 - f} := by rw [heq]; exact Ideal.mem_span_singleton_self _
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp this
      have := congrArg (· * f) hy
      simp only [mul_assoc, sub_mul, one_mul, hf.eq, sub_self, mul_zero] at this
      rw [hgf] at this
      exact hgne (sub_eq_zero.mp this.symm).symm
  have hf₂ne : f₂ ≠ f := fun h => hx0 (by rw [hf₂] at h; rw [hf₁]; linear_combination -h)
  obtain ⟨s₁, hs₁⟩ := ih _ (hgt f₁ hf₁i hf₁f hxf) f₁ hf₁i rfl
  obtain ⟨s₂, hs₂⟩ := ih _ (hgt f₂ hf₂i hf₂f hf₂ne) f₂ hf₂i rfl
  exact ⟨s₁ ∪ s₂, hsum ▸ good_union hs₁ hs₂ h12⟩

end NoethIdem29

open NoethIdem29 in
theorem solution
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    ∃ (n : ℕ) (e : Fin n → B), CompleteOrthogonalIdempotents e ∧
      ∀ i : Fin n, e i ≠ 0 ∧ ∀ x : B, IsIdempotentElem x → x * e i = 0 ∨ x * e i = e i := by
  classical
  obtain ⟨s, hs⟩ := exists_good (1 : B) IsIdempotentElem.one
  refine ⟨s.card, fun i => ((s.equivFin.symm i : s) : B), ⟨⟨fun i => hs.idem _ (s.equivFin.symm i).2, ?_⟩, ?_⟩, fun i => ⟨hs.ne _ (s.equivFin.symm i).2, hs.prim _ (s.equivFin.symm i).2⟩⟩
  · intro i j hij
    exact hs.ortho _ (s.equivFin.symm i).2 _ (s.equivFin.symm j).2
      (fun h => hij (s.equivFin.symm.injective (Subtype.ext h)))
  · rw [← hs.sum, ← Finset.sum_coe_sort s (fun e => e)]
    exact Fintype.sum_equiv s.equivFin.symm _ _ (fun i => rfl)

end S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
end P2MW
export P2MW.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq (solution)

-- Prove2me | solution 1 for Monotonicity_Theorem.definable_interval_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T20:30:43.778159+00:00
-- url     : https://prove2.me/submissions/f010dd41-a606-42df-9769-1a9f7f5738aa

import Definitions.Def_Monotonicity_Theorem_Framework

set_option autoImplicit false

open Monotonicity_Theorem

private def endpointList {R : Type} : Endpoint R → List R
  | .negInf => []
  | .finite a => [a]
  | .posInf => []

private lemma isFinite1_or {R : Type} {F₁ F₂ : Set (Power R 1)}
    (h₁ : IsFinite1 F₁) (h₂ : IsFinite1 F₂) : IsFinite1 (fun x => F₁ x ∨ F₂ x) := by
  obtain ⟨L₁, hL₁⟩ := h₁
  obtain ⟨L₂, hL₂⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_⟩
  intro x
  constructor
  · rintro (h | h)
    · exact List.mem_append.2 (Or.inl ((hL₁ x).1 h))
    · exact List.mem_append.2 (Or.inr ((hL₂ x).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ((hL₁ x).2 h)
    · exact Or.inr ((hL₂ x).2 h)

/-- Child A3: a definable subset of the line has finitely many boundary points: outside a finite
set, every open interval is either contained in it or disjoint from it. -/
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {S : Set (Power R 1)} (hS : FiniteUnionOfPointsAndIntervals D S) :
    ∃ F : Set (Power R 1), IsFinite1 F ∧
      ∀ u v : R, D.lt u v →
        (∀ x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x → ¬ F x) →
        ((openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset S ∨
          ∀ x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x → ¬ S x) := by
  induction hS with
  | empty =>
      refine ⟨fun _ => False, ⟨[], fun x => ⟨False.elim, fun h => absurd h (by simp)⟩⟩, ?_⟩
      intro u v _ _
      exact Or.inr fun x _ h => h
  | point a =>
      refine ⟨pointSet a, ⟨[a], fun x => by simp [pointSet, Power.coord1]⟩, ?_⟩
      intro u v _ havoid
      exact Or.inr fun x hx => havoid x hx
  | interval p q =>
      refine ⟨fun x => Power.coord1 x ∈ endpointList p ++ endpointList q,
        ⟨endpointList p ++ endpointList q, fun x => Iff.rfl⟩, ?_⟩
      intro u v huv havoid
      by_cases hmeet : ∃ x : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧ openInterval D p q x
      · obtain ⟨x, hxJ, hxS⟩ := hmeet
        refine Or.inl ?_
        intro y hyJ
        refine ⟨?_, ?_⟩
        · -- left endpoint
          cases p with
          | negInf => trivial
          | posInf => exact absurd hxS.1 (by simp [Endpoint.lt])
          | finite a =>
              have hax : D.lt a (x 0) := hxS.1
              have hmem : a ∈ endpointList (Endpoint.finite a) ++ endpointList q :=
                List.mem_append_left _ (by simp [endpointList])
              rcases D.trichotomy a (y 0) with h | h | h
              · exact h.1
              · exact absurd (havoid y hyJ) (by
                  simp only [not_not]
                  have : y 0 = a := h.1.symm
                  rw [Power.coord1, this]; exact hmem)
              · exact absurd (havoid (fun _ => a) ⟨D.trans hyJ.1 h.1, D.trans hax hxJ.2⟩)
                  (not_not_intro hmem)
        · -- right endpoint
          cases q with
          | posInf => trivial
          | negInf => exact absurd hxS.2 (by simp [Endpoint.lt])
          | finite c =>
              have hxc : D.lt (x 0) c := hxS.2
              have hmem : c ∈ endpointList p ++ endpointList (Endpoint.finite c) :=
                List.mem_append_right _ (by simp [endpointList])
              rcases D.trichotomy (y 0) c with h | h | h
              · exact h.1
              · exact absurd (havoid y hyJ) (by
                  simp only [not_not]
                  rw [Power.coord1, h.1]; exact hmem)
              · exact absurd (havoid (fun _ => c) ⟨D.trans hxJ.1 hxc, D.trans h.1 hyJ.2⟩)
                  (not_not_intro hmem)
      · refine Or.inr ?_
        intro x hxJ hxS
        exact hmeet ⟨x, hxJ, hxS⟩
  | union hA hB ihA ihB =>
      obtain ⟨FA, hFAfin, hFA⟩ := ihA
      obtain ⟨FB, hFBfin, hFB⟩ := ihB
      refine ⟨fun x => FA x ∨ FB x, isFinite1_or hFAfin hFBfin, ?_⟩
      intro u v huv havoid
      rcases hFA u v huv (fun x hx h => havoid x hx (Or.inl h)) with hA' | hA'
      · exact Or.inl fun x hx => Or.inl (hA' hx)
      · rcases hFB u v huv (fun x hx h => havoid x hx (Or.inr h)) with hB' | hB'
        · exact Or.inl fun x hx => Or.inr (hB' hx)
        · exact Or.inr fun x hx h => h.elim (hA' x hx) (hB' x hx)


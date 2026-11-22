-- Prove2me | solution 1 for Monotonicity_Theorem.no_good_window_locus_finite
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T21:12:22.080873+00:00
-- url     : https://prove2.me/submissions/202a1c8a-d965-4021-9818-b95e58f15feb

import Theorems.Thm_Monotonicity_Theorem_window_loci_definable
import Theorems.Thm_Monotonicity_Theorem_definable_interval_dichotomy
import Theorems.Thm_Monotonicity_Theorem_exists_monotone_subinterval

set_option autoImplicit false

open Monotonicity_Theorem

namespace NoGoodAux

variable {R : Type}

lemma isFinite1_union {F₁ F₂ : Set (Power R 1)}
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

/-- Inside any nonempty open interval one can find a subinterval avoiding a given finite
list of points. -/
lemma exists_subinterval_avoiding_list (D : DenseLinearOrderNoEndpoints R) :
    ∀ (L : List R) (u v : R), D.lt u v →
      ∃ u₁ v₁ : R, D.lt u₁ v₁ ∧
        (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
          openInterval D (Endpoint.finite u) (Endpoint.finite v) x) ∧
        (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
          x 0 ∉ L) := by
  intro L
  induction L with
  | nil =>
      intro u v huv
      exact ⟨u, v, huv, fun _ hx => hx, fun _ _ h => absurd h (by simp)⟩
  | cons a L ih =>
      intro u v huv
      obtain ⟨u₁, v₁, huv₁, hsub, havoid⟩ := ih u v huv
      by_cases ha : D.lt u₁ a ∧ D.lt a v₁
      · refine ⟨u₁, a, ha.1, ?_, ?_⟩
        · intro x hx
          exact hsub x ⟨hx.1, D.trans hx.2 ha.2⟩
        · intro x hx hmem
          rcases List.mem_cons.1 hmem with h | h
          · have hlt : D.lt (x 0) a := hx.2
            rw [← h] at hlt
            exact D.irrefl _ hlt
          · exact havoid x ⟨hx.1, D.trans hx.2 ha.2⟩ h
      · refine ⟨u₁, v₁, huv₁, hsub, ?_⟩
        intro x hx hmem
        rcases List.mem_cons.1 hmem with h | h
        · exact ha ⟨by rw [← h]; exact hx.1, by rw [← h]; exact hx.2⟩
        · exact havoid x hx h

/-- Inside any nonempty open interval one can find a subinterval avoiding a given finite set. -/
lemma exists_subinterval_avoiding_finite (D : DenseLinearOrderNoEndpoints R)
    {F : Set (Power R 1)} (hF : IsFinite1 F) (u v : R) (huv : D.lt u v) :
    ∃ u₁ v₁ : R, D.lt u₁ v₁ ∧
      (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x) ∧
      (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x → ¬ F x) := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨u₁, v₁, huv₁, hsub, havoid⟩ := exists_subinterval_avoiding_list D L u v huv
  exact ⟨u₁, v₁, huv₁, hsub, fun x hx hFx => havoid x hx ((hL x).1 hFx)⟩

/-- An infinite definable subset of the line contains a nonempty open interval. -/
lemma infinite_definable_contains_interval (D : DenseLinearOrderNoEndpoints R)
    {A : Set (Power R 1)} (hA : FiniteUnionOfPointsAndIntervals D A) (hinf : ¬ IsFinite1 A) :
    ∃ u v : R, D.lt u v ∧
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset A := by
  have key : IsFinite1 A ∨ ∃ u v : R, D.lt u v ∧
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset A := by
    clear hinf
    induction hA with
    | empty => exact Or.inl ⟨[], fun x => ⟨False.elim, fun h => absurd h (by simp)⟩⟩
    | point a => exact Or.inl ⟨[a], fun x => by simp [pointSet, Power.coord1]⟩
    | interval p q =>
        by_cases hne : ∃ x : Power R 1, openInterval D p q x
        · obtain ⟨x, hx⟩ := hne
          refine Or.inr ?_
          have hleft : ∃ u : R, Endpoint.lt D p (Endpoint.finite u) ∧ D.lt u (x 0) := by
            cases p with
            | negInf =>
                obtain ⟨u, hu⟩ := D.no_left_endpoint (x 0)
                exact ⟨u, trivial, hu⟩
            | finite a =>
                obtain ⟨u, hu1, hu2⟩ := D.dense (show D.lt a (x 0) from hx.1)
                exact ⟨u, hu1, hu2⟩
            | posInf => exact absurd hx.1 (by simp [Endpoint.lt])
          have hright : ∃ v : R, Endpoint.lt D (Endpoint.finite v) q ∧ D.lt (x 0) v := by
            cases q with
            | posInf =>
                obtain ⟨v, hv⟩ := D.no_right_endpoint (x 0)
                exact ⟨v, trivial, hv⟩
            | finite b =>
                obtain ⟨v, hv1, hv2⟩ := D.dense (show D.lt (x 0) b from hx.2)
                exact ⟨v, hv2, hv1⟩
            | negInf => exact absurd hx.2 (by simp [Endpoint.lt])
          obtain ⟨u, hpu, hux⟩ := hleft
          obtain ⟨v, hvq, hxv⟩ := hright
          refine ⟨u, v, D.trans hux hxv, ?_⟩
          intro y hy
          refine ⟨?_, ?_⟩
          · cases p with
            | negInf => trivial
            | posInf => exact absurd hx.1 (by simp [Endpoint.lt])
            | finite a => exact D.trans hpu hy.1
          · cases q with
            | posInf => trivial
            | negInf => exact absurd hx.2 (by simp [Endpoint.lt])
            | finite b => exact D.trans hy.2 hvq
        · refine Or.inl ⟨[], fun x => ⟨fun hx => absurd ⟨x, hx⟩ hne, fun h => absurd h (by simp)⟩⟩
    | union _ _ ihA ihB =>
        rcases ihA with hfa | ⟨u, v, huv, hsub⟩
        · rcases ihB with hfb | ⟨u, v, huv, hsub⟩
          · exact Or.inl (isFinite1_union hfa hfb)
          · exact Or.inr ⟨u, v, huv, fun x hx => Or.inr (hsub hx)⟩
        · exact Or.inr ⟨u, v, huv, fun x hx => Or.inl (hsub hx)⟩
  rcases key with h | h
  · exact absurd h hinf
  · exact h

end NoGoodAux

open NoGoodAux in
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hI : IsInfinite1 I) :
    IsFinite1 (setCompl (GoodWindowLocus f)) := by
  by_contra hinf
  -- the complement of the good-window locus is definable
  obtain ⟨hc, hi, hd⟩ := window_loci_definable D M f
  have hG : M.S 1 (GoodWindowLocus f) := M.union_mem hc (M.union_mem hi hd)
  have hC : M.S 1 (setCompl (GoodWindowLocus f)) := M.compl_mem hG
  obtain ⟨u, v, huv, hCsub⟩ :=
    infinite_definable_contains_interval D ((M.ominimal _).1 hC) hinf
  -- shrink so that the window is either inside the domain or misses it
  obtain ⟨F, hFfin, hFdich⟩ := definable_interval_dichotomy D ((M.ominimal I).1 f.domain_mem)
  obtain ⟨u₁, v₁, huv₁, hsub₁, havoid₁⟩ := exists_subinterval_avoiding_finite D hFfin u v huv
  rcases hFdich u₁ v₁ huv₁ havoid₁ with hIn | hOut
  · -- the window lies inside the domain: use the core o-minimal step
    obtain ⟨u₂, v₂, huv₂, hsub₂, hcase⟩ := exists_monotone_subinterval D M f u₁ v₁ huv₁ hIn
    obtain ⟨z, hz1, hz2⟩ := D.dense huv₂
    have hzmem : (fun _ => z) ∈ openInterval D (Endpoint.finite u₂) (Endpoint.finite v₂) :=
      ⟨hz1, hz2⟩
    have hz1' : (fun _ => z) ∈ openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) :=
      hsub₂ hzmem
    have hnot : ¬ GoodWindowLocus f (fun _ => z) :=
      hCsub (hsub₁ (fun _ => z) hz1')
    have hIsub : (openInterval D (Endpoint.finite u₂) (Endpoint.finite v₂)).Subset I := by
      intro x hx
      exact hIn (hsub₂ hx)
    refine hnot ?_
    rcases hcase with h | h | h
    · exact Or.inl ⟨u₂, v₂, hz1, hz2, h⟩
    · exact Or.inr (Or.inl ⟨u₂, v₂, hz1, hz2, hIsub, h⟩)
    · exact Or.inr (Or.inr ⟨u₂, v₂, hz1, hz2, hIsub, h⟩)
  · -- the window misses the domain: the function is vacuously constant there
    obtain ⟨z, hz1, hz2⟩ := D.dense huv₁
    have hzmem : (fun _ => z) ∈ openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) :=
      ⟨hz1, hz2⟩
    have hnot : ¬ GoodWindowLocus f (fun _ => z) := hCsub (hsub₁ (fun _ => z) hzmem)
    refine hnot (Or.inl ⟨u₁, v₁, hz1, hz2, ?_⟩)
    intro x hx hxJ _ _ _
    exact absurd hx (hOut x hxJ)

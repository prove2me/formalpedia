-- Prove2me | solution 2 for Monotonicity_Theorem.exists_greatest_of_list
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T20:24:12.55873+00:00
-- url     : https://prove2.me/submissions/f63b9fdf-2f9d-4ac9-8d73-440d31d246a5

import Definitions.Def_Monotonicity_Theorem_Framework
open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (hNe : L ≠ []) :
    exists M : R, M ∈ L /\ forall r : R, r ∈ L -> (D.lt r M \/ r = M) := by
  induction L with
  | nil => exact absurd rfl hNe
  | cons h t ih =>
    cases t with
    | nil =>
      refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      intro r hr
      simp at hr
      exact Or.inr hr
    | cons h2 t2 =>
      have hNet : h2 :: t2 ≠ [] := by simp
      obtain ⟨M, hM, hMax⟩ := ih hNet
      have hTri := D.trichotomy h M
      cases hTri with
      | inl h1 =>
        obtain ⟨hlt, _, _⟩ := h1
        refine ⟨M, List.mem_cons.mpr (Or.inr hM), ?_⟩
        intro r hr
        cases List.mem_cons.mp hr with
        | inl he =>
          have hlt2 : D.lt r M := by rw [he]; exact hlt
          exact Or.inl hlt2
        | inr hm => exact hMax r hm
      | inr h23 =>
        cases h23 with
        | inl h1 =>
          obtain ⟨heq, _, _⟩ := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM =>
              have hltRh : D.lt r h := by rw [←heq] at hltRM; exact hltRM
              exact Or.inl hltRh
            | inr heqRM =>
              exact Or.inr (heqRM.trans heq.symm)
        | inr h1 =>
          obtain ⟨hlt, _, _⟩ := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM => exact Or.inl (D.trans hltRM hlt)
            | inr heqRM =>
              have hltRh : D.lt r h := by rw [heqRM]; exact hlt
              exact Or.inl hltRh

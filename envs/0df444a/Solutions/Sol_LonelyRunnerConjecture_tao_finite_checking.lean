-- Prove2me | solution 1 for LonelyRunnerConjecture.tao_finite_checking
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:02:58.176993+00:00
-- url     : https://prove2.me/submissions/933ec832-74a2-4838-b08e-1973c22a4167
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
import Theorems.Thm_LefebvreVariations_lonely_runner_tao_inductive_core

set_option autoImplicit false

open LonelyRunnerConjecture

/-! The variation, verbatim (the only open step that belongs to it). -/


theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 1 ≤ n₀ →
      ((∀ n : ℕ, n ≤ n₀ → LRC n) ↔
       (∀ n : ℕ, n ≤ n₀ → ∀ v : Fin n → ℕ, (∀ i, 0 < v i) →
         Function.Injective v →
         (∀ i, (v i : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ 2)) →
         ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ)))) := by
  obtain ⟨C, hC, hV⟩ := LefebvreVariations.lonely_runner_tao_inductive_core
  refine ⟨C, hC, fun n₀ _ => ⟨?_, ?_⟩⟩
  · intro hL n hn v hpos hinj _
    obtain ⟨t, ht⟩ := hL n hn (Finset.univ.image v)
      (by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin])
      (by
        intro s hs
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
        exact hpos i)
    exact ⟨t, fun i => ht (v i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  · intro hP
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · intro S hS _
        have : S = ∅ := Finset.card_eq_zero.mp hS
        subst this
        exact ⟨0, by simp⟩
      · exact hV n hpos (fun m hm => ih m hm (by omega)) (hP n hn)

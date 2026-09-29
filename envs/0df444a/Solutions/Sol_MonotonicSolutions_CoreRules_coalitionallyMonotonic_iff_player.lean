-- Prove2me | solution 1 for MonotonicSolutions.CoreRules.coalitionallyMonotonic_iff_player
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:00:52.063502+00:00
-- url     : https://prove2.me/submissions/36720514-7009-4d20-ad6a-7bee104bb0d2

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic
import Definitions.Def_MonotonicSolutions_CoreRules_YoungGames



namespace MonotonicSolutions.CoreRules

theorem cm_player_core {n : ℕ} (φ : Game n → Fin n → ℝ) :
    IsCoalitionallyMonotonic φ ↔
      ∀ (i : Fin n) (v w : Game n), (∀ S : Finset (Fin n), i ∈ S → w.1 S ≤ v.1 S) →
        (∀ S : Finset (Fin n), i ∉ S → v.1 S = w.1 S) → φ w i ≤ φ v i := by
  classical
  constructor
  · intro hφ i
    suffices H : ∀ D : Finset (Finset (Fin n)), ∀ v w : Game n,
        (∀ S, v.1 S ≠ w.1 S → S ∈ D) →
        (∀ S : Finset (Fin n), i ∈ S → w.1 S ≤ v.1 S) →
        (∀ S : Finset (Fin n), i ∉ S → v.1 S = w.1 S) → φ w i ≤ φ v i by
      intro v w h1 h2
      exact H (Finset.univ.filter fun S => v.1 S ≠ w.1 S) v w (by simp) h1 h2
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro v w hD _ _
      have : v = w := by
        apply Subtype.ext; funext S
        by_contra h; simpa using hD S h
      rw [this]
    | insert T D hT ih =>
      intro v w hD h1 h2
      by_cases hiT : i ∈ T
      · let u : Game n := ⟨fun S => if S = T then v.1 T else w.1 S, by
          by_cases h : (∅ : Finset (Fin n)) = T
          · simp only [h, if_true]; rw [← h]; exact v.2
          · simp only [h, if_false]; exact w.2⟩
        have hu : ∀ S, u.1 S = if S = T then v.1 T else w.1 S := fun _ => rfl
        have step1 : φ w i ≤ φ u i := by
          apply hφ u w T
          · rw [hu]; simp only [if_true]; exact h1 T hiT
          · intro S hS; rw [hu, if_neg hS]
          · exact hiT
        have step2 : φ u i ≤ φ v i := by
          apply ih v u
          · intro S hS
            rw [hu] at hS
            by_cases h : S = T
            · subst h; simp at hS
            · rw [if_neg h] at hS
              have := hD S hS
              rw [Finset.mem_insert] at this
              exact this.resolve_left h
          · intro S hS; rw [hu]; split_ifs with h
            · subst h; exact le_rfl
            · exact h1 S hS
          · intro S hS; rw [hu]; split_ifs with h
            · subst h; exact absurd hiT hS
            · exact h2 S hS
        linarith
      · apply ih v w
        · intro S hS
          have := hD S hS
          rw [Finset.mem_insert] at this
          rcases this with h | h
          · subst h; exact absurd (h2 S hiT) hS
          · exact h
        · exact h1
        · exact h2
  · intro h v w T hT hS i hi
    apply h i v w
    · intro S _
      by_cases hST : S = T
      · subst hST; exact hT
      · exact (hS S hST).ge
    · intro S hiS
      apply hS
      rintro rfl; exact hiS hi

def NF (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) : ℕ :=
  if S = Finset.univ then top
  else (Finset.univ.filter (fun k => youngCoalition k ⊆ S)).sup val

lemma youngMaxFun_eq (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) :
    youngMaxFun val top S = (NF val top S : ℝ) := by
  unfold youngMaxFun NF; split_ifs <;> rfl

def xN : Fin 5 → ℕ := ![0, 1, 2, 7, 1]
def yN : Fin 5 → ℕ := ![3, 0, 0, 6, 3]

lemma chk_x : ∀ T : Finset (Fin 5), NF ![3, 3, 9, 9, 9] 11 T ≤ ∑ k ∈ T, xN k := by decide
lemma chk_y : ∀ T : Finset (Fin 5), NF ![3, 3, 9, 9, 12] 12 T ≤ ∑ k ∈ T, yN k := by decide
lemma chk_cmp : ∀ T : Finset (Fin 5), (1 ∈ T → NF ![3, 3, 9, 9, 9] 11 T ≤ NF ![3, 3, 9, 9, 12] 12 T) ∧
    (1 ∉ T → NF ![3, 3, 9, 9, 12] 12 T = NF ![3, 3, 9, 9, 9] 11 T) := by decide

end MonotonicSolutions.CoreRules

open MonotonicSolutions.CoreRules


theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ) :
    IsCoalitionallyMonotonic φ ↔
      ∀ (i : Fin n) (v w : Game n), (∀ S : Finset (Fin n), i ∈ S → w.1 S ≤ v.1 S) →
        (∀ S : Finset (Fin n), i ∉ S → v.1 S = w.1 S) → φ w i ≤ φ v i := by
  exact cm_player_core φ

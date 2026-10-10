-- Prove2me | solution 1 for OAI.Erdos3.manuscriptReciprocalProgressionTheorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T22:48:22.341408+00:00
-- url     : https://prove2.me/submissions/8e89f7f7-120d-4949-95ad-eb7bb0fc60e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos3_erdos_3

/-! OpenAI's comparator form of Erdős Problem 3 (divergent reciprocal sums force arithmetic
progressions of every length), reduced to the published `Erdos3.erdos_3`. -/

namespace Erdos3OAIGoal

open OAI.Erdos3

theorem reciprocalProgression_of_erdos_3 : ReciprocalProgressionTheorem := by
  classical
  intro A hA k
  have hA' : ¬ Summable fun a : A ↦ 1 / (a : ℝ) := by
    intro hs
    apply hA
    have hind : Summable (A.indicator fun n : ℕ ↦ 1 / (n : ℝ)) :=
      (summable_subtype_iff_indicator (s := A) (f := fun n : ℕ ↦ 1 / (n : ℝ))).1 hs
    refine hind.congr fun n ↦ ?_
    unfold reciprocalTerm
    by_cases hn : n ∈ A <;> simp [Set.indicator, hn]
  obtain ⟨k', hk', S, hSA, a, d, hcard, hS⟩ :=
    Filter.frequently_atTop.1 (Erdos3.erdos_3 A hA') (max k 2)
  have hk2 : 2 ≤ k' := le_trans (le_max_right _ _) hk'
  have hkk : k ≤ k' := le_trans (le_max_left _ _) hk'
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have hsub : S ⊆ {a} := by
        rw [hS]
        rintro x ⟨n, -, rfl⟩
        simp
      have h1 : S.encard ≤ 1 := by
        simpa using Set.encard_le_encard hsub
      rw [ENat.card_coe_set_eq] at hcard
      rw [hcard] at h1
      have : ((k' : ℕ) : ℕ∞) ≤ 1 := h1
      norm_cast at this
      omega
    · exact hd
  refine ⟨a, d, hd, fun i hi ↦ hSA ?_⟩
  rw [hS]
  exact ⟨i, by exact_mod_cast lt_of_lt_of_le hi hkk, by simp [smul_eq_mul]⟩

end Erdos3OAIGoal

open OAI.Erdos3 in
theorem solution : ReciprocalProgressionTheorem :=
  Erdos3OAIGoal.reciprocalProgression_of_erdos_3

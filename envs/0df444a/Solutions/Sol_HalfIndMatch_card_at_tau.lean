-- Prove2me | solution 1 for HalfIndMatch.card_at_tau
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:04:45.742003+00:00
-- url     : https://prove2.me/submissions/65794c2a-78e0-41e1-995a-477c81fd2219

import Mathlib
import Definitions.Def_HalfIndMatch_OnlineAlg
import Definitions.Def_HalfIndMatch_tauR

set_option autoImplicit false

open HalfIndMatch

private lemma step_mono {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n))
    (st : OnlineState n) :
    st.M ⊆ (onlineStep A G st).M ∧ (onlineStep A G st).M.card ≤ st.M.card + 1 := by
  unfold onlineStep
  split_ifs with hd
  · exact ⟨le_rfl, Nat.le_succ _⟩
  · split
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · split_ifs
      · exact ⟨le_rfl, Nat.le_succ _⟩
      · split
        · exact ⟨le_rfl, Nat.le_succ _⟩
        · split_ifs
          · exact ⟨Finset.subset_insert _ _, Finset.card_insert_le _ _⟩
          · exact ⟨le_rfl, Nat.le_succ _⟩

private lemma part1 {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) (t : ℕ) :
    At A G t ⊆ At A G (t + 1) ∧ (At A G (t + 1)).card ≤ (At A G t).card + 1 := by
  simp only [At, onlineRun]
  exact step_mono A G _

theorem solution {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) :
    (∀ t : ℕ, At A G t ⊆ At A G (t + 1) ∧ (At A G (t + 1)).card ≤ (At A G t).card + 1) ∧
    ∀ r : ℕ, 1 ≤ r → ∀ t : ℕ, tauR A G r = (t : ℕ∞) → (At A G t).card = r := by
  refine ⟨part1 A G, ?_⟩
  intro r hr t ht
  unfold tauR at ht
  split_ifs at ht with hne
  · have hmin := ht
    rw [Nat.cast_inj] at hmin
    have hmem := Finset.min'_mem _ hne
    rw [hmin, Finset.mem_filter, Finset.mem_Icc] at hmem
    obtain ⟨⟨h1, htn⟩, hrt⟩ := hmem
    apply le_antisymm _ hrt
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hstep := (part1 A G s).2
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      have : (At A G 0).card = 0 := by simp [At, onlineRun]
      omega
    · by_contra hcon
      have hle : r ≤ (At A G s).card := by omega
      have hs_mem : s ∈ (Finset.Icc 1 n).filter fun t => r ≤ (At A G t).card := by
        rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hs, by omega⟩, hle⟩
      have := Finset.min'_le _ _ hs_mem
      omega
  · exact absurd ht (by simp)

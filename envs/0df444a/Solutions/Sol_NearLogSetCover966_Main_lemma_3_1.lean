-- Prove2me | solution 1 for NearLogSetCover966.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:53:19.392139+00:00
-- url     : https://prove2.me/submissions/61e6cf28-1ee1-4111-9774-0cf470da4174

import Definitions.Def_NearLogSetCover966_Main_Core
set_option autoImplicit false
open NearLogSetCover966.Main

theorem solution (n : ℕ) (L : Set (Bits n)) (Φ : Bits n → Bool)
    (hΦ : Monotone Φ) :
    (∀ x : Bits n, Φ x ≤ localAcceptance L Φ x) ∧
      ∀ x ∈ L, Φ x = localAcceptance L Φ x := by
  classical
  have forward (x : Bits n) : Φ x ≤ localAcceptance L Φ x := by
    by_cases hx : Φ x = true
    · have hp : ∀ z ∈ L, Φ z = true ∨ ∃ a : Fin n, z a = false ∧ x a = true := by
        intro z hz
        by_cases hle : x ≤ z
        · left
          have hh : true ≤ Φ z := by simpa only [hx] using hΦ hle
          cases hz' : Φ z
          · rw [hz'] at hh
            exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hh)
          · rfl
        · right
          have hex : ∃ a, ¬ x a ≤ z a := by simpa only [Pi.le_def, not_forall] using hle
          obtain ⟨a, ha⟩ := hex
          refine ⟨a, ?_⟩
          cases hza : z a <;> cases hxa : x a <;> simp_all
      have hl : localAcceptance L Φ x = true := by
        simpa only [localAcceptance, decide_eq_true_eq] using hp
      simp [hx, hl]
    · have hx' : Φ x = false := Bool.eq_false_iff.mpr hx
      simp [hx']
  refine ⟨forward, ?_⟩
  intro x hx
  apply le_antisymm (forward x)
  by_cases hp : localAcceptance L Φ x = true
  · have hall : ∀ z ∈ L, Φ z = true ∨ ∃ a : Fin n, z a = false ∧ x a = true := by
      simpa only [localAcceptance, decide_eq_true_eq] using hp
    rcases hall x hx with h | ⟨a, ha, hb⟩
    · simp [h]
    · simp_all
  · have hp' : localAcceptance L Φ x = false := Bool.eq_false_iff.mpr hp
    simp [hp']

-- Prove2me | solution 1 for GlobalTheory.block_is_the_run
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:53.3814+00:00
-- url     : https://prove2.me/submissions/843c2dec-8049-47c3-b4e7-bc88df7afbee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BlockIsTheRun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n p t : ℕ) (a : ℕ → ℤ) (c : ℤ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    p + t ≤ n → p < t → n - (p + t) < t → (∀ j, p ≤ j → j < p + t → a j = a p) →
    (1 ≤ p → a p < a (p - 1)) → (p + t < n → a (p + t) < a p) →
    (∀ i < t, ∃ j < n, a j - j = c - i) → c = a p - p := by
  intro n p t a c hmono hpt hpt' hn hrun hleft hright hwin
  obtain ⟨j0, hj0n, hj0⟩ := hwin 0 (by omega)

  have key : ∀ i, i < t → j0 + i < n ∧ a (j0 + i) = a j0 := by
    intro i
    induction i with
    | zero => intro _; simpa using hj0n
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨j, hjn, hj⟩ := hwin (i + 1) hi
      push_cast at hj hj0
      have hge : j0 + i + 1 ≤ j := by
        by_contra hlt
        have := hmono j (j0 + i) (by omega) h1
        omega
      have hle := hmono (j0 + i) j (by omega) hjn
      have hj' : j = j0 + i + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [show j0 + (i + 1) = j by omega]
      omega
  have hq := (key (t - 1) (by omega)).1
  have hconst : ∀ k, j0 ≤ k → k < j0 + t → a k = a j0 := by
    intro k h1 h2
    have := (key (k - j0) (by omega)).2
    rwa [show j0 + (k - j0) = k by omega] at this
  rcases lt_trichotomy j0 p with h | h | h
  ·
    exfalso
    have e1 := hconst (p - 1) (by omega) (by omega)
    have e2 := hconst p (by omega) (by omega)
    have := hleft (by omega)
    omega
  · subst h
    push_cast at hj0
    omega
  ·
    exfalso
    have e1 := hconst (p + t - 1) (by omega) (by omega)
    have e2 := hconst (p + t) (by omega) (by omega)
    have e3 := hrun (p + t - 1) (by omega) (by omega)
    have := hright (by omega)
    omega
end GlobalTheory

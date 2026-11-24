-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Segments.shufcomb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:38:47.094389+00:00
-- url     : https://prove2.me/submissions/43492a9c-85b2-4b0c-82d2-87ed34490629

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StrictAntiOfTwoExceptions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Segments
namespace GlobalTheory.CompanionTheory.Segments
theorem _root_.solution (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  intro a b hab
  by_cases hbi : b = i
  · by_cases haj : a = j
    · rw [hbi, haj, hi, hj]
      omega
    · exact h2 a b hab haj (by rw [hbi]; exact hij)
  · by_cases hai : a = i
    · by_cases hbj : b = j
      · exfalso
        have hij' : i < j := by
          rw [← hai, ← hbj]
          exact hab
        obtain ⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by
          by_contra hc
          push_neg at hc
          have key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val := by
            intro k hk
            by_cases h : (⟨k, hk⟩ : Fin l) = i
            · left
              exact congrArg Fin.val h
            · right
              exact congrArg Fin.val (hc ⟨k, hk⟩ h)
          have k0 := key 0 (by omega)
          have k1 := key 1 (by omega)
          have k2 := key 2 (by omega)
          omega
        rcases lt_or_gt_of_ne hci with hc | hc
        · have h3 := h1 c j (lt_trans hc hij') hci (Ne.symm hij)
          have h4 := hw c
          omega
        · have h3 := h2 i c hc hij hcj
          omega
      · exact h2 a b hab (by rw [hai]; exact hij) hbj
    · exact h1 a b hab hai hbi
end GlobalTheory.CompanionTheory.Segments

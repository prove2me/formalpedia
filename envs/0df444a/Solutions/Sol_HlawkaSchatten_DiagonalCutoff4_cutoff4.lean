-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.cutoff4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T00:46:23.164983+00:00
-- url     : https://prove2.me/submissions/c6a525cf-9cec-46b4-8eda-e41c11990bc7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_four_to_six
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_cutoff6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
/- This is a reduction with one OPEN finite-interval dependency. -/
theorem solution :
    ∀ p : ℝ, 4 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp6 : 6 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff6.cutoff6 p hp6
  apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p (by linarith)
  exact HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six p hp (by linarith)

#print axioms solution

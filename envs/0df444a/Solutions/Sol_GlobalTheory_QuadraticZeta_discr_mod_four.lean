-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.discr_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:28:28.990735+00:00
-- url     : https://prove2.me/submissions/577d6557-ad22-40ee-9e16-c283c379eb69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (h2 : finrank ℚ K = 2) : discr K % 4 = 0 ∨ discr K % 4 = 1 := by
  obtain ⟨-, t, n, -, -, hD⟩ := exists_basis h2
  rcases Int.even_or_odd' t with ⟨k, rfl | rfl⟩
  · left
    rw [hD, show (2 * k) ^ 2 - 4 * n = 4 * (k ^ 2 - n) by ring, Int.mul_emod_right]
  · right
    rw [hD, show (2 * k + 1) ^ 2 - 4 * n = 1 + 4 * (k ^ 2 + k - n) by ring, Int.add_mul_emod_self_left]
    rfl
end GlobalTheory.QuadraticZeta

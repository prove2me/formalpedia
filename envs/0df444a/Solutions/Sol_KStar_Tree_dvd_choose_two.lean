-- Prove2me | solution 1 for KStar.Tree.dvd_choose_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:34.712547+00:00
-- url     : https://prove2.me/submissions/7566bc99-48ac-47c5-bf18-418bc3fb2697

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_OneAddPow
import Theorems.Thm_KStar_Tree_exists_eq_of_mod_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
namespace KStar.Tree
theorem _root_.solution {q n : ℕ} (hq : q % (2 * n) = 1) : n ∣ q.choose 2 := by
  obtain ⟨c, rfl⟩ := exists_eq_of_mod_eq_one hq
  rw [Nat.choose_two_right, Nat.add_sub_cancel,
    show (2 * n * c + 1) * (2 * n * c) = 2 * (n * ((2 * n * c + 1) * c)) by ring,
    Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right _ _
end KStar.Tree

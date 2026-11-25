-- Prove2me | solution 1 for KStar.Tree.nsmul_eq_self_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:41.482866+00:00
-- url     : https://prove2.me/submissions/79b8c522-4955-401d-bc45-b473ad8acf64

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
theorem _root_.solution {W : Type} [AddCommGroup W] {q n : ℕ} (hq : q % (2 * n) = 1) (h : ∀ m : W, n • m = 0)
    (m : W) : q • m = m := by
  obtain ⟨c, rfl⟩ := exists_eq_of_mod_eq_one hq
  rw [show 2 * n * c = n * (2 * c) by ring, add_smul, mul_smul, h, zero_add, one_smul]
end KStar.Tree

-- Prove2me | solution 1 for KStar.Tree.exists_eq_of_mod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:31.814149+00:00
-- url     : https://prove2.me/submissions/deb962da-5b15-481e-8b96-076400dcd110

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_OneAddPow

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
theorem _root_.solution {q n : ℕ} (hq : q % (2 * n) = 1) : ∃ c, q = 2 * n * c + 1 := by
  refine ⟨q / (2 * n), ?_⟩
  have h := Nat.div_add_mod q (2 * n)
  rw [hq] at h
  exact h.symm
end KStar.Tree

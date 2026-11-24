-- Prove2me | solution 1 for KStar.Tree.mod_two_mul_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:38.598182+00:00
-- url     : https://prove2.me/submissions/5845a80c-ee80-4bce-a073-a384ff9818a4

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
theorem _root_.solution {q l k M : ℕ} (hl : l.Prime) (hk : k ≤ M) (hq : q % (2 * l ^ M) = 1) :
    q % (2 * l ^ k) = 1 := by
  have hd : 2 * l ^ k ∣ 2 * l ^ M := Nat.mul_dvd_mul_left 2 (pow_dvd_pow l hk)
  rw [← Nat.mod_mod_of_dvd q hd, hq]
  apply Nat.mod_eq_of_lt
  have h1 : 1 ≤ l ^ k := Nat.one_le_pow k l hl.pos
  omega
end KStar.Tree

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:12.938526+00:00
-- url     : https://prove2.me/submissions/327ecaf4-1607-40e3-b6ab-045d5ef34345

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_coeff_pow_prime_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {e : ℕ}
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution (c : ℕ → k) : ∀ i, (recPoly (p ^ e) c 0 i).coeff 0 = 0 := by
  have hq0 : (0 : ℕ) ≠ p ^ e := (pow_pos hp.out.pos e).ne
  intro i
  induction i with
  | zero => simp [recPoly, coeff_X_pow, hq0]
  | succ i ih =>
    simp [recPoly, coeff_pow_prime_pow, ih, hp.out.ne_zero]
end GroundTheory.PAdicHodge.SemilinearResidue

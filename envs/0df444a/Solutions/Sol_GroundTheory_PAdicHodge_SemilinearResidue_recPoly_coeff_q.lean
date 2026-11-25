-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:28.746057+00:00
-- url     : https://prove2.me/submissions/4577e47c-ae88-45ef-ba5d-df7910b99d91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_coeff_pow_prime_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_one

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
theorem _root_.solution (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ j, (recPoly (p ^ e) c ε j).coeff (p ^ e) = c j := by
  have h2 := two_le_pow (p := p) he
  have hq0 : p ^ e ≠ 0 := by omega
  intro j
  cases j with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, coeff_C, hp.out.ne_zero]
  | succ j =>
    simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, Nat.div_self (by omega : 0 < p ^ e),
      recPoly_coeff_one he, hp.out.ne_zero]
end GroundTheory.PAdicHodge.SemilinearResidue

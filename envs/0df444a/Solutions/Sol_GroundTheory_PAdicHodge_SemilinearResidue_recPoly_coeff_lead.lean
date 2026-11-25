-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.recPoly_coeff_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:35.450838+00:00
-- url     : https://prove2.me/submissions/6531dcc3-fe8c-4a8e-9271-b46436b9c553

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_coeff_pow_prime_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_q

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
theorem _root_.solution (he : 0 < e) (c : ℕ → k) (ε : k) (j : ℕ) :
    ∀ t, (recPoly (p ^ e) c ε (j + t)).coeff ((p ^ e) ^ (t + 1)) = c j ^ (p ^ e) ^ t := by
  have h2 := two_le_pow (p := p) he
  intro t
  induction t with
  | zero => simpa using recPoly_coeff_q he c ε j
  | succ t ih =>
    have hne : (p ^ e) ^ (t + 1 + 1) ≠ p ^ e := by
      intro h
      have : (p ^ e) ^ (t + 1 + 1) = p ^ e * (p ^ e) ^ (t + 1) := by ring
      have h3 : 2 ≤ (p ^ e) ^ (t + 1) := le_trans h2 (Nat.le_self_pow (by omega) _)
      nlinarith
    have hdvd : p ^ e ∣ (p ^ e) ^ (t + 1 + 1) := dvd_pow_self _ (by omega)
    have hdiv : (p ^ e) ^ (t + 1 + 1) / p ^ e = (p ^ e) ^ (t + 1) := by
      rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    rw [show j + (t + 1) = (j + t) + 1 by ring, recPoly, coeff_add, coeff_pow_prime_pow,
      if_pos hdvd, hdiv, ih, coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero, add_zero, ← pow_mul,
      pow_succ]
end GroundTheory.PAdicHodge.SemilinearResidue

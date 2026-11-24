-- Prove2me | solution 1 for GlobalTheory.legendre_divided_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:40.3659+00:00
-- url     : https://prove2.me/submissions/169df686-2694-467d-b931-680af03e3675

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DividedPowersValuations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.PairingDivisionLocalBalance.DivPow := by
  refine ⟨?_, ?_, ?_⟩
  · intro l m hl hl2 hm
    haveI : Fact l.Prime := ⟨hl⟩
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l (n := m) (by omega)
    have hl3 : 3 ≤ l := by
      have := hl.two_le
      omega
    have h2 : 2 * padicValNat l m.factorial ≤ (l - 1) * padicValNat l m.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    constructor <;> omega
  · intro m hm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := padicValNat_factorial_lt_of_ne_zero 2 (n := m) (by omega)
    omega
  · intro j
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, mul_comm, padicValNat_factorial_mul]
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
end GlobalTheory

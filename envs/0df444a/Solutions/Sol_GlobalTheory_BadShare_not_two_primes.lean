-- Prove2me | solution 1 for GlobalTheory.BadShare.not_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:58.381305+00:00
-- url     : https://prove2.me/submissions/ef17f644-82bf-4174-b68c-340e56d70bd6

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
attribute [local instance] GlobalTheory.BadShare.factPrimeThree
namespace GlobalTheory.BadShare
theorem _root_.solution {l a n p : ℕ} (hl : l.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ∣ n) (h3 : p ∣ n) : ¬ n ∣ l ^ a := by
  intro h
  have e1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 (Nat.prime_two.dvd_of_dvd_pow (h2.trans h))
  have e2 := (Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow (h3.trans h))
  exact hp2 (e2.trans e1.symm)
end GlobalTheory.BadShare

-- Prove2me | solution 1 for OAI.Erdos3.distinct_prime_moduli_coprime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:20:06.739428+00:00
-- url     : https://prove2.me/submissions/ce0ea911-cb84-4988-82d8-450784f71491

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem distinct_prime_moduli_coprime {J : Type*} (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N) :
    Pairwise (fun i j => Nat.Coprime (N i) (N j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.distinct_prime_moduli_coprime.{u_1} := @OAI.Erdos3.distinct_prime_moduli_coprime.{u_1}

-- Prove2me | solution 1 for OAI.Erdos3.boundedPrime_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T15:39:00.819782+00:00
-- url     : https://prove2.me/submissions/3b4d4085-9a1a-48ba-a0f2-4e512bd9b952

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_OAIErdos3B094

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_injective (Q : ℕ) : Function.Injective (boundedPrime Q) := Subtype.val_injective

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.boundedPrime_injective := @OAI.Erdos3.boundedPrime_injective

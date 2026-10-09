-- Prove2me | solution 1 for OAI.Erdos3.affineMandatoryPrimes_outside_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:24:10.792318+00:00
-- url     : https://prove2.me/submissions/f008d287-ca73-47af-bf99-f330e9ec5159

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

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

open scoped BigOperators Classical

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

section

namespace Erdos3

open scoped Classical

theorem mem_affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (i : ι) :
    i ∈ affineMandatoryPrimes prime ξ P ↔ (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P := by
  simp only [affineMandatoryPrimes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem affineMandatoryPrimes_outside_inverse {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) {ξ P : ℝ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineMandatoryPrimes prime ξ P ⊆ K) (i : ι) (hi : i ∉ K) :
    (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  have ht : 0 < affineComparisonPrimeThreshold ξ P := by unfold affineComparisonPrimeThreshold; positivity
  have hp : affineComparisonPrimeThreshold ξ P ≤ (prime i : ℝ) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hi (hK ((mem_affineMandatoryPrimes prime ξ P i).mpr h))
  simpa only [affineComparisonContraction, one_div] using one_div_le_one_div_of_le ht hp

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affineMandatoryPrimes_outside_inverse.{u_1} := @OAI.Erdos3.affineMandatoryPrimes_outside_inverse.{u_1}

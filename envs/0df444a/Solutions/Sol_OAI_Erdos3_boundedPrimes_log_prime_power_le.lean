-- Prove2me | solution 1 for OAI.Erdos3.boundedPrimes_log_prime_power_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:24:18.958821+00:00
-- url     : https://prove2.me/submissions/7ec6b6d6-147b-4604-94fe-43fbb457c1f1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1340

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialForecastPath

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialForecastPath


end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem boundedPrimes_log_prime_power_le_oai (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p ^ Nat.log p Q ≤ Q := by
  intro p hp
  exact boundedPrimePower_le Q ⟨p, hp⟩

namespace VectorPolynomial

open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialForecastPath


end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialSlicedForecastPath


end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialSlicedForecastPath


end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix


namespace ActualFixedSpatialSlicedForecastPath




end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.boundedPrimes_log_prime_power_le_oai := @OAI.Erdos3.boundedPrimes_log_prime_power_le_oai

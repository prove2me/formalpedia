-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:21:14.102696+00:00
-- url     : https://prove2.me/submissions/8409543e-bfc3-4e96-acc7-c49f8ed9c694

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical


namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical


namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointGoodCutoff_bounds_oai {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    0 ≤ preparedRelativeEndpointGoodLog Ptest ∧
    1 ≤ preparedRelativeEndpointGoodCutoff Ptest ∧
    Real.exp (2 * Ptest) ≤ (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ∧
    (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ≤
      Real.exp (preparedRelativeEndpointGoodLog Ptest) := by
  refine ⟨by unfold preparedRelativeEndpointGoodLog; positivity,
    one_le_ceil_exp _, Nat.le_ceil _, ?_⟩
  exact ceil_exp_le_exp_add_one (by positivity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff_bounds_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff_bounds_oai

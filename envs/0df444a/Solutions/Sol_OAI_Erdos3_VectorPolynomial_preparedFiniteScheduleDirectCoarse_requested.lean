-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse_requested
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T03:47:55.394371+00:00
-- url     : https://prove2.me/submissions/92ba8599-2fa8-487f-a21c-81326b6f9cb0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B187

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectCoarse_requested {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) :
    requestedCoarse ≤ preparedFiniteScheduleDirectCoarse gainLog requestedCoarse :=
  le_max_right _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse_requested.{u_1} := @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse_requested.{u_1}

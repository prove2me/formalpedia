-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:18:11.843654+00:00
-- url     : https://prove2.me/submissions/d1825859-a4a5-4be9-9da1-43c25839e61e

import Mathlib
import Definitions.Def_OAIQ039C069

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_mul_oai (a b : ℕ →ᵇ A) : sequenceTrace τ ω (leftRestricted τ ω (a*b))=
    sequenceTrace τ ω (leftRestricted τ ω (b*a)) := by
  apply tendsto_nhds_unique (tendsto_trace τ ω (a*b))
  simpa only [BoundedContinuousFunction.mul_apply,hτ] using tendsto_trace τ ω (b*a)

end TracialSequence

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialSequence.trace_mul_oai.{u_1} := @OAI.Kadison.TracialSequence.trace_mul_oai.{u_1}

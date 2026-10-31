-- Prove2me | solution 1 for OAI.Generator.Tracial.boundedPartialResidual_mem_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:28.666089+00:00
-- url     : https://prove2.me/submissions/4cb2a3ee-526f-4f93-9e00-77cb693114aa

import Mathlib
import Definitions.Def_OAIQ129G012

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem boundedPartialResidual_mem_q129_oai (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) (j : ℕ) :
    ((boundedPartialResidual v).val j).val ∈ N := by
  have hs : (v j).support.val.val ∈ N := by
    rw [← (v j).unitary.initial]
    have hstar : star ((v j).val.val) ∈ N.toStarSubalgebra :=
      star_mem (show (v j).val.val ∈ N.toStarSubalgebra from hv j)
    exact N.mul_mem hstar (hv j)
  exact N.sub_mem N.one_mem hs

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.boundedPartialResidual_mem_q129_oai.{u_1} := @OAI.Generator.Tracial.boundedPartialResidual_mem_q129_oai.{u_1}

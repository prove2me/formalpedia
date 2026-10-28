-- Prove2me | solution 1 for OAI.Kadison.IrreducibleTowerAveraging.hull_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:43:27.092986+00:00
-- url     : https://prove2.me/submissions/1c3ac1f3-4e72-4ae2-91a2-95a222dd8094

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C038

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleTowerAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ in
omit [∀ n, Nonempty (ι n)] in
lemma hull_trace_oai (a : M) :
    ∀ x∈closedConvexHull ℝ (orbit M τ stage hmono a), inner ℂ (vacuum τ) x=τ a := by
  apply closedConvexHull_min
  · rintro x ⟨u,rfl⟩
    change inner ℂ (vacuum τ) (algebraVector τ ((u.val:M)*a*star (u.val:M)))=τ a
    rw [inner_vacuum_algebraVector,hτ,←mul_assoc]
    rw [u.val.property.1,one_mul]
  · exact (convex_singleton (τ a)).linear_preimage
      ((innerSL ℂ (vacuum τ)).toLinearMap.restrictScalars ℝ)
  · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IrreducibleTowerAveraging.hull_trace_oai.{u_1, u_2} := @OAI.Kadison.IrreducibleTowerAveraging.hull_trace_oai.{u_1, u_2}

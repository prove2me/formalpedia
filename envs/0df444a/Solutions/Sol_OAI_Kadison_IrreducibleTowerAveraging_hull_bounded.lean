-- Prove2me | solution 1 for OAI.Kadison.IrreducibleTowerAveraging.hull_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:43:04.946733+00:00
-- url     : https://prove2.me/submissions/0bec85f2-3fcf-4478-8604-fa6a95e1a1fa

import Mathlib
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C042

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRelativeCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.NormalRelativeCommutant

open TracialGNS NormalGNS

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M)

lemma vector_unitball_convex :
    Convex ℝ {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
  have hh := (convex_closedBall (0:M) 1).linear_image ((algebraVector τ).restrictScalars ℝ)
  simpa only [Metric.closedBall,dist_zero_right,LinearMap.coe_restrictScalars,Set.mem_ofPred_eq,
    Set.image,exists_prop] using hh

end Kadison.NormalRelativeCommutant

end

end
end

end OAI
end

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

omit [∀ n, Nonempty (ι n)] in
lemma hull_bounded_oai (hnormal : BoundedWOTContinuous M τ) (a : M) (ha : ‖a‖≤1) :
    closedConvexHull ℝ (orbit M τ stage hmono a) ⊆
      {x : τ.GNS | ∃ b : M, ‖b‖≤1 ∧ algebraVector τ b=x} := by
  apply closedConvexHull_min _ (NormalRelativeCommutant.vector_unitball_convex M τ)
    (vector_unitball_isClosed M τ hnormal)
  rintro x ⟨u,rfl⟩
  refine ⟨(u.val:M)*a*star (u.val:M),?_,rfl⟩
  have hn : ‖(u.val:M)*a*star (u.val:M)‖=‖a‖ := by
    exact (CStarRing.norm_mul_coe_unitary _ (star u.val)).trans
      (CStarRing.norm_coe_unitary_mul u.val a)
  rwa [hn]

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IrreducibleTowerAveraging.hull_bounded_oai.{u_1, u_2} := @OAI.Kadison.IrreducibleTowerAveraging.hull_bounded_oai.{u_1, u_2}

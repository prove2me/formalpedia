-- Prove2me | solution 1 for OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:38:58.957698+00:00
-- url     : https://prove2.me/submissions/183c6049-da75-4866-8808-7d1948907e9a

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

lemma intertwines (a : A) :
    (embedding τ φ ξ hτ).toContinuousLinearMap.comp (τ.gnsStarAlgHom a)=
      (φ a).comp (embedding τ φ ξ hτ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have hl : τ.gnsStarAlgHom a (TracialGNS.algebraVector τ b)=
      TracialGNS.algebraVector τ (a*b) := TracialGNS.left_coe τ a b
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hl,embedding_coe,
    map_mul,mul_apply_eq_comp]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulVectorGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

variable (M : VonNeumannAlgebra H)

lemma gnsEmbedding_intertwines_oai (a : M) (v : (restricted x M).GNS) (n : ℕ) :
    gnsEmbedding x M ((restricted x M).gnsStarAlgHom a v) n=a.val (gnsEmbedding x M v n) := by
  exact congrArg (fun T : (restricted x M).GNS →L[ℂ] InfiniteAmplification.Space ℕ H => T v n)
    (VectorGNS.intertwines (restricted x M)
      ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)).comp M.subtype) (vector x)
      (fun a => (vector_inner x a.val).symm) a)

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines_oai.{u_1} := @OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines_oai.{u_1}

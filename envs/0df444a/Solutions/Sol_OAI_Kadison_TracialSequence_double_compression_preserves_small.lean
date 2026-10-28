-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.double_compression_preserves_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:43:27.560249+00:00
-- url     : https://prove2.me/submissions/e8120ebe-8840-4b56-89ad-40525281f1e6

import Mathlib
import Definitions.Def_OAIQ039C072
import Definitions.Def_OAIQ039D000
import Theorems.Thm_OAI_Kadison_TracialSequence_double_embedding_small

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma compression_on_preserved (T : H →L[ℂ] H) (x y : τ.GNS)
    (hxy : T (embedding τ φ ξ hτ x)=embedding τ φ ξ hτ y) :
    compression τ φ ξ hτ T x=y := by
  change (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint
    (T (embedding τ φ ξ hτ x))=y
  rw [hxy]
  have he := congrArg (fun B : τ.GNS →L[ℂ] τ.GNS => B y)
    (LinearIsometry.adjoint_comp_self (embedding τ φ ξ hτ))
  exact he

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequenceOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ)

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma act_constant (T : E →L[ℂ] F) (x : E) :
    act ω (BoundedContinuousFunction.const ℕ T) (constant ω E x)=constant ω F (T x) := by
  rw [constant_apply,act_coe,constant_apply]
  congr 1

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence ReducingRepresentation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma compressed_constant (S : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    compressed τ ω S (constantIn τ ω x)=constantIn τ ω (S x) := by
  change (boundedSubspace τ ω).orthogonalProjectionOnto
    (act ω (BoundedContinuousFunction.const ℕ S) (constant ω τ.GNS x))=_
  rw [act_constant]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (constantIn τ ω (S x))

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDoubleCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor FreeBlocks

lemma double_compression_preserves_small_oai {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    doubleCompressionLeft τ ω M hconst hτ hM hone T x=doubleCompressionRight τ ω M hconst hτ hM hone T x := by
  unfold doubleCompressionLeft doubleCompressionRight
  apply VectorGNS.compression_on_preserved
  calc
    _ = compressed τ ω T (constantIn τ ω x) := congrArg (compressed τ ω T)
      (double_embedding_small τ ω M hconst hτ hM hone x)
    _ = constantIn τ ω (T x) := compressed_constant τ ω T x
    _ = _ := (double_embedding_small τ ω M hconst hτ hM hone (T x)).symm

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.double_compression_preserves_small_oai := @OAI.Kadison.TracialSequence.double_compression_preserves_small_oai

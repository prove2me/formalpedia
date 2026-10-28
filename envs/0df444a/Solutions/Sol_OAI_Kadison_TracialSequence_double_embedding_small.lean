-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.double_embedding_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:43:26.483794+00:00
-- url     : https://prove2.me/submissions/b7380e2a-d3b3-47f2-b60c-82cf090dd4fc

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C072
import Definitions.Def_OAIQ039D000

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

lemma double_embedding_small_oai {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1) (x : τ.GNS) :
    doubleEmbeddingLeft τ ω M hconst hτ hM hone x=constantIn τ ω x := by
  unfold doubleEmbeddingLeft
  let : SeminormedAddCommGroup (subalgebraState τ ω hτ M hM hone).functional.PreGNS :=
    doubleCompressionPreGNS (subalgebraState τ ω hτ M hM hone).functional
  refine (algebraVector_dense τ).induction_on x (isClosed_eq
    ((VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
      M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
      (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))).continuous.comp
      (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
        (constantHom τ ω M hconst) (constant_trace τ ω M hconst)).continuous)
    (constantIn τ ω).continuous) ?_
  intro a
  have ha := originalEmbedding_coe τ (subalgebraState τ ω hτ M hM hone)
    (constantHom τ ω M hconst) (constant_trace τ ω M hconst) a
  refine (congrArg (VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
    (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))) ha).trans ?_
  exact (VectorGNS.embedding_coe (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
    (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))
    (constantHom τ ω M hconst a)).trans (by
    change leftRestricted τ ω (constantSequence a) (sequenceVacuum τ ω)=_
    rw [leftRestricted_vacuum]
    apply Subtype.ext
    exact vector_const τ ω a)

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.double_embedding_small_oai := @OAI.Kadison.TracialSequence.double_embedding_small_oai

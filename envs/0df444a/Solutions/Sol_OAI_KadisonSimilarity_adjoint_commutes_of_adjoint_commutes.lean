-- Prove2me | solution 1 for OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:22:52.339979+00:00
-- url     : https://prove2.me/submissions/4d46e1ef-95c5-4db0-90cc-102e959006c6

import Mathlib
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelRepeatedOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical multiplicity operators on repeated-letter words

Compression to one normalized repeated word defines the degree-wise operator.
The invariant-intertwiner classification proves that this same operator acts
on every repeated-letter word. Adjoint compatibility follows from the concrete
compression formula.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {G : ℕ → Type*}
  [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)]
  [∀ n, CompleteSpace (G n)]
  {H : Type*}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {A : ℕ → Type*}
  [∀ s, Fintype (A s)]
  [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)

variable (Y : H →L[ℂ] H)

/-- Commutation with an adjoint yields the required commutation for the
adjoint of the ambient operator. -/
theorem adjoint_commutes_of_adjoint_commutes_oai (Y Q : H →L[ℂ] H)
    (h : Y.comp Q.adjoint = Q.adjoint.comp Y) : Y.adjoint.comp Q = Q.comp Y.adjoint := by
  have h' := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h'.symm

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes_oai.{u_2} := @OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes_oai.{u_2}

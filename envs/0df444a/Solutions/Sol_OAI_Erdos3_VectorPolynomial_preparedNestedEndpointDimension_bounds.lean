-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimension_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T03:59:33.129975+00:00
-- url     : https://prove2.me/submissions/fca0b03b-262d-43fe-9f5f-7f032d689b64

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B185

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointDimensionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedNestedEndpointDimensionExponent_two_le (s : ℕ) :
    2 ≤ preparedNestedEndpointDimensionExponent s :=
  (exists_endpointDimension_uniform_budget s).choose_spec.1

theorem preparedNestedEndpointDimension_bounds
    (s m : ℕ) (hm : m ≤ s) (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer inner : ℕ) {Bstruct pnum : ℝ}
    (hA : preparedNestedEndpointDimensionExponent s ≤ A)
    (houter : 1 ≤ outer) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (nX M : ℕ) (hnX : (nX : ℝ) ≤ Bstruct) (hM : (M : ℝ) ≤ Bstruct) :
    allocatedComparisonDimension m pnum ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) ∧
    ((nX + m * M : ℕ) : ℝ) ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) := by
  have hAtwo := (preparedNestedEndpointDimensionExponent_two_le s).trans hA
  have hlocal := (exists_endpointDimension_uniform_budget s).choose_spec.2 m hm
    hB hnum nX M hnX hM
  have hwork := preparedFiniteForward_shiftedPower_le_work A
    (preparedNestedEndpointDimensionExponent s) constants innerDepth hAtwo hA hB
  have hseed : preparedFiniteForwardWork A constants innerDepth Bstruct ≤
      candidateNestedForwardSeed A constants innerDepth outer Bstruct := by
    simpa only [candidateNestedForwardSeed_succ, candidateNestedForwardSeed_zero] using
      candidateNestedForwardSeed_monotone A constants innerDepth hAtwo hB houter
  have hparameter := le_preparedFiniteForwardParameter A constants inner
    (candidateNestedForwardSeed_nonneg A constants innerDepth outer hB)
  exact ⟨hlocal.1.trans (hwork.trans (hseed.trans hparameter)),
    hlocal.2.trans (hwork.trans (hseed.trans hparameter))⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimension_bounds := @OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimension_bounds

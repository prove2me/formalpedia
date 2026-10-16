-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedRelativeFinalExtraction_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:12:38.280326+00:00
-- url     : https://prove2.me/submissions/797775e3-3ca5-48d1-895b-90de8c36e7b4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1344

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical



end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal


namespace AllocatedExternalCandidateSamplerFamily


end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeFinalExtraction_power_oai
    (m degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) :
    ∃ passagePower : ℕ, 2 ≤ passagePower ∧ ∀ p : ℝ, 0 ≤ p →
      let t := preparedRelativeFinalEnvelope degree basePower inputPower
        preparationPower requiredPower discount p
      spatialPatchExtractionCost (recoveredKernelScalarBudget
        (preparedFinalScalarBudget m degree t)) ≤ (p + 2) ^ passagePower := by
  let X : Polynomial ℕ := Polynomial.X
  let t : Polynomial ℕ := 2 + (X + 2) ^ preparationPower + (X + 2) ^ requiredPower +
    ((X + 2) ^ basePower + 2) ^ inputPower + Polynomial.C ⌈discount⁻¹⌉₊ +
      (X + 2) ^ basePower + Polynomial.C degree * X
  let B : Polynomial ℕ := 2048 * t ^ 3 +
    (t + 2) ^ (preparedIntegralBasisExponent m + 1) + 2 * t + 1 + Polynomial.C degree * t
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (20 * (8 * (B + 1) ^ 2 + 1) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, t, X, preparedRelativeFinalEnvelope, preparedFinalScalarBudget,
    recoveredKernelScalarBudget, spatialPatchExtractionCost, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedRelativeFinalExtraction_power_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedRelativeFinalExtraction_power_oai

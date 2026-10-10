-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_nativeBudget_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T18:03:53.278174+00:00
-- url     : https://prove2.me/submissions/060778d0-aae1-4586-9b2e-19de7910844b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B146

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedModularGeneralDetectorResources_nativeBudget_eq
    {α : Type*} [Semiring α] (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L L' : α) :
    (preparedModularGeneralDetectorResources K dim P L).nativeBudget =
      (preparedModularGeneralDetectorResources K dim P L').nativeBudget := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_nativeBudget_eq.{u_1} := @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_nativeBudget_eq.{u_1}

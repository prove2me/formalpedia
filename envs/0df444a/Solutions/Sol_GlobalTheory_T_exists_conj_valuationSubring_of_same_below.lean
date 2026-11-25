-- Prove2me | solution 1 for GlobalTheory.T.exists_conj_valuationSubring_of_same_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:38:38.757881+00:00
-- url     : https://prove2.me/submissions/15c9357b-fde3-46d9-aef1-1b5a0006b9ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelowStatement
import Theorems.Thm_GlobalTheory_conj_places_of_same_prime_below


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  first | exact @GlobalTheory.conj_places_of_same_prime_below | exact GlobalTheory.conj_places_of_same_prime_below | (intros; apply GlobalTheory.conj_places_of_same_prime_below <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for N25.chi71_inertia_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:58.637344+00:00
-- url     : https://prove2.me/submissions/a5496fc4-2abd-4fa9-bcc3-58e21a889012

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section

namespace N25

local instance prime5_N25_chi71_inertia_eq_one_sc85c0b : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance prime71_N25_chi71_inertia_eq_one_sc85c0b : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The mod-71 cyclotomic character is unramified at five. -/
theorem _root_.solution (τ : G5) (hτ : τ ∈ I5) :
    ExtCitation.cycloChar 71 (r5 τ) = 1 := by
  exact ExtCitation.cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia 71 q5 (by decide) hτ

end N25

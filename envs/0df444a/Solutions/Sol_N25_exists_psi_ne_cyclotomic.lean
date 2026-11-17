-- Prove2me | solution 1 for N25.exists_psi_ne_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:41.673201+00:00
-- url     : https://prove2.me/submissions/a255b883-e910-437c-b079-e0252815f822

import Theorems.Thm_N25_psi_inertia_witness
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_chi71_inertia_eq_one

set_option autoImplicit false

namespace N25

local instance primeSeventyOneCharacterDistinction_s6977e0 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Inertia at five distinguishes the quintic cusp character from the
mod-seventy-one cyclotomic character. -/
theorem _root_.solution :
    ∃ σ : Gal, (psi σ : ZMod 71) ≠ (ExtCitation.cycloChar 71 σ : ZMod 71) := by
  obtain ⟨τ, hτ, hψ⟩ := psi_inertia_witness
  refine ⟨r5 τ, ?_⟩
  rw [hψ, chi71_inertia_eq_one τ hτ]
  decide

end N25

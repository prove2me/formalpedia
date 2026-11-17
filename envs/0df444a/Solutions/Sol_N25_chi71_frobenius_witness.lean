-- Prove2me | solution 1 for N25.chi71_frobenius_witness
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:57.203858+00:00
-- url     : https://prove2.me/submissions/89bc5179-e237-458a-83bc-6f4e815e142f

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section

namespace N25

local instance prime5_N25_chi71_frobenius_witness_s91800c : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance prime71_N25_chi71_frobenius_witness_s91800c : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Arithmetic Frobenius acts by five on the mod-71 cyclotomic line. -/
theorem _root_.solution :
    ∃ φ : G5, (ExtCitation.primeLocalPlace q5).IsFrobeniusAt (r5 φ) 5 ∧
      ExtCitation.cycloChar 71 (r5 φ) = ZMod.unitOfCoprime 5 (by decide) := by
  obtain ⟨φ,hφ⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal q5
  refine ⟨φ,hφ,?_⟩
  apply ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
    71 (ExtCitation.cycloChar 71) ?_ 5 (by decide) (by decide)
    (ExtCitation.primeLocalPlace q5) (ExtCitation.liesOverPrime_primeLocalPlace q5) (r5 φ) hφ
  intro σ μ hμ
  have h := modularCyclotomicCharacter.spec
    (L := AlgebraicClosure ℚ) (ExtCitation.card_rootsOfUnity_eq_self 71) σ.toRingEquiv
    (rootsOfUnity.mkOfPowEq μ hμ).property
  exact h

end N25

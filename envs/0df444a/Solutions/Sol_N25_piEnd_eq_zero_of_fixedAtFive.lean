-- Prove2me | solution 1 for N25.piEnd_eq_zero_of_fixedAtFive
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:13.701184+00:00
-- url     : https://prove2.me/submissions/9c833921-d135-4015-854d-0ca53418a312

import Theorems.Thm_N25_fixed_eq_zero_of_K2_rows
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section

namespace N25

local instance prime71_N25_piEnd_eq_zero_of_fixedAtFive_se93ae7 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- A locally fixed point in the selected isogeny kernel vanishes. -/
theorem _root_.solution (K2 : K2Rows) (x : J)
    (hπ : piEnd x = 0) (hfixed : ∀ τ : G5, r5 τ • x = x) : x = 0 := by
  have h := fixed_eq_zero_of_K2_rows vAct K2.i K2.q K2.i_injective K2.exact_at_V
    K2.i_galois K2.q_galois (⟨x,hπ⟩ : V) (fun τ => Subtype.ext (hfixed τ))
  exact congrArg Subtype.val h

end N25

-- Prove2me | solution 1 for GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:03.68573+00:00
-- url     : https://prove2.me/submissions/b65bdb83-7a14-427f-8b0e-217b20b87596

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CyclotomicIrreducibleOfNotDvdDiscr
import Theorems.Thm_ReciprocityTheory_Cheb_cyclotomic_irreducible_of_forall_isUnramifiedAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial NumberField
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by
  intro E _ _ l hl hd
  refine ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt hl fun P hP hlP => ?_
  exact (not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.1 hl)).1 hd P hP
    (by simpa using hlP)
end GlobalTheory

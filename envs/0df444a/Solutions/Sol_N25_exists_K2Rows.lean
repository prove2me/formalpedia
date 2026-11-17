-- Prove2me | solution 1 for N25.exists_K2Rows
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:13.136509+00:00
-- url     : https://prove2.me/submissions/e0a1eb1c-3096-4afb-8394-9074e4c48ab3

import Theorems.Thm_N25_kernel_natCard
import Definitions.Def_N25_LocalKummerPolynomial
import Theorems.Thm_N25_exists_cyclotomic_quotient_of_cusp
import Definitions.Def_N25_GlobalKummer
import Theorems.Thm_N25_exists_kernel_inclusion_of_character
import Theorems.Thm_N25_exists_K2Rows_of_card_and_maps
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false

namespace N25

/-- The rational cusp line and its Fricke character line give the frozen exact
sequence on the literal selected kernel. The cusp facts and cyclotomic relation
are the upstream geometric inputs. -/
theorem _root_.solution (hPhi : PhiFiveZero) (c a : J)
    (hcne : c ≠ 0) (hc71 : 71 • c = 0)
    (hcgamma : gamma c = 5 • c) (hcgal : ∀ σ : Gal, σ • c = c)
    (hane : a ≠ 0) (ha71 : 71 • a = 0)
    (hagamma : gamma a = 57 • a)
    (hagal : ∀ σ : Gal, σ • a = (psi σ : ZMod 71).val • a) : Nonempty K2Rows := by
  obtain ⟨i, hi, _, hiGal⟩ :=
    exists_kernel_inclusion_of_character hPhi a hane ha71 hagamma hagal
  obtain ⟨q, hq, hqGal⟩ :=
    exists_cyclotomic_quotient_of_cusp hPhi c hcne hc71 hcgamma hcgal
  exact exists_K2Rows_of_card_and_maps (kernel_natCard hPhi) i hi hiGal q hq hqGal

end N25

-- Prove2me | solution 1 for GlobalTheory.finite_height_eq_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:02.801323+00:00
-- url     : https://prove2.me/submissions/9c4fded6-1884-4c7f-a07d-36ec39b4bb3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_minimalPrimes_span_singleton_of_height_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
namespace GlobalTheory
theorem _root_.solution {a : A} (ha : a ≠ 0) :
    {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage
    (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hap⟩
  exact mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap
end GlobalTheory

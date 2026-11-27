-- Prove2me | solution 1 for GlobalTheory.iInf_primeLocalSubalgebra_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:11.718723+00:00
-- url     : https://prove2.me/submissions/19bfc8c7-05aa-451c-bbd7-5384fc07c454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_forall_height_eq_one

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
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable (A K)
namespace GlobalTheory
theorem _root_.solution :
    ⨅ p : {p : PrimeSpectrum A // p.asIdeal.height = 1}, primeLocalSubalgebra K p.1.asIdeal = ⊥ := by
  refine bot_unique fun x hx => Algebra.mem_bot.mpr ?_
  exact (mem_range_algebraMap_iff_forall_height_eq_one x).mpr fun p hp h1 =>
    Algebra.mem_iInf.mp hx ⟨⟨p, hp⟩, h1⟩
end GlobalTheory

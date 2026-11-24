-- Prove2me | solution 1 for GlobalTheory.height_eq_one_of_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:32.929295+00:00
-- url     : https://prove2.me/submissions/e2885ea7-b3cc-4fb5-aa39-440a1a188ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_height_eq_one_of_forall_mem_iff_dvd

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
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) : p.height = 1 := by
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine height_eq_one_of_forall_mem_iff_dvd (b := b) ha fun r => ?_
  rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
end GlobalTheory

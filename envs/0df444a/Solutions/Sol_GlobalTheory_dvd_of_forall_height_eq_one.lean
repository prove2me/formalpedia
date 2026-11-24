-- Prove2me | solution 1 for GlobalTheory.dvd_of_forall_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:10.992156+00:00
-- url     : https://prove2.me/submissions/13549391-fc71-465a-863c-d094312c9642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_height_eq_one

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
theorem _root_.solution {a b : A} (ha : a ≠ 0)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → ∃ s, s ∉ p ∧ a ∣ s * b) : a ∣ b := by
  by_contra hab
  have hb : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hb
  obtain ⟨_, h1, hap⟩ := (mem_associatedPrimes_iff_height_eq_one ha).mp hp
  obtain ⟨s, hs, hsb⟩ := h p h1 hap
  refine hs (hle ?_)
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
end GlobalTheory

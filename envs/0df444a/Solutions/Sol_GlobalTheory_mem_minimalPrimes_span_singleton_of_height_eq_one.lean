-- Prove2me | solution 1 for GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:33.02087+00:00
-- url     : https://prove2.me/submissions/d1a4f449-c4b8-435d-8455-58e5c2f9ef8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

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
theorem _root_.solution {p : Ideal A} [p.IsPrime]
    (hp : p.height = 1) {a : A} (ha : a ≠ 0) (hap : a ∈ p) :
    p ∈ (Ideal.span {a}).minimalPrimes := by
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem p).mpr hap⟩, ?_⟩
  rintro q ⟨hq, haq⟩ hqp
  by_contra hne
  have hlt : q < p := lt_of_le_not_ge hqp hne
  have h1 : q.height < p.height := Ideal.height_strict_mono_of_isPrime hlt
  rw [hp, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  rw [h1, Ideal.span_singleton_le_iff_mem] at haq
  exact ha haq
end GlobalTheory

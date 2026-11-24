-- Prove2me | solution 1 for GlobalTheory.length_quotient_span_singleton_eq_addVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:54.859739+00:00
-- url     : https://prove2.me/submissions/06bcaa0b-adc8-4888-9988-7105b347d73c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addVal_zero, Ideal.span_singleton_zero,
      (Submodule.quotEquivOfEqBot (⊥ : Ideal S) rfl).length_eq]
    by_contra h
    have h' := Module.length_ne_top_iff.mp h
    rw [← isArtinianRing_iff_isFiniteLength] at h'
    exact not_isField S (IsArtinianRing.isField_of_isDomain S)
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal]
end GlobalTheory

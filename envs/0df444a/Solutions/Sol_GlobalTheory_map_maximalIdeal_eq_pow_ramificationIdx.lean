-- Prove2me | solution 1 for GlobalTheory.map_maximalIdeal_eq_pow_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:04.190875+00:00
-- url     : https://prove2.me/submissions/dcbad69b-4223-4f57-a3c7-1c33f67192a4

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
variable [IsLocalHom (algebraMap R S)]
namespace GlobalTheory
theorem _root_.solution :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpS : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hpS hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S) hp,
    Ideal.ramificationIdx'_spec (n := n) hn.le, hn]
  rw [hn]
  exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) n).not_ge
end GlobalTheory

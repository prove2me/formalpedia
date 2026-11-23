-- Prove2me | solution 1 for GlobalTheory.ramificationIdx_maximalIdeal_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:26.892874+00:00
-- url     : https://prove2.me/submissions/d077de64-62de-4d90-9d97-45bb4504283c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_map_maximalIdeal_eq_pow_ramificationIdx

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
theorem _root_.solution : 0 < (maximalIdeal S).ramificationIdx R := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := map_maximalIdeal_eq_pow_ramificationIdx R S
  rw [h, pow_zero, Ideal.one_eq_top] at this
  exact (map_maximalIdeal_lt_top (algebraMap R S)).ne this
end GlobalTheory

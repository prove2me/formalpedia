-- Prove2me | solution 1 for GlobalTheory.length_fibre_eq_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:25.580802+00:00
-- url     : https://prove2.me/submissions/85a5a8b7-ecc3-4aea-bfad-dcb1d4be86cb

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
theorem _root_.solution :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by
  conv_lhs => rw [map_maximalIdeal_eq_pow_ramificationIdx]
  exact length_quotient_pow_maximalIdeal S _
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.length_baseChange_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:07.541163+00:00
-- url     : https://prove2.me/submissions/81e948c6-919c-4277-8cad-49345cc1bd09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_length_baseChange_flat
import Theorems.Thm_GlobalTheory_length_fibre_eq_ramificationIdx

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
variable (X : Type*) [AddCommGroup X] [Module R X]
namespace GlobalTheory
theorem _root_.solution :
    Module.length S (S ⊗[R] X) =
      Module.length R X * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_flat, length_fibre_eq_ramificationIdx]
end GlobalTheory

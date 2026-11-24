-- Prove2me | solution 1 for GlobalTheory.length_baseChange_subquotient_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:56.088279+00:00
-- url     : https://prove2.me/submissions/cf27806f-e718-4e5b-8b37-7a5adb7ea6d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_length_baseChange_subquotient_flat
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
variable {X}
namespace GlobalTheory
theorem _root_.solution (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_subquotient_flat, length_fibre_eq_ramificationIdx]
end GlobalTheory

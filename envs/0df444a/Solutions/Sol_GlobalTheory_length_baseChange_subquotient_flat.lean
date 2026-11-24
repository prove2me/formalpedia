-- Prove2me | solution 1 for GlobalTheory.length_baseChange_subquotient_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:34.375343+00:00
-- url     : https://prove2.me/submissions/94ca54c8-276d-4a99-ba5c-ed8b9e8f78b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_nonempty_baseChange_subquotient_equiv
import Theorems.Thm_GlobalTheory_length_baseChange_flat

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
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]
variable {X}
namespace GlobalTheory
theorem _root_.solution (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) *
        Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  rw [← length_baseChange_flat]
  exact (nonempty_baseChange_subquotient_equiv R S A B).some.length_eq.symm
end GlobalTheory

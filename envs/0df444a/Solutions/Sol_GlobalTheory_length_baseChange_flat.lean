-- Prove2me | solution 1 for GlobalTheory.length_baseChange_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:39.458859+00:00
-- url     : https://prove2.me/submissions/e4f16d2b-e1ba-4577-abff-3b8c465ec719

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
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]
namespace GlobalTheory
theorem _root_.solution :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  IsLocalRing.length_baseChange R S X
end GlobalTheory

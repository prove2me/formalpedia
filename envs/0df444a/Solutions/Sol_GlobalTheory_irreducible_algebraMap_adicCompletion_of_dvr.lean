-- Prove2me | solution 1 for GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:25.17053+00:00
-- url     : https://prove2.me/submissions/8f32e352-e9fe-4471-8be0-bc86e2598f8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {V}
namespace GlobalTheory
theorem _root_.solution {π : V} (hπ : Irreducible π) :
    Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) :=
  (adicCompletion_isDVR_irreducible V hπ).2.2
end GlobalTheory

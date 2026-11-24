-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.expIn_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:21.212449+00:00
-- url     : https://prove2.me/submissions/2ad52381-4eb0-4b29-8dd6-d40ed70b6692

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (v : HeightOneSpectrum (OF E)) (n : ℕ) : expIn (v.asIdeal ^ n) v = n :=
  multiplicity_pow_self v.ne_bot (fun h => v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) n
end GlobalTheory.CMVal.Model

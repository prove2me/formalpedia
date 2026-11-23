-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.expIn_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:30.712798+00:00
-- url     : https://prove2.me/submissions/0f148a69-2873-4458-ba61-93e3b4abb913

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor

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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution (v : HeightOneSpectrum (OF E)) (n : ℕ) : expIn (v.asIdeal ^ n) v = n :=
  multiplicity_pow_self v.ne_bot (fun h => v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) n
end GlobalTheory.CMVal.InhabK

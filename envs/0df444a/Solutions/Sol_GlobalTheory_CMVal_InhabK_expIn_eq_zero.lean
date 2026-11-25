-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.expIn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:33.764349+00:00
-- url     : https://prove2.me/submissions/c140ebcd-08f9-4ea8-94f6-3699ac41fe7c

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
theorem _root_.solution {𝔣 : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} : expIn 𝔣 v = 0 ↔ ¬ v.asIdeal ∣ 𝔣 :=
  multiplicity_eq_zero
end GlobalTheory.CMVal.InhabK

-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.not_unitAt_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:11.155018+00:00
-- url     : https://prove2.me/submissions/08666c4b-dcd0-41df-bc5d-eb7758467c27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_not_intAt_inv

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
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {l : ℕ} (hl : l.Prime) : ¬ UnitAt l (l : ℂ) := fun h => not_intAt_inv hl h.2.2
end GlobalTheory.CMVal.Model

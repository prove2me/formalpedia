-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.not_isCMType_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:38.734803+00:00
-- url     : https://prove2.me/submissions/add1321f-0be1-465a-8dea-0026a5d14b79

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
theorem _root_.solution (φ : Empty → E →+* ℂ) : ¬ IsCMType φ := fun h => by
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨i, -⟩ := h σ
  exact i.elim
end GlobalTheory.CMVal.Model

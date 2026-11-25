-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.LevelLe.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:04.411285+00:00
-- url     : https://prove2.me/submissions/e1a96f12-179d-40bc-baed-c882491e4d8b

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
namespace LevelLe
theorem _root_.solution {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (h : LevelLe χ P m) (hmn : m ≤ n) :
    LevelLe χ P n := fun y h1 h3 =>
  h y h1 (h3.trans (WithZero.exp_le_exp.2 (by omega)))
end LevelLe
end GlobalTheory.CMVal.Model

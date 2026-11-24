-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.levelLe_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:22.187959+00:00
-- url     : https://prove2.me/submissions/1d82eded-39b6-4725-a5f2-74db7036b008

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
theorem _root_.solution {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} : LevelLe χ⁻¹ P n ↔ LevelLe χ P n := by
  refine forall_congr' fun y => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  change (χ.loc P y)⁻¹ = 1 ↔ _
  exact inv_eq_one
end GlobalTheory.CMVal.Model

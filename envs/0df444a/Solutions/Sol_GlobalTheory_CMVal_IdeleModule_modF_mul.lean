-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleModule.modF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:35:57.675957+00:00
-- url     : https://prove2.me/submissions/f18355c5-544e-4ace-9abb-ef05261ff480

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_finite
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_absNorm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleModule
theorem _root_.solution (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']
end GlobalTheory.CMVal.IdeleModule

-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleModule.modF_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:00.995183+00:00
-- url     : https://prove2.me/submissions/5ddac2f1-95a3-4367-bfe6-9b3724d5e1de

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
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
theorem _root_.solution (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _
end GlobalTheory.CMVal.IdeleModule

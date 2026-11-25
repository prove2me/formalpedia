-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.lInf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:34.946641+00:00
-- url     : https://prove2.me/submissions/a1ad7ee4-9817-4d71-a936-9cd06f6fe185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) :
    LInf m s = ∏ i, Complex.Gammaℂ (s + (|m i| : ℤ)) := by
  simp only [LInf, Complex.Gammaℂ_def]
end GlobalTheory.CMVal.Model

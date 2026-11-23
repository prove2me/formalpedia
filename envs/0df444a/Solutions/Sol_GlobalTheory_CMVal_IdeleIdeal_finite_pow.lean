-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleIdeal.finite_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:31.198805+00:00
-- url     : https://prove2.me/submissions/6695a76e-816e-45e9-a9b5-ab48d00b9705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_ordAt_eventually
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
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleIdeal
theorem _root_.solution (y : (Af E)ˣ) :
    (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal ^ ordAt y w).Finite := by
  have := ordAt_eventually y
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]
end GlobalTheory.CMVal.IdeleIdeal

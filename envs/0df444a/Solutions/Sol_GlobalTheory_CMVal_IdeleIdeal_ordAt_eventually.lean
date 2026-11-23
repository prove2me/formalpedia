-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleIdeal.ordAt_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:01.886544+00:00
-- url     : https://prove2.me/submissions/b1494ade-4a04-481f-80f5-845a3a28e2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
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
theorem _root_.solution (y : (Af E)ˣ) : ∀ᶠ w in Filter.cofinite, ordAt y w = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 y.isUnit).2] with w hw
  simp [ordAt, hw]
end GlobalTheory.CMVal.IdeleIdeal

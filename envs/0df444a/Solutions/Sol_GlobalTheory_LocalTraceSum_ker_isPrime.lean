-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.ker_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:35.338139+00:00
-- url     : https://prove2.me/submissions/36913c02-32fe-40ad-8de4-495721fc4013

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_mem_ker
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution (σ : F →+* Ω) : (ker σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ker]; simp
  · intro a b hab
    rw [mem_ker] at hab
    by_contra h
    rw [not_or, mem_ker, mem_ker, not_lt, not_lt] at h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab
    nlinarith [h.1, h.2]
end GlobalTheory.LocalTraceSum

-- Prove2me | solution 1 for GlobalTheory.EigenPair.natMul_mem_orderC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:56.639023+00:00
-- url     : https://prove2.me/submissions/276c44c8-6213-462a-bc78-83e08fdb5024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.EigenPair
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.EigenPair
theorem _root_.solution (c : Ideal (OF E)) (z : 𝓞 E) :
    ((Ideal.absNorm c : ℕ) : E) * (z : E) ∈ orderC c := by
  refine mem_orderC.2 ⟨0, ((Ideal.absNorm c : ℕ) : 𝓞 E) * z, ?_, ?_⟩
  · refine Ideal.mul_mem_right z _ ?_
    have h := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) (Ideal.absNorm_mem c)
    simpa using h
  · simp
end GlobalTheory.EigenPair

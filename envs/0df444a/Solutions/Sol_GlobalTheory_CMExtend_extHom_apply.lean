-- Prove2me | solution 1 for GlobalTheory.CMExtend.extHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:55.795529+00:00
-- url     : https://prove2.me/submissions/bdae40ab-913a-4c45-87cd-9c53c6e40020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
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
noncomputable section
open GlobalTheory GlobalTheory.CMExtend
variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]
namespace GlobalTheory.CMExtend
theorem _root_.solution (hc : c ≠ ⊥) (g : orderC c →+* A) (a : orderC c) : extHom K hc g a = g a := by
  show extFun K hc g a = g a
  rw [extFun_eq hc g one_ne_zero (by simpa using a.2)]
  simp only [Nat.cast_one, inv_one, one_smul]
  congr 1
  apply Subtype.ext; simp
end GlobalTheory.CMExtend

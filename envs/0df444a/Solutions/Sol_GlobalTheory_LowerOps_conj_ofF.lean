-- Prove2me | solution 1 for GlobalTheory.LowerOps.conj_ofF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:27.732721+00:00
-- url     : https://prove2.me/submissions/24edf80b-84a0-476c-bd66-a2be5600cb0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.LowerOps
theorem _root_.solution (a : OF E) :
    IsCMField.complexConj E ((ofF c a : orderC c) : E) = ((ofF c a : orderC c) : E) := by
  show IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a
  rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
  exact IsCMField.complexConj_apply_eq_self E _
end GlobalTheory.LowerOps

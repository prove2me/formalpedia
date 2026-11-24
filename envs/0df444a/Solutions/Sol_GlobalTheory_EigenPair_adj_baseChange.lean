-- Prove2me | solution 1 for GlobalTheory.EigenPair.adj_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:55.813866+00:00
-- url     : https://prove2.me/submissions/e62de707-e755-4043-83e2-aed8d6fb233d

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
theorem _root_.solution {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H]
    [Module O H] (B : LinearMap.BilinForm O H) (f g : Module.End O H) (hfg : ∀ h h', B (f h) h' = B h (g h'))
    (x y : K ⊗[O] H) : B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s h =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t h' => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hfg]
end GlobalTheory.EigenPair

-- Prove2me | solution 1 for GlobalTheory.KSp.good_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:05.572266+00:00
-- url     : https://prove2.me/submissions/044d78c3-6b2b-4d5a-9ef3-211e9dddd19d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_good_of_addEquiv
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_good_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  intro F _ _ _ _ _ V _ _ _ _ _
  haveI := IsModuleTopology.topologicalAddGroup F V
  let b := Module.finBasis F V
  let e := b.equivFun
  exact GlobalTheory.KSp.GoodSpace.good_of_addEquiv e.toAddEquiv
    (IsModuleTopology.continuous_of_linearMap (R := F) e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap (R := F) e.symm.toLinearMap)
    (GlobalTheory.KSp.GoodSpace.good_pi _)
end GlobalTheory.KSp

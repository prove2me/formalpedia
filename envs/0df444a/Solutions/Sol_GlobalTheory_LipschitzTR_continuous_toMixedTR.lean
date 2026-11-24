-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.continuous_toMixedTR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:47:04.479771+00:00
-- url     : https://prove2.me/submissions/691931ca-2313-48f2-b0df-8f80d4ddd8b6

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    Continuous (toMixedTR F) := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (PiLp.continuous_apply 2 _ _)
end GlobalTheory.LipschitzTR

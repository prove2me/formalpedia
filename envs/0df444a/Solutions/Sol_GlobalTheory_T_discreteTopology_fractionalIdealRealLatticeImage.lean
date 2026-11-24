-- Prove2me | solution 1 for GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:46.516874+00:00
-- url     : https://prove2.me/submissions/62814bf6-5b9b-4a00-8f54-6c5a296acbbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImageStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_discrete_latOf


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.discrete_latOf | exact GlobalTheory.LipschitzTR.discrete_latOf | (intros; apply GlobalTheory.LipschitzTR.discrete_latOf <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.EuclidTransport.l2Transport_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:42.064803+00:00
-- url     : https://prove2.me/submissions/e36c118a-7ed6-4cbc-ba58-81fdf24a3178

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzL2EuclideanIdentification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.EuclidTransport
variable (l : Type) [Fintype l]
variable {l}
variable (l)
variable {l}
namespace GlobalTheory.EuclidTransport
theorem _root_.solution (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2Transport l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl
end GlobalTheory.EuclidTransport

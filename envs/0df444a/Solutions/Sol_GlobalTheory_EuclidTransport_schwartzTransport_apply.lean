-- Prove2me | solution 1 for GlobalTheory.EuclidTransport.schwartzTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:34.080929+00:00
-- url     : https://prove2.me/submissions/7f8475a6-24d0-4886-aea8-a2a6b14fa69b

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
namespace GlobalTheory.EuclidTransport
theorem _root_.solution (φ : 𝓢(l → ℝ, ℂ)) (x : EuclideanSpace ℝ l) :
    schwartzTransport l φ x = φ x.ofLp := rfl
end GlobalTheory.EuclidTransport

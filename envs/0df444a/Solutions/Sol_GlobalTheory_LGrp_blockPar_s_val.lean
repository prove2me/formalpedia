-- Prove2me | solution 1 for GlobalTheory.LGrp.blockPar_s_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:22.295876+00:00
-- url     : https://prove2.me/submissions/84f0a938-adcb-4a2d-b63e-2a044178a66c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {k n α : Type} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]
variable [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
variable {a d : Type} [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d]
namespace GlobalTheory.LGrp
theorem _root_.solution (m : GL a k × GL d k) : ((blockPar k a d).s m).val = fromBlocks m.1.val 0 0 m.2.val := rfl
end GlobalTheory.LGrp

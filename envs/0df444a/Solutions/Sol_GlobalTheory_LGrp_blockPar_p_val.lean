-- Prove2me | solution 1 for GlobalTheory.LGrp.blockPar_p_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:15.046+00:00
-- url     : https://prove2.me/submissions/d4a1c7b9-c061-44b7-bff1-2a3350c5dd6a

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
theorem _root_.solution (q : (blockPar k a d).Q) :
    ((blockPar k a d).p q).1.val = q.1.val.toBlocks₁₁ ∧ ((blockPar k a d).p q).2.val = q.1.val.toBlocks₂₂ := ⟨rfl, rfl⟩
end GlobalTheory.LGrp

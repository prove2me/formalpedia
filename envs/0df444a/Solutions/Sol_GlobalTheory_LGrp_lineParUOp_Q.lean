-- Prove2me | solution 1 for GlobalTheory.LGrp.lineParUOp_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:02:16.391606+00:00
-- url     : https://prove2.me/submissions/c54ac4bd-65da-43cc-92bf-355ab362b81f

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
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
namespace GlobalTheory.LGrp
theorem _root_.solution : (lineParUOp σ hσ hc n).Q = (parUOp σ (selfDualBlocks_line (n + 2))).Q := rfl
end GlobalTheory.LGrp

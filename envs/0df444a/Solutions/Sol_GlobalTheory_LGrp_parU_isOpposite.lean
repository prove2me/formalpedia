-- Prove2me | solution 1 for GlobalTheory.LGrp.parU_isOpposite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:35:09.961952+00:00
-- url     : https://prove2.me/submissions/2bcd1330-87e9-4989-84f5-10b5bd813a63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_blockQ_inf_dual

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {α : Type} [LinearOrder α]
namespace GlobalTheory.LGrp
theorem _root_.solution (σ : L →+* L) {n : ℕ} {b : Fin n → α} (hb : SelfDualBlocks b) :
    (parU σ hb).IsOpposite (parUOp σ hb) := by
  refine ⟨rfl, le_antisymm ?_ ?_⟩
  · exact fun g hg => ⟨⟨g.1, g.2, (blockQ_inf_dual b).le hg⟩, rfl⟩
  · rintro _ ⟨m, rfl⟩
    exact ⟨(parU σ hb).s_mem m, (parUOp σ hb).s_mem m⟩
end GlobalTheory.LGrp

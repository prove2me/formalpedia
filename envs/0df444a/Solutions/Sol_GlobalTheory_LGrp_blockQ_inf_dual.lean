-- Prove2me | solution 1 for GlobalTheory.LGrp.blockQ_inf_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:12.652911+00:00
-- url     : https://prove2.me/submissions/b3b02cb1-6220-4094-bc91-2118fbf9c133

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
namespace GlobalTheory.LGrp
theorem _root_.solution (b : n → α) : blockQ k b ⊓ blockQ k (α := αᵒᵈ) b = blockL k b := by
  refine le_antisymm (fun g hg i j h => ?_) (le_inf (blockL_le b) (blockL_le (α := αᵒᵈ) b))
  rcases lt_or_gt_of_ne h with h | h
  · exact hg.2 h
  · exact hg.1 h
end GlobalTheory.LGrp

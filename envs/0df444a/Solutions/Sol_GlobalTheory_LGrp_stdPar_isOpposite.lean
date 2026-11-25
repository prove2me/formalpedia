-- Prove2me | solution 1 for GlobalTheory.LGrp.stdPar_isOpposite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:48.441966+00:00
-- url     : https://prove2.me/submissions/3d52d2e7-ab6d-4c7c-8a3c-369de745b424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_blockQ_inf_dual
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution (b : n → α) : (stdPar k b).IsOpposite (stdParOp k b) :=
  ⟨rfl, (blockQ_inf_dual b).trans (Subgroup.range_subtype _).symm⟩
end GlobalTheory.LGrp

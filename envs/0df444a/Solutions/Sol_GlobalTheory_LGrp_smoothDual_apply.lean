-- Prove2me | solution 1 for GlobalTheory.LGrp.smoothDual_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:44.912195+00:00
-- url     : https://prove2.me/submissions/2d411c69-7176-4b75-9a42-13b962e0f411

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
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [IsTopologicalGroup G]
namespace GlobalTheory.LGrp
theorem _root_.solution (ρ : Representation ℂ G V) (g : G) (l : smoothPart ρ.dual) (v : V) :
    (smoothDual ρ g l).1 v = l.1 (ρ g⁻¹ v) := rfl
end GlobalTheory.LGrp

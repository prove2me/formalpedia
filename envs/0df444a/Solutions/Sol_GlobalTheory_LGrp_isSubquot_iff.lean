-- Prove2me | solution 1 for GlobalTheory.LGrp.isSubquot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:54.140396+00:00
-- url     : https://prove2.me/submissions/bcbf9999-9b5d-40fe-be90-2a1ec5baf43f

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
open ValuativeRel
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (π : Representation ℂ G W) (ρ : Representation ℂ G V) :
    IsSubquot π ρ ↔ SmGL.IsSubquotient π ρ := Iff.rfl
end GlobalTheory.LGrp

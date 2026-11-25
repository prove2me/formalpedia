-- Prove2me | solution 1 for GlobalTheory.LGrp.coinvCharMid_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:12.273483+00:00
-- url     : https://prove2.me/submissions/1ebb9f18-9b8c-4398-b90c-55f00ff3987e

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
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (χ : A →* ℂˣ) (ρ : Representation ℂ (G × (A × H)) V) (g : G × H) (v : V) :
    coinvCharMid χ ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (g.1, 1, g.2) v) := rfl
end GlobalTheory.LGrp

-- Prove2me | solution 1 for GlobalTheory.LGrp.parDatum_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:43.371119+00:00
-- url     : https://prove2.me/submissions/a01b694e-3341-47c4-9cd3-a5305434def1

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
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.LGrp
theorem _root_.solution (e : (Σ a, m a) ≃ n) : (parDatum k e).U = SmGL.unipRad k e := rfl
end GlobalTheory.LGrp

-- Prove2me | solution 1 for GlobalTheory.LGrp.LeviDatum.nInd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:59.683501+00:00
-- url     : https://prove2.me/submissions/6e63a368-3757-498b-a19a-ab5d5eae15ec

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
open GlobalTheory.LGrp.LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp.LeviDatum
theorem _root_.solution (σ : Representation ℂ M W) (g x : G) (f : P.IndSpace σ) :
    (P.nInd σ g f).1.1 x = f.1.1 (x * g) := rfl
end GlobalTheory.LGrp.LeviDatum

-- Prove2me | solution 1 for GlobalTheory.LGrp.lineParUOp_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:26.590076+00:00
-- url     : https://prove2.me/submissions/bf27027f-bec5-4258-a08e-b9be06a88cb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
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
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
namespace GlobalTheory.LGrp
theorem _root_.solution (q : (lineParUOp σ hσ hc n).Q) :
    (((lineParUOp σ hσ hc n).p q).1 : L) = q.1.1.val 0 0 ∧
      ∀ i j, ((lineParUOp σ hσ hc n).p q).2.1.val i j = q.1.1.val (midIdx i) (midIdx j) :=
  ⟨rfl, fun i j => if_pos ((lineBlocks_mid i).trans (lineBlocks_mid j).symm)⟩
end GlobalTheory.LGrp

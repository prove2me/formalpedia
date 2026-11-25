-- Prove2me | solution 1 for GlobalTheory.LGrp.borelU_le_lineParU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:27.413857+00:00
-- url     : https://prove2.me/submissions/72a49a6c-3c1f-4800-8681-2b1fe7f5f6b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_borelU_Q
import Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_Q

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
theorem _root_.solution : (borelU σ (n + 2)).Q ≤ (lineParU σ hσ hc n).Q := fun g hg =>
  (mem_lineParU_Q σ hσ hc g).2 fun i hi => (mem_borelU_Q σ _ g).1 hg i 0 (Fin.pos_of_ne_zero hi)
end GlobalTheory.LGrp

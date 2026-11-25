-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_lineParU_Q_iff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:05.190143+00:00
-- url     : https://prove2.me/submissions/43a408b7-e434-4d6d-81e0-1280e0ebf029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_Q
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



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
theorem _root_.solution (g : GU σ (n + 2)) :
    g ∈ (lineParU σ hσ hc n).Q ↔ ∃ a : L, g.1.val *ᵥ Pi.single 0 1 = a • Pi.single 0 1 := by
  rw [mem_lineParU_Q]
  constructor
  · refine fun h => ⟨g.1.val 0 0, funext fun l => ?_⟩
    by_cases hl : l = 0
    · simp [hl]
    · simp [hl, h l hl]
  · rintro ⟨a, h⟩ i hi
    simpa [hi] using congrFun h i
end GlobalTheory.LGrp

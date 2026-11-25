-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_lineParUOp_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:06:22.334001+00:00
-- url     : https://prove2.me/submissions/912f0ba1-0260-4b90-8e77-f6f5a6a1a815

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_row_eq_zero_of_col
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
    g ∈ (lineParUOp σ hσ hc n).Q ↔ ∀ i, i ≠ Fin.last (n + 1) → g.1.val i (Fin.last (n + 1)) = 0 := by
  show (∀ ⦃i j⦄, lineBlocks (n + 2) i < lineBlocks (n + 2) j → g.1.val i j = 0) ↔ _
  constructor
  · intro h i hi
    induction i using lineCases <;> first | exact absurd rfl hi | (refine h ?_; simp; done)
  · intro h i j e
    have h' := row_eq_zero_of_col σ g _ h
    rw [Fin.rev_last] at h'
    induction i using lineCases <;> induction j using lineCases <;>
      first | (exfalso; simp at e; done) | (refine h _ ?_; simp; done) | exact h _ (Fin.last_pos).ne | (refine h' _ ?_; simp; done)
end GlobalTheory.LGrp

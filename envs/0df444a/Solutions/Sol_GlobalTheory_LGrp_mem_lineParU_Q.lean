-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_lineParU_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:57.158806+00:00
-- url     : https://prove2.me/submissions/ada94917-292a-4661-9d16-8a934c23d5b9

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
theorem _root_.solution (g : GU σ (n + 2)) : g ∈ (lineParU σ hσ hc n).Q ↔ ∀ i, i ≠ 0 → g.1.val i 0 = 0 := by
  show g.1.val.BlockTriangular (lineBlocks (n + 2)) ↔ _
  constructor
  · intro h i hi
    induction i using lineCases <;> first | exact absurd rfl hi | (refine h ?_; simp; done)
  · intro h i j e
    have h' := row_eq_zero_of_col σ g 0 h
    rw [Fin.rev_zero] at h'
    induction i using lineCases <;> induction j using lineCases <;>
      first | (exfalso; simp at e; done) | (refine h _ ?_; simp; done) | (refine h' _ ?_; simp; done)
end GlobalTheory.LGrp

-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_borelLineLevi_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:06.416727+00:00
-- url     : https://prove2.me/submissions/63a587fb-c2bd-49e2-b8af-189130de1783

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_borelU_Q
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
theorem _root_.solution (x : Lˣ × GU σ n) :
    x ∈ (borelLineLevi σ n).Q ↔ lineSec σ hσ n x ∈ (borelU σ (n + 2)).Q := by
  show x.2 ∈ (borelU σ n).Q ↔ _
  rw [mem_borelU_Q, mem_borelU_Q]
  simp only [IsBorelU, lineSec_val]
  constructor
  · intro h i j e
    induction i using lineCases <;> induction j using lineCases <;>
      first | exact absurd e (lt_irrefl _) | (rw [lineMat_mid_mid]; exact h _ _ (Nat.lt_of_succ_lt_succ e)) | simp
  · intro h i j e
    simpa using h (midIdx i) (midIdx j) (Nat.succ_lt_succ e)
end GlobalTheory.LGrp

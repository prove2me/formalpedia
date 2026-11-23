-- Prove2me | solution 1 for GlobalTheory.LGrp.row_eq_zero_of_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.363611+00:00
-- url     : https://prove2.me/submissions/1019d2f2-7825-460f-ab2f-4fd3fe2b979b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
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
omit hσ hc [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.LGrp
theorem _root_.solution (g : GU σ n) (c : Fin n) (h : ∀ i, i ≠ c → g.1.val i c = 0) (j : Fin n) (hj : j ≠ c.rev) :
    g.1.val c.rev j = 0 := by
  have h1 : g.1.val *ᵥ Pi.single c 1 = g.1.val c c • Pi.single c 1 := by
    ext l
    by_cases hl : l = c
    · simp [hl]
    · simp [hl, h l hl]
  have h2 : (Pi.single c 1 : Fin n → L) = g.1.val c c • ((g.1⁻¹).val *ᵥ Pi.single c 1) := by
    rw [← mulVec_smul, ← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
  have h0 : g.1.val c c ≠ 0 := fun e => by simpa [e] using congrFun h2 c
  have hjr : j.rev ≠ c := fun e => hj (by rw [← e, Fin.rev_rev])
  have h3 : (g.1⁻¹).val j.rev c = 0 := by simpa [hjr, h0] using congrFun h2 j.rev
  rw [(mem_GU_iff σ _ g.1).1 g.2, Fin.rev_rev] at h3
  exact (map_eq_zero σ).1 h3
end GlobalTheory.LGrp

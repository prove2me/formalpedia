-- Prove2me | solution 1 for GlobalTheory.LGrp.unrChar_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:59.086458+00:00
-- url     : https://prove2.me/submissions/7763552c-2f15-4a82-82d1-d277b24bfdf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_unrChar_apply
import Theorems.Thm_GlobalTheory_LGrp_vZ_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_unrChar_apply
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
open ValuativeRel
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.LGrp
theorem _root_.solution (z : ℂˣ) (ϖ : kˣ) (h1 : valuation k (ϖ : k) < 1)
    (hmax : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (ϖ : k)) : unrChar (vZ k) z ϖ = z := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hne : e (valuation k (ϖ : k)) ≠ 0 := by simp
  have hlt : e (valuation k (ϖ : k)) < 1 := by
    rw [← map_one e]; exact e.strictMono h1
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx' : e (valuation k x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  have hx1 : valuation k x < 1 := by
    rw [← e.strictMono.lt_iff_lt, hx', map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hle : WithZero.exp (-1 : ℤ) ≤ e (valuation k (ϖ : k)) := by
    rw [← hx']; exact e.strictMono.monotone (hmax x hx1)
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hle
  have : WithZero.log (e (valuation k (ϖ : k))) = -1 := by omega
  rw [unrChar_apply, vZ_apply, this]; simp
end GlobalTheory.LGrp

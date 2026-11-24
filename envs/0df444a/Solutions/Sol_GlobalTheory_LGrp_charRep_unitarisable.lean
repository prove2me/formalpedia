-- Prove2me | solution 1 for GlobalTheory.LGrp.charRep_unitarisable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:35:06.556762+00:00
-- url     : https://prove2.me/submissions/0e1326b2-aede-417c-994c-7ad373d42640

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
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (χ : G →* ℂˣ) (h : ∀ g, ‖(χ g : ℂ)‖ = 1) : IsUnitarisable (charRep χ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp [mul_assoc]) (fun _ _ _ => by simp [mul_add])
    (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
  · intro v w; simp [mul_comm]
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hv
  · intro g v w
    have : (χ g : ℂ) * starRingEnd ℂ (χ g : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h g]; simp
    simp only [LinearMap.mk₂'ₛₗ_apply, charRep_apply, map_mul]
    linear_combination (v * starRingEnd ℂ w) * this
end GlobalTheory.LGrp

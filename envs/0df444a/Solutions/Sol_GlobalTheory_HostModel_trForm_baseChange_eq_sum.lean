-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_baseChange_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:16.080313+00:00
-- url     : https://prove2.me/submissions/17526ffe-92f6-430b-aabf-c4e9dde7a107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    ((trForm H).baseChange ℝ v w : ℂ) = ∑ τ : E →+* ℂ, conj (realEmb τ v) * realEmb τ w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' h h' => simp [h, h', add_mul, Finset.sum_add_distrib]
  | tmul r x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' h h' => rw [map_add, Complex.ofReal_add, h, h']; simp [mul_add, Finset.sum_add_distrib]
    | tmul s y =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
      push_cast
      rw [trForm_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [realEmb_tmul, map_mul, Complex.conj_ofReal]
      ring
end GlobalTheory.HostModel

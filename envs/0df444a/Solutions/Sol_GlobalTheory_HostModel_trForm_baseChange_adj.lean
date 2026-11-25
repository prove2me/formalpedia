-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_baseChange_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:21.761+00:00
-- url     : https://prove2.me/submissions/c04182d9-9468-43a8-91d2-004a08aa16c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_eq_sum
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
theorem _root_.solution (H : Host E) (a : 𝓞 E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ ((1 ⊗ₜ a) * v) w = (trForm H).baseChange ℝ v ((1 ⊗ₜ H.bar a) * w) := by
  apply Complex.ofReal_injective
  rw [trForm_baseChange_eq_sum, trForm_baseChange_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_mul, realEmb_tmul, embedding_bar, Complex.ofReal_one, one_mul]
  ring
end GlobalTheory.HostModel

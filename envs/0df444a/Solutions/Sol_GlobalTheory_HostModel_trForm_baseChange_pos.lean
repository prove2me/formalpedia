-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_baseChange_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:16.345797+00:00
-- url     : https://prove2.me/submissions/c624402f-a117-4bb9-8141-7c45f76e62b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_eq_sum
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_self_eq_sum
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_nondegenerate
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
theorem _root_.solution (H : Host E) {v : ℝ ⊗[ℤ] 𝓞 E} (hv : v ≠ 0) :
    0 < (trForm H).baseChange ℝ v v := by
  rw [trForm_baseChange_self_eq_sum]
  refine (Finset.sum_nonneg fun τ _ => sq_nonneg _).lt_of_ne fun h => hv ?_
  have h0 : ∀ τ : E →+* ℂ, realEmb τ v = 0 := fun τ => by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => sq_nonneg _).1 h.symm τ (Finset.mem_univ τ)
  refine (trForm_baseChange_nondegenerate H).1 v fun w => Complex.ofReal_injective ?_
  rw [trForm_baseChange_eq_sum]
  simp [h0]
end GlobalTheory.HostModel

-- Prove2me | solution 1 for GlobalTheory.HostModel.hypJ_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:46:44.665627+00:00
-- url     : https://prove2.me/submissions/c8d367b4-6624-44f0-81fe-a823919c7368

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_trForm_symm
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ConjDual
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) (x : 𝓞 E) :
    hypJ H (1 ⊗ₜ (x, 0)) = 1 ⊗ₜ (0, traceDual H x) := by
  apply (hypRealBasis H).repr.injective
  have h := LinearMap.toMatrix_mulVec_repr (hypRealBasis H) (hypRealBasis H) (hypJ H) (1 ⊗ₜ (x, 0))
  apply DFunLike.coe_injective
  rw [← h, toMatrix_hypJ]
  have hx : ∀ y, trForm H x y =
      ∑ j, trForm H y (RingOfIntegers.basis E j) * (RingOfIntegers.basis E).repr x j := by
    intro y
    rw [trForm_symm]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
    simp only [map_sum, map_zsmul]
    simp [mul_comm]
  ext (i | i) <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hypRealBasis, hypBasis_repr_inl, hypBasis_repr_inr, gram, hx]
end GlobalTheory.HostModel

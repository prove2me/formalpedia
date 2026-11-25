-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_baseChange_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:30.014919+00:00
-- url     : https://prove2.me/submissions/d9f91ab0-2eb1-44ad-9cd3-b5c94b6e7c5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ v w = (trForm H).baseChange ℝ w v := by
  apply Complex.ofReal_injective
  rw [← Complex.conj_ofReal ((trForm H).baseChange ℝ w v), trForm_baseChange_eq_sum, trForm_baseChange_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun τ _ => by rw [map_mul, Complex.conj_conj, mul_comm]
end GlobalTheory.HostModel

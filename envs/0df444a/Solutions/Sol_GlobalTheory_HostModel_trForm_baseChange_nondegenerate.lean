-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_baseChange_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:19.906793+00:00
-- url     : https://prove2.me/submissions/cce149d8-89ef-4347-8365-d298c1e80361

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_trForm_nondegenerate
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
theorem _root_.solution (H : Host E) : ((trForm H).baseChange ℝ).Nondegenerate := by
  classical
  let b := RingOfIntegers.basis E
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 (trForm_nondegenerate H)
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℝ)]
  have e : LinearMap.BilinForm.toMatrix (b.baseChange ℝ) ((trForm H).baseChange ℝ) =
      (Int.castRingHom ℝ).mapMatrix (LinearMap.BilinForm.toMatrix b (trForm H)) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [e, ← RingHom.map_det]
  simpa using h
end GlobalTheory.HostModel

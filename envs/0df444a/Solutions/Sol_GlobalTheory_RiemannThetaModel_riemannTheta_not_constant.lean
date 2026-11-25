-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.riemannTheta_not_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:14.152089+00:00
-- url     : https://prove2.me/submissions/d7e73185-7c7b-4a36-a298-2cf4c6bce1d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_RiemannThetaModel_riemannTheta_zero_zero_half_period
import Theorems.Thm_GlobalTheory_RiemannThetaModel_one_le_re_riemannTheta_I_smul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution :
    riemannTheta 0 0 !![I] ![(1 + I) / 2] ≠ riemannTheta 0 0 !![I] 0 := by
  rw [riemannTheta_zero_zero_half_period]
  have h := one_le_re_riemannTheta_I_smul_one (ι := Fin 1)
  have e : (I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = !![I] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [e] at h
  intro h0
  rw [← h0] at h
  norm_num at h
end GlobalTheory.RiemannThetaModel

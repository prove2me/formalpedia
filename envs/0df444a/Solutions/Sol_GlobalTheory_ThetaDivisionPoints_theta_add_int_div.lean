-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.theta_add_int_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:27:31.983048+00:00
-- url     : https://prove2.me/submissions/c5d368f8-283a-4cf7-ada5-8918de763d12

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • ofIntVec m)) ((N : ℂ) • τ) =
      eC (ofRealVec a ⬝ᵥ ofIntVec m) * theta a 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaQuasiPeriod_holds (Fin g) a 0 ((N : ℂ) • z) ((N : ℂ) • τ) 0 m (hτ.smul _)
  rw [ofIntVec_zero, mulVec_zero, add_zero] at h
  rw [smul_add, smul_smul, mul_inv_cancel₀ hN, one_smul, h]
  congr 1
  simp [autFactor, ofIntVec_zero, eC_zero]
end GlobalTheory.ThetaDivisionPoints

-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.theta_add_tau_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:14.9297+00:00
-- url     : https://prove2.me/submissions/118196f2-acca-466a-a257-4212af7d4718

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
import Theorems.Thm_ReciprocityTheory_PTheta_thetaRealTransl_holds
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
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (n : Fin g → ℤ) :
    ∃ u : ℂ, u ≠ 0 ∧ theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) =
      u * theta (a + fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaRealTransl_holds (Fin g) a 0 (fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) (hτ.smul _)
  have e0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  have e1 : ofRealVec (fun i => (n i : ℝ) / N) = (N : ℂ)⁻¹ • ofIntVec n := by
    ext i; simp [ofRealVec, ofIntVec, div_eq_inv_mul]
  have e2 : ((N : ℂ) • τ) *ᵥ ((N : ℂ)⁻¹ • ofIntVec n) = (N : ℂ) • (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  rw [e0, add_zero, add_zero (0 : Fin g → ℝ)] at h
  rw [smul_add, ← e2, ← e1]
  exact ⟨_, Complex.exp_ne_zero _, h⟩
end GlobalTheory.ThetaDivisionPoints

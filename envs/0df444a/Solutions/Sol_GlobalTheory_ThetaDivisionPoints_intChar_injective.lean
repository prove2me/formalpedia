-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.intChar_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:48.217493+00:00
-- url     : https://prove2.me/submissions/0356b265-8923-412b-817e-5984661bead4

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
import Theorems.Thm_GlobalTheory_ThetaSpan_ofIntVec_single
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
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
theorem _root_.solution {g : ℕ} {N : ℕ} (hN : N ≠ 0) :
    Function.Injective (intChar (g := g) N) := by
  intro c c' h
  funext i
  have key : ∀ d : Fin g → Fin N, intChar N d (Multiplicative.ofAdd (Pi.single i 1)) =
      cexp (2 * Real.pi * I / N) ^ (d i : ℕ) := by
    intro d
    change eC (ofRealVec (fun i => ((d i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec (Pi.single i 1)) = _
    rw [GlobalTheory.ThetaSpan.ofIntVec_single, dotProduct_single_one, ← Complex.exp_nat_mul, eC]
    congr 1
    simp only [ofRealVec]
    push_cast
    ring
  have h1 := key c
  rw [h, key c'] at h1
  exact Fin.ext ((Complex.isPrimitiveRoot_exp N hN).pow_inj (c i).2 (c' i).2 h1.symm)
end GlobalTheory.ThetaDivisionPoints

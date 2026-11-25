-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.exists_theta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:36:19.92917+00:00
-- url     : https://prove2.me/submissions/42c0e2cb-6735-422a-9382-171cf8447dc4

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
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_mem_span_of_laws
import Theorems.Thm_GlobalTheory_ThetaSpan_laws_of_level
import Theorems.Thm_GlobalTheory_exists_level_apply_ne_zero_of_two_le
import Theorems.Thm_GlobalTheory_riemannTheta_level_one_ne_zero
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_P2M_GlobalTheory_classicalTheta_level_and_linearIndependent__6b643778a469
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
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    {N : ℕ} (hN : 2 ≤ N) (z : Fin g → ℂ) : ∃ c : Fin g → Fin N,
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 := by
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero classicalTheta_level_and_linearIndependent'
  obtain ⟨f, hf, hz⟩ := GlobalTheory.exists_level_apply_ne_zero_of_two_le f8 g τ hτ N hN z
  have hs := mem_span_of_laws hτ (by omega : 1 ≤ N) ⟨hf.1, GlobalTheory.ThetaSpan.laws_of_level τ N f hf.2⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  by_contra hcon
  push Not at hcon
  apply hz
  rw [← ha]
  simp [Finset.sum_apply, hcon]
end GlobalTheory.ThetaDivisionPoints

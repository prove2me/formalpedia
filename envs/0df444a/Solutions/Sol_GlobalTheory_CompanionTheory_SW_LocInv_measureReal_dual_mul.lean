-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInv.measureReal_dual_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:03.406117+00:00
-- url     : https://prove2.me/submissions/c90a3e8e-7af8-4952-921e-99d6c05b60be

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Theorems.Thm_GroundTheory_LocalField_inversion_const_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_measureReal_valBall
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard
import Theorems.Thm_GroundTheory_LocalField_selfDualMeasure_real_valBall_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.LocInv
theorem _root_.solution (ψ : AddChar K Circle) (k : ℤ) :
    (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) *
      (selfDualMeasure ψ).real (valBall K k) = 1 := by
  rw [measureReal_valBall _ (addCharConductor ψ - k), measureReal_valBall _ k,
    selfDualMeasure_real_valBall_zero]
  have hq : (0 : ℝ) < residueCard K := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have h := (inversion_const_eq_one_iff (K := K) (addCharConductor ψ)
    (Real.rpow_nonneg hq.le ((addCharConductor ψ : ℝ) / 2))).mpr rfl
  have e : (residueCard K : ℝ) ^ (-(addCharConductor ψ - k)) * (residueCard K : ℝ) ^ (-k) =
      (residueCard K : ℝ) ^ (-addCharConductor ψ) := by
    rw [← zpow_add₀ hq.ne']
    congr 1
    ring
  rw [← h, ← e]
  ring
end GlobalTheory.CompanionTheory.SW.LocInv

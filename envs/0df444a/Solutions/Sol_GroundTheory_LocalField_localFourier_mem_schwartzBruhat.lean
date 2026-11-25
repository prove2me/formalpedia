-- Prove2me | solution 1 for GroundTheory.LocalField.localFourier_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:36.141563+00:00
-- url     : https://prove2.me/submissions/6b29d9bf-d84d-4e83-a594-f7cebd392e28

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_isLocallyConstant_of_add_valBall
import Theorems.Thm_GroundTheory_LocalField_exists_invariant_of_mem_schwartzBruhat
import Theorems.Thm_GroundTheory_LocalField_localFourier_eq_zero_of_notMem
import Theorems.Thm_GroundTheory_LocalField_localFourier_add_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
namespace GroundTheory.LocalField
theorem _root_.solution {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localFourier μ ψ f ∈ schwartzBruhat K := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine ⟨isLocallyConstant_of_add_valBall (N := addCharConductor ψ - M)
    fun y h hh => localFourier_add_eq μ hψ hψ1 hM y hh, ?_⟩
  exact HasCompactSupport.intro (isCompact_valBall (addCharConductor ψ - N))
    fun y hy => localFourier_eq_zero_of_notMem μ hψ hψ1 hN hy
end GroundTheory.LocalField

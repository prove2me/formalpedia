-- Prove2me | solution 1 for GroundTheory.LocalField.meromorphicOn_localLFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:48.615926+00:00
-- url     : https://prove2.me/submissions/36538db0-165a-4a56-acd9-d405a7f9ad5c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Theorems.Thm_GroundTheory_LocalField_differentiable_qpow
import Theorems.Thm_GroundTheory_LocalField_localLFactor_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_localLFactor_of_not_isUnramified

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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
omit [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (χ : Kˣ →* ℂˣ) : MeromorphicOn (localLFactor χ) Set.univ := by
  intro s _
  by_cases h : IsUnramifiedChar χ
  · have e : localLFactor χ = fun s =>
        (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ :=
      funext fun s => localLFactor_of_isUnramified h s
    rw [e]
    exact ((((differentiable_qpow (K := K)).const_mul _).const_sub 1).analyticAt s).meromorphicAt.inv
  · have e : localLFactor χ = fun _ => (1 : ℂ) :=
      funext fun s => localLFactor_of_not_isUnramified h s
    rw [e]
    exact analyticAt_const.meromorphicAt
end GroundTheory.LocalField

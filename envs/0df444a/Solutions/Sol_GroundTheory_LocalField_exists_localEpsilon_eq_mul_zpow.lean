-- Prove2me | solution 1 for GroundTheory.LocalField.exists_localEpsilon_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:17.767551+00:00
-- url     : https://prove2.me/submissions/383f061d-4e69-4727-acaa-7f89594f3ee7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_not_isUnramified_eq
import Theorems.Thm_GroundTheory_LocalField_qcpow_mul_qcpow
import Theorems.Thm_GroundTheory_LocalField_qcpow_zpow


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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ a : ℂ, ∃ k : ℤ, ∀ s : ℂ, localEpsilon χ ψ s = a * ((residueCard K : ℂ) ^ (-s)) ^ k := by
  by_cases hu : IsUnramifiedChar χ
  · refine ⟨((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
      (residueCard K : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2), -addCharConductor ψ, fun s => ?_⟩
    rw [localEpsilon_of_isUnramified hu, qcpow_zpow, mul_assoc, qcpow_mul_qcpow]
    congr 2
    push_cast
    ring
  · refine ⟨(((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) *
      ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
          valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
        quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K,
      -(addCharConductor ψ - quasiCharConductor χ), fun s => ?_⟩
    rw [localEpsilon_of_not_isUnramified_eq hu, qcpow_zpow]
    rw [show ((-(addCharConductor ψ - (quasiCharConductor χ : ℤ)) : ℤ) : ℂ) * -s =
      (((addCharConductor ψ - quasiCharConductor χ : ℤ)) : ℂ) * s by push_cast; ring]
    ring
end GroundTheory.LocalField

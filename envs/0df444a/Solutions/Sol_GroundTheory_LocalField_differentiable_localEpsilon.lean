-- Prove2me | solution 1 for GroundTheory.LocalField.differentiable_localEpsilon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:25.557918+00:00
-- url     : https://prove2.me/submissions/06c9aaaa-81aa-48ba-aeaa-b8fea5e5cac7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_exists_localEpsilon_eq_mul_zpow
import Theorems.Thm_GroundTheory_LocalField_differentiable_qpow
import Theorems.Thm_GroundTheory_LocalField_qpow_ne_zero


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
theorem _root_.solution : Differentiable ℂ (localEpsilon χ ψ) := by
  obtain ⟨a, k, h⟩ := exists_localEpsilon_eq_mul_zpow (χ := χ) (ψ := ψ)
  rw [show localEpsilon χ ψ = fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ k from funext h]
  exact (differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a
end GroundTheory.LocalField

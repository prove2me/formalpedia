-- Prove2me | solution 1 for GroundTheory.LocalField.localEpsilon_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:13.357587+00:00
-- url     : https://prove2.me/submissions/0664548e-8896-406b-a347-f7f2f822f6b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_qcpow

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
theorem _root_.solution (h : IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s = ((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
      (residueCard K : ℂ) ^ ((addCharConductor ψ : ℂ) * (s - 1 / 2)) := by
  rw [localEpsilon, if_pos h, map_zpow, Units.val_zpow_eq_zpow_val, ← zpow_neg,
    modulus_cpow_eq_qcpow (unifUnit K ^ addCharConductor ψ).ne_zero, ord_unifUnit_zpow]
  congr 2
  ring
end GroundTheory.LocalField

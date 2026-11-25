-- Prove2me | solution 1 for GroundTheory.LocalField.localEpsilon_of_not_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:34.645573+00:00
-- url     : https://prove2.me/submissions/c4a465d9-cc6c-4c02-8652-93f48dfb785a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon

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
theorem _root_.solution (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
          valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
        quasiCharExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-s) * (ψ x : ℂ) ∂selfDualMeasure ψ := by
  rw [localEpsilon, if_neg h]
end GroundTheory.LocalField

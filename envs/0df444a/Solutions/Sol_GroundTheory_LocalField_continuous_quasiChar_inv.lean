-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_quasiChar_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:21.535692+00:00
-- url     : https://prove2.me/submissions/1fcd44f9-40a0-40c3-9f2f-73b84132f229

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar

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
variable (χ : Kˣ →* ℂˣ)
variable {χ}
variable (hχ : Continuous χ)
include hχ
omit hχ
namespace GroundTheory.LocalField
theorem _root_.solution (hχ : Continuous χ) : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := by
  have : ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
    funext u
    rfl
  rw [this]
  exact hχ.inv
end GroundTheory.LocalField

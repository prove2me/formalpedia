-- Prove2me | solution 1 for GroundTheory.LocalField.localZeta_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:03.973813+00:00
-- url     : https://prove2.me/submissions/68a575a4-c4d0-4bcb-add8-eb49ad733dd8

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
variable {χ : Kˣ →* ℂˣ}
namespace GroundTheory.LocalField
theorem _root_.solution (c : ℂ) (f : K → ℂ) (s : ℂ) :
    localZeta (fun x => c * f x) χ s = c * localZeta f χ s := by
  unfold localZeta
  rw [← integral_const_mul]
  congr 1
  funext u
  ring
end GroundTheory.LocalField

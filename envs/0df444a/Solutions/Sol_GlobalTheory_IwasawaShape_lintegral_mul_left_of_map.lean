-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.lintegral_mul_left_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:34.36318+00:00
-- url     : https://prove2.me/submissions/6ed8d0f6-bf92-4913-9e69-5756dc02e982

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
omit [MeasurableInv G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by
  have e := lintegral_map (μ := ρ) hf (measurable_const_mul p)
  rw [h] at e
  exact e.symm
end GlobalTheory.IwasawaShape

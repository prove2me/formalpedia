-- Prove2me | solution 1 for GroundTheory.Global.inv_mul_le_one_iff_withZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:05.715052+00:00
-- url     : https://prove2.me/submissions/5a16c117-464d-4cbb-9922-4bf240d06ac4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {b c : ℤᵐ⁰} (hc : c ≠ 0) : c⁻¹ * b ≤ 1 ↔ b ≤ c := by
  constructor
  · intro h
    calc b = c * (c⁻¹ * b) := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one c
  · intro h
    calc c⁻¹ * b ≤ c⁻¹ * c := by gcongr
      _ = 1 := inv_mul_cancel₀ hc
end GroundTheory.Global

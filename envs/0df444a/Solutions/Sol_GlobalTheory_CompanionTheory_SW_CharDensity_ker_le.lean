-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:14.921845+00:00
-- url     : https://prove2.me/submissions/efb45a8d-6673-4e5e-83b6-d21fcabd679b

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution {b : ℝ} (hb : 0 < b) (w : V) :
    ker b w ≤ (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold ker
  have hp := Real.pi_pos
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi ^ 2 / b * ‖w‖ ^ 2 := by positivity
  linarith
end GlobalTheory.CompanionTheory.SW.CharDensity

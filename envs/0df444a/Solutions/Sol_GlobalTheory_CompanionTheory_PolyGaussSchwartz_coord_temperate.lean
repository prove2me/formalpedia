-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord_temperate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:17.237889+00:00
-- url     : https://prove2.me/submissions/80b2fd8a-ddf8-4e91-9c02-c15f283f8b15

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz
theorem _root_.solution (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth
end GlobalTheory.CompanionTheory.PolyGaussSchwartz

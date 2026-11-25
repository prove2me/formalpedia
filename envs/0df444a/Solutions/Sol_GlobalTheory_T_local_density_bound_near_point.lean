-- Prove2me | solution 1 for GlobalTheory.T.local_density_bound_near_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:34.976665+00:00
-- url     : https://prove2.me/submissions/74dc1421-a0ea-47ef-b9b6-8949c1830b25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPointStatement
import Theorems.Thm_GlobalTheory_LineCos_exists_map_cosSq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (T : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))) (ρ : ReciprocityTheory.L2DbarEstimates.V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : ReciprocityTheory.L2DbarEstimates.V (d + 1)),
    IsOpen T → z₀ ∈ T → ContinuousOn ρ T → ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) T →
    (∀ z ∈ T, (G (GlobalTheory.LineCos.base z)).PosDef) →
    ∃ N : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.exists_map_cosSq_le | exact GlobalTheory.LineCos.exists_map_cosSq_le | (intros; apply GlobalTheory.LineCos.exists_map_cosSq_le <;> assumption)
end _root_.GlobalTheory.T

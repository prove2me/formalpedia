-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedSignedRestartAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:00:03.210615+00:00
-- url     : https://prove2.me/submissions/b7a2928a-db66-4dc3-bb4c-73a851c55c74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionSupSplitUpperV1
import Theorems.Thm_Kyprianou_Ch03_reflectionSupSplitLowerV1
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (c y : ℝ) (hy : 0 ≤ y)
    (r : Omega → NNReal) (t : NNReal) :
    ∀ᵐ w ∂P,
      reflectedSup (fun s v => c * X s v) y (r w + t) w =
      max (reflectedSup (fun s v => c * X s v) y (r w) w)
        (LevyExtrema.SBA.runSup (fun s => c * (X (r w + s) w - X (r w) w)) t)
        - c * (X (r w + t) w - X (r w) w) := by
  filter_upwards [hX.cadlag_ae] with w hw
  let a := r w
  let g : NNReal → ℝ := fun s => c * X s w
  let G : NNReal → ℝ := fun s => g (a+s) - g a
  have hb := reflectionSignedCompactBoundV1 (fun s => X s w) hw c (a+t)
  have hs := le_antisymm (reflectionSupSplitUpperV1 g a t hb)
    (reflectionSupSplitLowerV1 g a t hb)
  have he : (fun s => c * (X (a+s) w - X a w)) = G := by
    funext s
    dsimp [G,g]
    ring
  change max y (LevyExtrema.SBA.runSup g (a+t)) - g (a+t) =
    max (max y (LevyExtrema.SBA.runSup g a) - g a)
      (LevyExtrema.SBA.runSup (fun s => c * (X (a+s) w - X a w)) t) -
        c * (X (a+t) w - X a w)
  rw [he,hs]
  have ht : c * (X (a+t) w - X a w) = g (a+t) - g a := by
    dsimp [g]
    ring
  rw [ht, ← max_assoc]
  have hm := max_sub_sub_right (max y (LevyExtrema.SBA.runSup g a))
    (LevyExtrema.SBA.runSup G t + g a) (g a)
  rw [add_sub_cancel_right] at hm
  rw [hm]
  ring

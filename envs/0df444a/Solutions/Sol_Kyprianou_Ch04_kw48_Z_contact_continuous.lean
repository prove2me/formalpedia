-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_Z_contact_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:09.597981+00:00
-- url     : https://prove2.me/submissions/c9dec348-091f-4b44-96ad-74835ffe4e19

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- At a positive contact time the process has no downward jump
and its two-parameter characteristic process is continuous. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (w : Ω) (t : NNReal) (ht : 0 < t)
    (hContact : L.X t w = runningSup L t w) :
    ContinuousAt (fun r : NNReal => Z L alpha beta r w) t := by
  obtain ⟨l,hl⟩ := L.leftLim w t ht
  haveI : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot' (show (Iio t).Nonempty from ⟨0,ht⟩) le_rfl
  have hUpper : l ≤ runningSup L t w := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((runningSup_monotone_and_path_le L w).2 s).trans
      ((runningSup_monotone_and_path_le L w).1 hs.le)
  have hLower := L.noPosJumps w t l ht hl
  have heq : l = L.X t w := le_antisymm (hContact ▸ hUpper) hLower
  rw [heq] at hl
  have hLeft : ContinuousWithinAt (fun r => L.X r w) (Iio t) t := hl
  have hRight := L.rightCont w t
  have hX : ContinuousAt (fun r => L.X r w) t := by
    rw [← continuousWithinAt_univ, ← Iio_union_Ici]
    exact hLeft.union hRight
  have hU := (runningSup_continuous_actual L w).continuousAt (x := t)
  unfold Z
  fun_prop (disch := assumption)

-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_path_weight_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:16:07.763303+00:00
-- url     : https://prove2.me/submissions/b5adb912-4582-48c4-8dc1-cb11a4b6d440

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ s ≤ T, |g ((s:ℝ),X s w)| ≤ M) ∧
      (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),L s w)| ≤ M) := by
  obtain ⟨_,R,hR,hX,hL⟩ := exercise41PathCompactV10 X L w hc hl T
  let K := Icc (0:ℝ) (T:ℝ) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : K ⊆ Ici (0:ℝ) ×ˢ (univ : Set ℝ) :=
    fun z hz => ⟨hz.1.1,mem_univ _⟩
  obtain ⟨M,hM⟩ := (hK.image_of_continuousOn (hg.mono hsub).abs).bddAbove
  refine ⟨max 0 M,le_max_left _ _,?_,?_⟩
  · intro s hs
    have h1 : (s:ℝ) ≤ (T:ℝ) := by exact_mod_cast hs
    exact (hM ⟨((s:ℝ),X s w),⟨⟨s.coe_nonneg,h1⟩,abs_le.mp (hX s hs)⟩,rfl⟩).trans (le_max_right _ _)
  · intro s hs hst
    have h1 : (s:ℝ) ≤ (T:ℝ) := by exact_mod_cast hst
    exact (hM ⟨((s:ℝ),L s w),⟨⟨s.coe_nonneg,h1⟩,abs_le.mp (hL s hs hst)⟩,rfl⟩).trans (le_max_right _ _)

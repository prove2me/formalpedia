-- Prove2me | solution 1 for Kyprianou.Ch04.strictLeftSampleWeightLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:37:13.893015+00:00
-- url     : https://prove2.me/submissions/58a053f4-4d8e-4d2a-9544-fab2b3eb7018

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Strict-left state samples and time continuity give convergence of predictable weights. -/
theorem solution (g : ℝ → ℝ → ℝ) (Y : NNReal → ℝ)
    (t : NNReal) (l : ℝ) (u : ℕ → NNReal)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hu : Tendsto u atTop (𝓝[<] t))
    (hY : Tendsto Y (𝓝[<] t) (𝓝 l)) :
    Tendsto (fun n => g (u n : ℝ) (Y (u n))) atTop (𝓝 (g (t : ℝ) l)) := by
  have ht : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (t : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (hu.mono_right nhdsWithin_le_nhds)
  have hp := ht.prodMk_nhds (hY.comp hu)
  have hpair : Tendsto (fun n => ((u n : ℝ), Y (u n))) atTop
      (𝓝[Ici (0 : ℝ) ×ˢ univ] ((t : ℝ), l)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hp, Eventually.of_forall fun n => ⟨(u n).coe_nonneg, mem_univ _⟩⟩
  exact (hg ((t : ℝ), l) ⟨t.coe_nonneg, mem_univ _⟩).tendsto.comp hpair

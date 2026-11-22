-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:03:30.158807+00:00
-- url     : https://prove2.me/submissions/c7f722d6-bc09-430c-bc46-608238e3ade3

import Mathlib

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by
  let C := eLpNorm b 2 μ
  let D := fun n => eLpNorm (a n - b) 2 μ
  have hc : Tendsto (fun _ : ι => C) l (𝓝 C) := tendsto_const_nhds
  have hd : Tendsto D l (𝓝 0) := htend
  have hu : Tendsto (fun n => D n + C + C) l (𝓝 (C + C)) := by
    simpa only [zero_add] using (hd.add hc).add hc
  have hprod : Tendsto (fun n => D n * (D n + C + C)) l (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul hd (Or.inr (ENNReal.add_ne_top.mpr ⟨hbfin, hbfin⟩)) hu (Or.inr ENNReal.zero_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod (fun _ => bot_le)
  intro n
  have hm := (ha n).aestronglyMeasurable
  have hn := hb.aestronglyMeasurable
  have hbnd : eLpNorm (a n) 2 μ ≤ D n + C := by
    simpa only [sub_add_cancel, D, C] using (eLpNorm_add_le (hm.sub hn) hn (p := 2) (by norm_num))
  have heq : (fun ω => a n ω ^ 2 - b ω ^ 2) = (a n - b) • (a n + b) := by
    funext ω
    change _ = (a n ω - b ω) * (a n ω + b ω)
    ring
  change eLpNorm (fun ω => a n ω ^ 2 - b ω ^ 2) 1 μ ≤ D n * (D n + C + C)
  rw [heq]
  calc
    _ ≤ D n * eLpNorm (a n + b) 2 μ := eLpNorm_smul_le_mul_eLpNorm (hm.add hn) (hm.sub hn)
    _ ≤ D n * (D n + C + C) := by
      gcongr
      exact (eLpNorm_add_le hm hn (p := 2) (by norm_num)).trans (add_le_add_left hbnd C)

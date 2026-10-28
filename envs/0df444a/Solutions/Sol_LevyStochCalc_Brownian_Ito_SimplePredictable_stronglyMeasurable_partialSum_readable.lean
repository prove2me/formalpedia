-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_partialSum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:15.642042+00:00
-- url     : https://prove2.me/submissions/a123a072-5f35-42af-8283-df3989ea8780

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
omit [MeasurableSpace Ω] in
/-- A finite sum of processes measurable for a sub-σ-algebra is measurable for it. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_range_sum {m : MeasurableSpace Ω} {n : ℕ} {f : ℕ → Ω → ℝ}
    (h : ∀ i ∈ Finset.range n, @MeasureTheory.StronglyMeasurable Ω ℝ _ m (f i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ m (fun ω => ∑ i ∈ Finset.range n, f i ω) :=
  @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ m _ _ _ h
theorem solution (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {k : ℕ} (hk : k ≤ G.N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k) := by
  refine LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_range_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hiN : i < G.N := lt_of_lt_of_le hi hk
  have hterm : G.term W i = fun ω => G.ξ ⟨i, hiN⟩ ω
      * (W.W (G.partition (⟨i, hiN⟩ : Fin G.N).succ) ω
        - W.W (G.partition (⟨i, hiN⟩ : Fin G.N).castSucc) ω) := by
    funext ω; rw [LevyStochCalc.Brownian.Ito.SimplePredictable.term, dif_pos hiN]
  rw [hterm]
  have hle1 : G.partition (⟨i, hiN⟩ : Fin G.N).castSucc
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.castSucc]; omega)
  have hle2 : G.partition (⟨i, hiN⟩ : Fin G.N).succ
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.succ]; omega)
  exact ((h_adapt ⟨i, hiN⟩).mono (ℱ.mono hle1)).mul
    (((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle2)).sub
      ((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle1)))

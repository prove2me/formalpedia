-- Prove2me | solution 1 for Kyprianou.Ch03.levy_shiftedGerm_le_nullCompletion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T11:09:10.952075+00:00
-- url     : https://prove2.me/submissions/b68bbe26-eadc-42d8-9f7d-2949fc497a9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_germ_zero_one_of_shift_independence_ws01f
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_measurable
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_tendsto_zero_ae
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_shift_indep
import Theorems.Thm_Kyprianou_Ch03_germ_zero_one_le_nullCompletion

open Filter MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal Topology

set_option autoImplicit false

/-!
Blumenthal for the shifted Lévy process $Y_u = X_{t+u}-X_t$.

1. Open: measurability / a.e. continuity at 0 / full-path shift independence of $Y$.
2. Proved: `germ_zero_one_of_shift_independence_ws01f` ⇒ germ is $0$–$1$.
3. Open: a $0$–$1$ germ sits in the null `generateFrom` $\sigma$-algebra.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    germSigma (fun u : NNReal => fun omega : Omega => X (t + u) omega - X t omega) ≤
      MeasurableSpace.generateFrom
        {A : Set Omega |
          exists N : Set Omega,
            MeasurableSet N ∧ P N = 0 ∧ A ⊆ N} := by
  set Y : NNReal → Omega → Real := fun u ω => X (t + u) ω - X t ω
  have hBm : ∀ u, Measurable (Y u) := fun u =>
    levy_shifted_process_measurable P X hX t u
  have hC : ∀ᵐ ω ∂P, Tendsto (fun u => Y u ω) (nhds (0 : NNReal)) (nhds 0) :=
    levy_shifted_process_tendsto_zero_ae P X hX t
  have hShift : ∀ s : NNReal, 0 < s →
      Indep
        (MeasurableSpace.comap
          (fun ω (u : NNReal) => Y (s + u) ω - Y s ω) MeasurableSpace.pi)
        (pastSigma Y s) P := by
    intro s hs
    have hform :
        (fun ω (u : NNReal) => Y (s + u) ω - Y s ω) =
          (fun ω (u : NNReal) =>
            (X (t + (s + u)) ω - X t ω) - (X (t + s) ω - X t ω)) := by
      funext ω u; simp [Y]
    simpa [hform] using levy_shifted_process_shift_indep P X hX t s hs
  have h01 : ∀ {A : Set Omega}, @MeasurableSet Omega (germSigma Y) A → P A = 0 ∨ P A = 1 :=
    fun {A} hA =>
      AvramDividend.Classical.germ_zero_one_of_shift_independence_ws01f
        (B := Y) hBm hC hShift hA
  exact germ_zero_one_le_nullCompletion P Y h01

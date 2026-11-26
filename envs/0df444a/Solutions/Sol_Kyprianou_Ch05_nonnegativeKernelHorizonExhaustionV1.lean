-- Prove2me | solution 1 for Kyprianou.Ch05.nonnegativeKernelHorizonExhaustionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:58:54.573536+00:00
-- url     : https://prove2.me/submissions/5befb056-97dc-4726-9440-339e3fc48c95

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (Q : Measure Omega) (N : Omega → Measure E)
    (g : Omega → E → ENNReal) (hg : ∀ w, Measurable (g w))
    (S : ℕ → Set E) (hS : ∀ n, MeasurableSet (S n)) (hm : Monotone S)
    (hM : ∀ n, AEMeasurable (fun w => ∫⁻ z in S n, g w z ∂N w) Q) :
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in S n, g w z ∂N w ∂Q) atTop
      (nhds (∫⁻ w, ∫⁻ z in ⋃ n, S n, g w z ∂N w ∂Q)) := by
  classical
  have hmono (w : Omega) : Monotone (fun n => ∫⁻ z in S n, g w z ∂N w) :=
    fun i j hij => lintegral_mono_set (hm hij)
  have he (w : Omega) : (∫⁻ z in ⋃ n, S n, g w z ∂N w) =
      ⨆ n, ∫⁻ z in S n, g w z ∂N w := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hS)]
    have hg' (n : ℕ) : Measurable ((S n).indicator (g w)) := (hg w).indicator (hS n)
    have hmon : Monotone (fun n => (S n).indicator (g w)) :=
      fun i j hij z => Set.indicator_le_indicator_of_subset (hm hij) (fun _ => zero_le) z
    have hi : (⋃ n, S n).indicator (g w) = fun z => ⨆ n, (S n).indicator (g w) z := by
      funext z
      by_cases hz : z ∈ ⋃ n, S n
      · obtain ⟨n,hn⟩ := mem_iUnion.mp hz
        rw [Set.indicator_of_mem hz]
        apply le_antisymm
        · exact le_iSup_of_le n (by rw [Set.indicator_of_mem hn])
        · exact iSup_le (fun i => Set.indicator_le_self' (fun _ _ => zero_le) _)
      · rw [Set.indicator_of_notMem hz]
        symm
        apply le_antisymm (iSup_le fun n => by
          rw [Set.indicator_of_notMem (fun hn => hz (mem_iUnion.mpr ⟨n,hn⟩))]
          exact le_rfl) bot_le
    rw [hi,lintegral_iSup hg' hmon]
    simp_rw [lintegral_indicator (hS _)]
  simp_rw [he]
  rw [lintegral_iSup' hM (ae_of_all _ hmono)]
  exact tendsto_atTop_iSup (fun i j hij => lintegral_mono (fun w => hmono w hij))

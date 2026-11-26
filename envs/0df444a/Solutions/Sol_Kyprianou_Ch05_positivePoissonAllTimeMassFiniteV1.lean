-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonAllTimeMassFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:40.890252+00:00
-- url     : https://prove2.me/submissions/c80b9b4c-9967-4c73-b611-959bc2f3b992

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMassFiniteV1
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
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi) :
    ∀ᵐ w ∂Q, ∀ t : NNReal, (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) < ⊤ := by
  have hn : ∀ n : ℕ, ∀ᵐ w ∂Q,
      (∫⁻ z in Ioc (0 : ℝ) (n : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) < ⊤ :=
    fun n => positivePoissonStripMassFiniteV1 Q Pi K Z hd hint 0 n
  filter_upwards [ae_all_iff.2 hn] with w hw
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge (t : ℝ)
  exact (lintegral_mono_set (show Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ) ⊆
    Ioc (0 : ℝ) (n : ℝ) ×ˢ Ioi (0 : ℝ) from
    fun z hz => ⟨⟨hz.1.1,hz.1.2.trans hn⟩,hz.2⟩)).trans_lt (hw n)

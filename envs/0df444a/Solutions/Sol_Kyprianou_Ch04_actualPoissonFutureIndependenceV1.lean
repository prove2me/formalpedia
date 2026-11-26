-- Prove2me | solution 1 for Kyprianou.Ch04.actualPoissonFutureIndependenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:32.016713+00:00
-- url     : https://prove2.me/submissions/406e0210-66fb-4d79-aa6c-e7c1f95d6233

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch04_completedFutureFunctionalIndepV1
import Theorems.Thm_Kyprianou_Ch04_shiftedMarkedCountExtractorV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual intrinsic jump measure of a Lévy process has future counts independent of its completed past. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω)))
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X L ω) :
    Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N := by
  intro s t B hst hB
  obtain ⟨G,hG,hExtract⟩ := Kyprianou.Ch04.shiftedMarkedCountExtractorV1 s (t-s) B hB
  apply Kyprianou.Ch04.completedFutureFunctionalIndepV1 P F X hX hF s G hG
  filter_upwards [hX.cadlag_ae,hL,hN] with ω hω hl hn
  rw [hn, ← add_tsub_cancel_of_le hst]
  exact hExtract X L ω (fun u => (hω u).1) hl

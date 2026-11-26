-- Prove2me | solution 1 for Kyprianou.Ch04.actualPoissonPastMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:19:39.973395+00:00
-- url     : https://prove2.me/submissions/08f57258-2b71-42ab-824f-022cdef0c5f6

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkExtractorV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathMarkedCountV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathRightContinuousV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftExistenceV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureCountV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual Poisson jump measure is measurable on the completed natural past. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω)))
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X L ω) :
    ∀ (T : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ →
      Measurable[F T] (fun ω => N.N ω D) := by
  intro T D hD hsub
  obtain ⟨G,hG,hExtract⟩ := Kyprianou.Ch04.arbitraryTimeMarkExtractorV1 D hD
  let Z (ω : Ω) (u : NNReal) := X (min u T) ω
  have hAdapt := Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1 P X F hF
  have hCoord (u : NNReal) : Measurable[F T] (fun ω => Z ω u) :=
    (hAdapt (min u T)).mono (F.mono (min_le_right u T)) le_rfl
  have hZ : Measurable[F T] Z := by
    letI : MeasurableSpace Ω := F T
    exact measurable_pi_lambda _ hCoord
  apply Kyprianou.Ch04.completedMeasAECongrV1 P X F hF T _ _ (hG.comp hZ)
  filter_upwards [hX.cadlag_ae,hL,hN] with ω hCad hl hn
  have hr : ∀ u, ContinuousWithinAt (fun v => X v ω) (Ici u) u := fun u => (hCad u).1
  have hx := Kyprianou.Ch04.rightContinuousTimeMeasurableV1 (fun u => X u ω) hr
  have hLm := Kyprianou.Ch04.leftLimitTimeMeasurableV1 (fun u => X u ω) (fun u => L u ω) hx hl
  rw [hn, Kyprianou.Ch04.pathJumpMeasureCountV1 X L ω hx hLm D hD]
  rw [Kyprianou.Ch04.frozenPathMarkedCountV1 (fun u => X u ω) (fun u => L u ω) T hl D hsub]
  exact hExtract (Z ω)
    (Kyprianou.Ch04.frozenPathRightContinuousV1 (fun u => X u ω) T hr)
    (Kyprianou.Ch04.frozenPathLeftExistenceV1 (fun u => X u ω) (fun u => L u ω) T hl)

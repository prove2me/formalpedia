-- Prove2me | solution 1 for Kyprianou.Ch03.snlCommonAllPathRegularizationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:18.706677+00:00
-- url     : https://prove2.me/submissions/41e77f9d-0dc0-4c3b-a071-74a1129dfbac

import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_negativeLevyNoPositiveJumpsAEV1
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_allpath_cadlag_version
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open scoped Topology

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∃ Y : NNReal → Omega → ℝ,
      (∀ᵐ w ∂P, ∀ t, Y t w = X t w) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ w, Y 0 w = 0) ∧
      (∀ w t, ContinuousWithinAt (fun s => Y s w) (Set.Ici t) t) ∧
      (∀ w t, 0 < t → ∃ l, Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 l)) ∧
      (∀ w t l, 0 < t → Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 l) → Y t w ≤ l) := by
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hj := Kyprianou.Ch03.negativeLevyNoPositiveJumpsAEV1 P X hX T hLK hNegative
  obtain ⟨Y, he, hy, hz, hc, hjy⟩ :=
    Kyprianou.Ch08.StageB.source_result81_allpath_cadlag_version
      Omega P X hm hX.start_zero hX.cadlag_ae hj
  exact ⟨Y, he, hy, fun w => congrFun hz w,
    fun w t => (hc w t).1, fun w t _ => (hc w t).2, hjy⟩

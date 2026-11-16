-- Prove2me | solution 1 for Kyprianou.Ch06.levyProcessOfWeakGridIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:17:29.294984+00:00
-- url     : https://prove2.me/submissions/54c69df5-0c99-4fa6-a4df-d56be987edd2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch06_stationaryIncrementsFromMarginalLaw
import Theorems.Thm_Kyprianou_Ch06_cadlagFromPathRegularity
import Theorems.Thm_Kyprianou_Ch06_zeroTimeNormalisationAeEq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- All published IsLevyProcess requirements follow for the pointwise-normalised
process once the remaining weak-grid independent-increments obligation is known. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t))
    (hindep : ProbabilityTheory.HasIndependentIncrements X P)
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => if t = 0 then (0 : Real) else X t ω) P := by
  let Y : NNReal → Ω → Real := fun t ω => if t = 0 then 0 else X t ω
  have hAE : ∀ᵐ ω ∂P, ∀ t : NNReal, Y t ω = X t ω :=
    Kyprianou.Ch06.zeroTimeNormalisationAeEq P X hzero
  have hYmeas : ∀ t : NNReal, Measurable (Y t) := by
    intro t
    by_cases ht : t = 0
    · subst t
      simpa [Y] using (measurable_const : Measurable (fun _ : Ω => (0 : Real)))
    · simpa [Y, ht] using hmeas t
  have hYzero : ∀ᵐ ω ∂P, Y 0 ω = 0 := by
    exact Filter.Eventually.of_forall (fun ω => by simp [Y])
  have hmap (t : NNReal) : P.map (Y t) = P.map (X t) := by
    apply Measure.map_congr
    filter_upwards [hAE] with ω hω
    exact hω t
  have hincrements (s t : NNReal) :
      P.map (fun ω => Y (s + t) ω - Y s ω) =
        P.map (fun ω => X (s + t) ω - X s ω) := by
    apply Measure.map_congr
    filter_upwards [hAE] with ω hω
    rw [hω (s + t), hω s]
  have hYlaw (s t : NNReal) :
      P.map (fun ω => Y (s + t) ω - Y s ω) = P.map (Y t) :=
    (hincrements s t).trans ((hlaw s t).trans (hmap t).symm)
  have hYstat : ProbabilityTheory.HasStationaryIncrements Y P :=
    Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw P Y hYmeas hYzero hYlaw
  have hYindep : ProbabilityTheory.HasIndependentIncrements Y P := by
    intro n ts hts
    have heq : ∀ i : Fin n,
        (fun ω => X (ts i.succ) ω - X (ts i.castSucc) ω) =ᵐ[P]
        (fun ω => Y (ts i.succ) ω - Y (ts i.castSucc) ω) := by
      intro i
      filter_upwards [hAE] with ω hω
      rw [hω (ts i.succ), hω (ts i.castSucc)]
    exact (hindep n ts hts).congr heq
  have hYcadlag : ∀ᵐ ω ∂P,
      ProbabilityTheory.IsCadlag (fun t => Y t ω) := by
    have hCadX := Kyprianou.Ch06.cadlagFromPathRegularity P X hregular
    filter_upwards [hAE, hCadX] with ω hω hcad
    have heq : (fun t => Y t ω) = (fun t => X t ω) := funext hω
    simpa [heq] using hcad
  exact ⟨by funext ω; simp [Y], hYindep, hYstat, hYcadlag⟩

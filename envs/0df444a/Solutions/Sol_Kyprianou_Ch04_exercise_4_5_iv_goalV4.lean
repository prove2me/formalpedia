-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_iv_goalV4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:57:43.000116+00:00
-- url     : https://prove2.me/submissions/846714d3-d47e-4816-a20a-ed14de794cd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV4
import Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedBoundedFamilyWitnessV2
import Theorems.Thm_Kyprianou_Ch04_gluedLocalMartingaleStoppedEqV1
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Transfer stopped martingales to the consistent glued process. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_5_ivV4 := by
  unfold Kyprianou.Ch04.certificate_ex4_5_ivV4
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hLeftZero hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint X2 hX2Representation
  obtain ⟨Mf,stops,I,I2,hCons,hGrid,hSum,hUCP,hStop,hMono,hEx,hMart,hIto⟩ :=
    Kyprianou.Ch04.exercise45LocalisedBoundedFamilyWitnessV2 P F X hLevy
      triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hLeftZero hNLaw f fTime
      fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint X2
      hX2Representation
  let M : NNReal → Ω → ℝ := fun t w =>
    if h : ∃ k : ℕ, t ≤ stops k w then Mf (Nat.find h) t w else 0
  have hEq := Kyprianou.Ch04.gluedLocalMartingaleStoppedEqV1 P Mf stops hMono hCons
  refine ⟨M,stops,I,I2,hGrid,hSum,hUCP,hStop,hMono,hEx,?_,hIto⟩
  intro n
  have he (t : NNReal) :
      (fun w => M (min t (stops n w)) w) =ᵐ[P]
      (fun w => Mf n (min t (stops n w)) w) := by
    filter_upwards [hEq] with w hw
    exact hw n t
  apply (hMart n).congr _ (fun t => (he t).symm)
  intro t
  exact (Kyprianou.Ch04.completedMeasAECongrV1 P X F hFiltration t _ _
    ((hMart n).stronglyAdapted t).measurable (he t)).stronglyMeasurable

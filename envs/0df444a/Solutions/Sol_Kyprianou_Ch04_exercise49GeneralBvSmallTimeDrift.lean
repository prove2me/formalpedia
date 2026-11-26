-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:48:08.100376+00:00
-- url     : https://prove2.me/submissions/ddf87d73-03ff-49c6-b056-3c1dc8d411df

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvPathRepV1
import Theorems.Thm_Kyprianou_Ch04_bvCompactPathDerivativeV1
import Theorems.Thm_Kyprianou_Ch04_rationalSlopeAtInteriorV1
import Theorems.Thm_Kyprianou_Ch04_stationaryRationalDriftAtOriginV1
import Theorems.Thm_Kyprianou_Ch04_rationalRightLimitBridgeV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Set Topology

/-- Complete the general bounded-variation small-time drift limit. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))) :
    ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega / (t : Real))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0))
        (nhds drift) := by
  have hrep := Kyprianou.Ch04.bvPathRepV1 P X hLevy triplet hTriplet hBV drift hDrift
  have hA : ∀ᵐ ω ∂P, ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun r : ℚ =>
        (X (Real.toNNReal s + Real.toNNReal (r : ℝ)) ω - X (Real.toNNReal s) ω) /
          (Real.toNNReal (r : ℝ) : ℝ))
        (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds drift) := by
    filter_upwards [hrep] with ω hr
    filter_upwards [Kyprianou.Ch04.bvCompactPathDerivativeV1 (fun t => X t ω) drift hr,
      ae_restrict_mem measurableSet_Ioo] with s hs hm
    exact Kyprianou.Ch04.rationalSlopeAtInteriorV1 (fun t => X t ω) drift s hm.1.le hs
  have h0 := Kyprianou.Ch04.stationaryRationalDriftAtOriginV1 P X hLevy drift hA
  filter_upwards [h0, hLevy.cadlag_ae] with ω hω hc
  apply (Kyprianou.Ch04.rationalRightLimitBridgeV1 (fun t => X t ω / (t : ℝ)) drift ?_).mp hω
  intro t ht
  exact (hc t).1.div continuous_subtype_val.continuousWithinAt (by exact_mod_cast ht.ne')

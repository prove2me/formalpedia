-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1StationaryWorkload
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:06:29.320555+00:00
-- url     : https://prove2.me/submissions/606a2d10-5fa4-48cd-b385-b53e8dbd7bea

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkload_positiveTrafficLimit
import Theorems.Thm_Kyprianou_Ch04_exercise46MM1TrafficIntegratedTailV1
import Theorems.Thm_Kyprianou_Ch04_exercise46MM1GeometricMixtureIdentityV1
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_runningSup_nonnegative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exercise 4.6(iii) (p. 108). M/M/1 limiting workload mixture. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (lambda mu : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu)
    (hd : L.drift = 1)
    (hServiceLaw :
      L.ν =
        ((volume : Measure Real).restrict (Set.Iio 0)).withDensity
          (fun y : Real =>
            ENNReal.ofReal (lambda * mu * Real.exp (mu * y)))) :
    ∃ stationary : Measure Real,
      IsProbabilityMeasure stationary ∧
      stationary =
        ENNReal.ofReal (1 - lambda / mu) •
          ((Measure.dirac (0 : Real)) +
            ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
              (fun x : Real =>
                ENNReal.ofReal (lambda * Real.exp (-(mu - lambda) * x)))) ∧
      (∀ f : BoundedContinuousFunction Real Real,
        let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal -> Omega -> Real := fun t omega =>
          supX t omega - L.X t omega
        Tendsto
          (fun t : NNReal => ∫ omega, f (W t omega) ∂P)
          atTop (nhds (∫ x : Real, f x ∂stationary))) := by
  obtain ⟨hr, he⟩ := Kyprianou.Ch04.exercise46MM1TrafficIntegratedTailV1
    lambda mu hlambda hmu L.ν hServiceLaw
  have hm : 0 < mu := hlambda.trans hmu
  let rho : ENNReal := (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift
  have hR : rho = ENNReal.ofReal (lambda/mu) := by simp [rho, hd, hr]
  have hpos : 0 < rho := by rw [hR]; exact ENNReal.ofReal_pos.mpr (div_pos hlambda hm)
  have hlt : rho < 1 := by rw [hR, ← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : Real) < 1)).mpr ((div_lt_one hm).mpr hmu)
  obtain ⟨nu, hn, hEta, _, hLaw, hConv⟩ :=
    Kyprianou.Ch04.stationaryWorkload_positiveTrafficLimit P F L hBV
      (by rw [hd]; norm_num) hpos hlt
  let eta : Measure Real := ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
    (fun x => L.ν (Set.Iio (-x)) / (ENNReal.ofReal L.drift * rho))
  letI : IsProbabilityMeasure nu := hn
  letI : IsProbabilityMeasure eta := hEta
  have hE : eta = ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (mu*Real.exp (-mu*x))) := by
    simpa [eta, rho, hd] using he
  have hEq := Kyprianou.Ch04.exercise46MM1GeometricMixtureIdentityV1
    lambda mu hlambda hmu nu eta hE (by simpa only [← hR] using hLaw)
  refine ⟨nu, hn, hEq, ?_⟩
  intro f
  have hs (t : NNReal) (w : Omega) :
      0 ≤ sSup ((fun s : NNReal => L.X s w) '' Set.Iic t) := by
    have h := AvramDividend.Classical.shiftedLevy_runningSup_nonnegative L w 0 t
    have hset : Set.Icc (0 : NNReal) t = Set.Iic t := by ext s; simp
    simpa [hset, L.X_zero] using h
  have h := hConv 0 le_rfl f
  simpa only [max_eq_right (hs _ _)] using h

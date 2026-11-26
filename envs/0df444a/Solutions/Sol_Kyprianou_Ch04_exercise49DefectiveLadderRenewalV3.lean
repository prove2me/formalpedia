-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DefectiveLadderRenewalV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:08:34.997797+00:00
-- url     : https://prove2.me/submissions/0bde3cad-560b-4de0-ad08-43b02ae61bcb

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PhysicalRenewalLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RenewalLawSeriesV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Combine physical regeneration and the geometric convolution expansion. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift = triplet.drift -
      ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega)))
    (hTendsInfinity : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real -> Omega -> WithTop NNReal := fun initial omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
              initial + X t omega < 0}
        let rho : Real := (P {omega : Omega | tau 0 omega ≠ ⊤}).toReal
        0 < rho → rho < 1 →
        ∀ (finiteTime : Omega → NNReal),
          Measurable finiteTime →
          (∀ᵐ omega : Omega ∂P, tau 0 omega ≠ ⊤ →
            tau 0 omega = (finiteTime omega : WithTop NNReal)) →
          ∃ eta : Measure Real,
            IsProbabilityMeasure eta ∧
            (∀ B : Set Real, MeasurableSet B →
              (eta B).toReal =
                (P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                    -(X (finiteTime omega) omega) ∈ B}).toReal / rho) ∧
            let convPow : Nat -> Measure Real :=
              Nat.rec (Measure.dirac (0 : Real))
                (fun _ mu => mu.conv eta)
            ∀ x : Real, 0 ≤ x →
              (P {omega : Omega | tau x omega = ⊤}).toReal =
                (1 - rho) *
                  ∑' k : Nat, rho ^ k * (convPow k (Set.Iic x)).toReal := by
  dsimp only
  intro h0 h1 f hf he
  obtain ⟨eta, hEta, hDeficit, mu, hMu, hSurvival, hLaw⟩ :=
    Kyprianou.Ch04.exercise49PhysicalRenewalLawV1
      P X hLevy triplet hTriplet hBV drift hDrift hd hNotSubordinator
      hTendsInfinity h0 h1 f hf he
  letI : IsProbabilityMeasure eta := hEta
  letI : IsProbabilityMeasure mu := hMu
  refine ⟨eta, hEta, hDeficit, ?_⟩
  intro x hx
  rw [hSurvival x hx]
  exact Kyprianou.Ch04.exercise49RenewalLawSeriesV1
    _ h0.le h1 mu eta hLaw (Set.Iic x) measurableSet_Iic

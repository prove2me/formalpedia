-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RhoPositiveV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:08.476087+00:00
-- url     : https://prove2.me/submissions/3e163543-705a-4709-ba45-5fccac9c7a51

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A zero ruin probability forces all marginals nonnegative, hence monotone paths. -/
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
        0 < rho := by
  dsimp only
  by_contra hn
  have hz : (P {omega : Omega |
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ 0 + X t omega < 0} ≠ ⊤}).toReal = 0 :=
    le_antisymm (le_of_not_gt hn) ENNReal.toReal_nonneg
  have hnull : P {omega : Omega |
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ 0 + X t omega < 0} ≠ ⊤} = 0 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _), hz, ENNReal.ofReal_zero]
  apply hNotSubordinator
  apply Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P X hLevy
  intro t
  have hgood : ∀ᵐ omega ∂P,
      sInf {v : WithTop NNReal | ∃ s : NNReal,
        v = ↑s ∧ 0 < s ∧ 0 + X s omega < 0} = ⊤ := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hgood] with omega hw
  by_contra! hneg
  have ht : 0 < t := by
    by_contra! h
    have he : t = 0 := le_antisymm h bot_le
    rw [he, congrFun hLevy.start_zero omega] at hneg
    exact (lt_irrefl 0) hneg
  have hle : (sInf {v : WithTop NNReal | ∃ s : NNReal,
      v = ↑s ∧ 0 < s ∧ 0 + X s omega < 0}) ≤ ↑t :=
    sInf_le ⟨t, rfl, ht, by simpa only [zero_add] using hneg⟩
  rw [hw] at hle
  exact WithTop.coe_ne_top (top_le_iff.mp hle)

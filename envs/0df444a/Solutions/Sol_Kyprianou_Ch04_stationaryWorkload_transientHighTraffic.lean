-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkload_transientHighTraffic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:42:29.245525+00:00
-- url     : https://prove2.me/submissions/aad1135f-7608-4170-a3b1-a30bd0a0793d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_overloadedInput_tendsto_atBot
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    (1 < rho →
      ∀ w : Real, 0 ≤ w →
        let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        ∀ᵐ omega : Omega ∂P,
          Tendsto (fun t : NNReal => W t omega) atTop atTop) := by
  dsimp only
  intro hRho w hw
  filter_upwards [Kyprianou.Ch04.overloadedInput_tendsto_atBot P F L hBV hd hRho] with omega hlim
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [tendsto_atBot.1 hlim (w - b)] with t ht
  have hmax := le_max_left w (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t))
  linarith

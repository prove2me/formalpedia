-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleTimeTrafficRegimesV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:03:59.050055+00:00
-- url     : https://prove2.me/submissions/f7401d60-6729-4be4-a0e2-cc13f97d5808
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTraffic_supercriticalFiniteIdle
import Theorems.Thm_Kyprianou_Ch04_totalIdleTraffic_nonSupercriticalInfiniteIdle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Theorem 4.1 (p. 89), using the normalised positive-density coefficient d*Phi(0). -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    let totalIdle : Omega → ENNReal := fun omega =>
      ∫⁻ t in Set.Ici (0 : Real),
        (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (rho > 1 →
      ∃ phi : Real,
        0 < phi ∧ L.ψ phi = 0 ∧
        (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
        (P {omega : Omega | totalIdle omega = 0}).toReal =
          1 - Real.exp (-phi * w) ∧
        (∀ x : Real, 0 ≤ x →
          (P {omega : Omega |
            0 < totalIdle omega ∧
            totalIdle omega ≤ ENNReal.ofReal x}).toReal =
              Real.exp (-phi * w) *
                (1 - Real.exp (-phi * L.drift * x)))) ∧
    (rho ≤ 1 →
      (P {omega : Omega | totalIdle omega = ⊤}).toReal = 1) := by
  exact ⟨
    Kyprianou.Ch04.totalIdleTraffic_supercriticalFiniteIdle P F L hBV hd w hw,
    Kyprianou.Ch04.totalIdleTraffic_nonSupercriticalInfiniteIdle P F L hBV hd w hw
  ⟩

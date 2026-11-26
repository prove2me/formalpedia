-- Prove2me | solution 1 for Kyprianou.Ch04.overloadedInput_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:29.193668+00:00
-- url     : https://prove2.me/submissions/1e2c25a3-e9b0-43e7-8077-9d87fd3f9ada

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficPsiSignV1
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_Kyprianou_Ch04_negativeExponentIntegerDivergence
import Theorems.Thm_Kyprianou_Ch04_boundedVariationIntegerDivergenceExtends
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hRho : 1 < (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift) :
    ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => L.X t omega) atTop atBot := by
  have hs := Kyprianou.Ch04.totalIdleTrafficPsiSignV1 P F L hBV hd
  have hn : ¬ ∀ theta : Real, 0 ≤ theta → 0 ≤ L.ψ theta :=
    fun h => (not_le_of_gt hRho) (hs.mpr h)
  push_neg at hn
  obtain ⟨theta, htheta, hpsi⟩ := hn
  have hp : 0 < theta := by
    by_contra h
    have he : theta = 0 := le_antisymm (le_of_not_gt h) htheta
    subst theta
    have hz : L.ψ 0 = 0 := by simp [SpectrallyNegativeLevy.ψ, laplaceExponent]
    linarith
  filter_upwards [Kyprianou.Ch04.negativeExponentIntegerDivergence P F L theta hp hpsi,
    bv_drift_deficit_ae_monotone_all_times L hBV] with w hw hm
  exact Kyprianou.Ch04.boundedVariationIntegerDivergenceExtends
    (fun t => L.X t w) L.drift hd hm hw

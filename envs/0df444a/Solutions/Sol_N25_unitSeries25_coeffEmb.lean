-- Prove2me | solution 1 for N25.unitSeries25_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:50.689896+00:00
-- url     : https://prove2.me/submissions/82474ae1-36eb-4dfd-8e40-5c029b1d308b

import Mathlib
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff

set_option autoImplicit false

open ModularCurve

namespace N25

private theorem coeffEmb_intSeries (K : Type*) [Field K] [Algebra ℚ K]
    (p : PowerSeries ℤ) : coeffEmb K (intSeriesC ℚ p) = intSeriesC K p := by
  ext k
  rw [coeffEmb_coeff]
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have hn : k < 0 := lt_of_not_ge hk
    rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hn,
      ofPowerSeries_coeff_of_neg _ hn, map_zero]

/-- Coefficient extension preserves the literal unpowered unit quotient. -/
theorem _root_.solution (K : Type*) [Field K] [Algebra ℚ K] (i : Fin 5) :
    coeffEmb K (unitSeries25 ℚ i) = unitSeries25 K i := by
  simp only [unitSeries25, map_div₀, coeffEmb_intSeries]

end N25

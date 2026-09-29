-- Prove2me | solution 1 for ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d867ddb0-9761-5d16-b04e-9274f7b5a89f

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : (qInftyPlaceBar L F h).toValuationSubring) : ¬IsUnit (algebraMap L (qInftyPlaceBar L F h).toValuationSubring ((qSeriesBar L F (f : F)).coeff 0) - f) := by
  set c : L := (qSeriesBar L F (f : F)).coeff 0 with hc
  have hcoe : qSeriesBar L F
      ((algebraMap L (qInftyPlaceBar L F h).toValuationSubring c - f : _) : F)
      = HahnSeries.single (0 : ℤ) c - qSeriesBar L F (f : F) := by
    have h1 : ((algebraMap L (qInftyPlaceBar L F h).toValuationSubring c - f : _) : F)
        = algebraMap L F c - (f : F) := by
      push_cast
      rw [Place.coe_algebraMap]
    rw [h1, qSeriesBar_sub, qSeriesBar_algebraMap]
  have hgcoeff : ∀ k : ℤ, k ≤ 0 →
      (qSeriesBar L F
        ((algebraMap L (qInftyPlaceBar L F h).toValuationSubring c - f : _) : F)).coeff k
        = 0 := by
    intro k hk
    rw [hcoe, HahnSeries.coeff_sub]
    rcases lt_or_eq_of_le hk with hk' | hk'
    · rw [HahnSeries.coeff_single_of_ne (by omega : k ≠ 0),
        HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk' f.2), sub_zero]
    · subst hk'
      rw [HahnSeries.coeff_single_same, hc, sub_self]
  intro hunit
  rcases eq_or_ne
    (((algebraMap L (qInftyPlaceBar L F h).toValuationSubring c - f : _) : F)) 0
    with hg0 | hg0
  · have hzero : (algebraMap L (qInftyPlaceBar L F h).toValuationSubring c - f : _) = 0 :=
      Subtype.ext hg0
    rw [hzero] at hunit
    exact not_isUnit_zero hunit
  · have horder := (isUnit_qIntegersBar_iff hg0).mp hunit
    have hne := HahnSeries.coeff_order_eq_zero.not.mpr (qSeriesBar_ne_zero hg0)
    rw [horder] at hne
    exact hne (hgcoeff 0 le_rfl)

end S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar
end P2MW
export P2MW.S_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar (solution)

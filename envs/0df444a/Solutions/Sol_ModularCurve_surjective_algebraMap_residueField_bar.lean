-- Prove2me | solution 1 for ModularCurve.surjective_algebraMap_residueField_bar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8248b77a-26c5-55e5-a419-140da8a187c5

import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_surjective_algebraMap_residueField_bar

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Function.Surjective (algebraMap L (qInftyPlaceBar L F h).ResidueField) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring) y
  refine ⟨(qSeriesBar L F (f : F)).coeff 0, ?_⟩
  have hmem : algebraMap L (qInftyPlaceBar L F h).toValuationSubring
      ((qSeriesBar L F (f : F)).coeff 0) - f ∈
      IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar L h f
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := IsLocalRing.maximalIdeal (qInftyPlaceBar L F h).toValuationSubring)
    (algebraMap L (qInftyPlaceBar L F h).toValuationSubring
      ((qSeriesBar L F (f : F)).coeff 0)) f).mpr hmem

end S_ModularCurve_surjective_algebraMap_residueField_bar
end P2MW
export P2MW.S_ModularCurve_surjective_algebraMap_residueField_bar (solution)

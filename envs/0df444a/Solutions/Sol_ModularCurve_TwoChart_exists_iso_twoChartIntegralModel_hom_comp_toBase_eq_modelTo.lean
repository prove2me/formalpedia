-- Prove2me | solution 1 for ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9fdb6e58-25f0-52e3-be9d-2030bd85181f

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)] :
    ∃ e : ModularCurve.TwoChartModel A K j ≅ AlgebraicCurve.TwoChartIntegralModel A K j,
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A K j = ModularCurve.TwoChart.modelTo A K j ∧
      ModularCurve.TwoChart.ιFin A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin A K j ∧
      ModularCurve.TwoChart.ιInf A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf A K j :=
  ⟨Iso.refl _, Category.id_comp _, Category.comp_id _, Category.comp_id _⟩

#print axioms solution

end S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
end P2MW
export P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo (solution)

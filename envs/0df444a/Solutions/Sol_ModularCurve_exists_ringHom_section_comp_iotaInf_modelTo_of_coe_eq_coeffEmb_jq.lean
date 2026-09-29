-- Prove2me | solution 1 for ModularCurve.exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a4eec57a-c5c7-531e-ac2f-c536ec80bcb4

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq
p2m_attr_erase "simp" "ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem solution
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
      (ε : Spec (CommRingCat.of A) ⟶ ModularCurve.TwoChartModel A (↥K) j),
      (∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a) ∧
      ψ (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = 0 ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0) ∧
      ε = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιInf A (↥K) j ∧
      ε ≫ ModularCurve.TwoChart.modelTo A (↥K) j = 𝟙 _ ∧
      (∀ y : ↥(Spec (CommRingCat.of A)), ε.base y ∉ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) := by
  obtain ⟨ψ, hψA, -, hψc, hψ0⟩ :=
    ModularCurve.exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq L K A j hj
  refine ⟨ψ, _, hψA, hψ0, hψc, rfl, ?_, ?_⟩
  · have hcomp : ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) = RingHom.id A := RingHom.ext hψA
    rw [Category.assoc, ModularCurve.TwoChart.ιInf_modelTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
      CommRingCat.ofHom_id, Spec.map_id]
  · intro y hy
    rw [Scheme.Hom.comp_apply] at hy
    have h := (AlgebraicCurve.TwoChartIntegralModel.iotaInf_mem_range_iotaFin_iff A (↥K) j
      ((Spec.map (CommRingCat.ofHom ψ)).base y)).mp hy
    apply h
    show ModularCurve.TwoChart.jInvChartInf A (↥K) j ∈ (y.asIdeal.comap ψ)
    rw [Ideal.mem_comap, hψ0]
    exact y.asIdeal.zero_mem

#print axioms solution

end S_ModularCurve_exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq (solution)

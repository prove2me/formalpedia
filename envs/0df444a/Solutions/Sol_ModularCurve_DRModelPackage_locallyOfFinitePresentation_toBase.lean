-- Prove2me | solution 1 for ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/65d2f2c3-4882-5e14-831c-69c282ab8346

import Mathlib
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    LocallyOfFinitePresentation (DRModel.toBase p) := by

  have hFin : Algebra.FiniteType ℤ
      ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
    letI := (TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    haveI : IsScalarTower ℤ (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        ((TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).commutes r).symm
    haveI : Module.Finite (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := 𝔛.chartFin_finite
    exact Algebra.FiniteType.trans (S := Polynomial ℤ) inferInstance inferInstance
  have hInf : Algebra.FiniteType ℤ
      ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
    letI := (TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    haveI : IsScalarTower ℤ (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        ((TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).commutes r).symm
    haveI : Module.Finite (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := 𝔛.chartInf_finite
    exact Algebra.FiniteType.trans (S := Polynomial ℤ) inferInstance inferInstance
  haveI := hFin; haveI := hInf
  exact AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase ℤ ↥(modularFunctionFieldFull p)
    (IgusaScheme.jFull p)

end S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase (solution)

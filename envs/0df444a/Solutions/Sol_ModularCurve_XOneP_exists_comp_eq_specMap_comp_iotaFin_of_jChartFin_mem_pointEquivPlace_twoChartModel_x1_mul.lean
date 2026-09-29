-- Prove2me | solution 1 for ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8c5dd7da-56e9-5707-8e06-523c80b7d3f8

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _})
    (hjx : (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (ModularCurve.TwoChart.jChartFin A (↥K) j)))))) ∈ (Mη.pointEquivPlace x).toValuationSubring) :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ,
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
  classical

  let Φ : Mη.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))
  let x₀ : closedPoints Mη.C := pointEquivClosedPoint Mη.toBase x

  have hmem : Φ.base x₀.1 ∈ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base :=
    AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
      A (↥K) j Mη Φ (hMne := Mη_chart_nonempty) x₀ hjx

  have hrange : Set.range (x.1 ≫ Φ).base ⊆ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base := by
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint (AlgebraicClosure ℚ) := Subsingleton.elim _ _
    rw [ht]
    exact hmem
  let g' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ ModularCurve.TwoChart.XFin A (↥K) j :=
    IsOpenImmersion.lift (ModularCurve.TwoChart.ιFin A (↥K) j) (x.1 ≫ Φ) hrange
  have hfac : g' ≫ ModularCurve.TwoChart.ιFin A (↥K) j = x.1 ≫ Φ := IsOpenImmersion.lift_fac _ _ _

  refine ⟨(Spec.fullyFaithful.preimage g').unop.hom, ?_⟩
  change x.1 ≫ Φ = _
  rw [← hfac, CommRingCat.ofHom_hom]
  congr 1
  exact (Spec.fullyFaithful.map_preimage g').symm

end S_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul (solution)

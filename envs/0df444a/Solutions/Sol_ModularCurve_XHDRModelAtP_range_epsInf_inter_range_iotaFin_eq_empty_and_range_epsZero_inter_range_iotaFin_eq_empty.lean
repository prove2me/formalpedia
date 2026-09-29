-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/df9ecb28-d137-5182-aaba-88503989018c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

p2m_open_scoped "MatrixGroups Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 3200000

namespace CuspsOffFinH

open AlgebraicCurve.TwoChartIntegralModel

theorem coeff_zero_jInv_eq_zero (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (((jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ).coeff 0 = 0 := by
  have hcoe : (((jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = jq⁻¹ := by
    show (((jAt Γ hj)⁻¹ : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = jq⁻¹
    rw [IntermediateField.coe_inv]
    rfl
  rw [hcoe]
  have hjq : (jq : LaurentSeries ℚ) ≠ 0 := jq_ne_zero
  have hinv : (jq⁻¹ : LaurentSeries ℚ) ≠ 0 := inv_ne_zero hjq
  have hord : (jq⁻¹ : LaurentSeries ℚ).order = 1 := by
    have h := HahnSeries.order_mul_of_ne_zero (x := jq) (y := jq⁻¹)
      (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hjq) (HahnSeries.leadingCoeff_ne_zero.mpr hinv))
    rw [mul_inv_cancel₀ hjq, HahnSeries.order_one, order_jq] at h
    omega
  exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; decide)

theorem jInv_not_mem_of_ιInf_mem_range_ιFin (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (x : ↥(XInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))
    (hx : (ιInf p Γ hj).base x ∈ Set.range (ιFin p Γ hj).base) :
    jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ∉ x.asIdeal := by
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨u, -, hu⟩ := (TwoChartsAux.ιFin_eq_ιInf_iff (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) x₀ x).1 hx₀
  have hmem : x ∈ Set.range (fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).base := ⟨u, hu⟩
  rw [TwoChartsAux.range_fInf] at hmem
  exact hmem

end CuspsOffFinH

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (hwfin : 𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange) :
    Set.range 𝔛.εinf.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base = ∅ ∧
    Set.range 𝔛.εzero.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base = ∅ := by

  have hinf : ∀ y : ↥(Spec (CommRingCat.of (R p))), 𝔛.εinf.1.base y ∉ Set.range (ιFin p (ΓM M H) hj).base := by
    intro y hy
    rw [𝔛.εinf_chart, Scheme.Hom.comp_apply] at hy
    apply CuspsOffFinH.jInv_not_mem_of_ιInf_mem_range_ιFin p (ΓM M H) hj _ hy

    have h0 : 𝔛.rhoInf (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) = 0 := by
      have h := 𝔛.rhoInf_spec (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      rw [CuspsOffFinH.coeff_zero_jInv_eq_zero] at h
      exact_mod_cast h
    show 𝔛.rhoInf.toRingHom _ ∈ y.asIdeal
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0]
    exact y.asIdeal.zero_mem
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨y, rfl⟩
    exact hinf y
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨y, rfl⟩ hz

    apply hinf y
    have hw : 𝔛.w.hom.base (𝔛.εinf.1.base y) = 𝔛.εzero.1.base y := by
      rw [← Scheme.Hom.comp_apply, 𝔛.w_sections]
    have hmem : 𝔛.εinf.1.base y ∈ 𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange := by
      show 𝔛.w.hom.base (𝔛.εinf.1.base y) ∈ ((ιFin p (ΓM M H) hj).opensRange : Set _)
      rw [hw]
      exact hz
    rw [hwfin] at hmem
    exact hmem

end S_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty (solution)

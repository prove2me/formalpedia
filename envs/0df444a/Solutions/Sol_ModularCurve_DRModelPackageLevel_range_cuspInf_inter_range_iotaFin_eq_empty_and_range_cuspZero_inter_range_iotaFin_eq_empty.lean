-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e0e50e8e-1ba7-53df-b015-92acf7b19fd3

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

namespace CuspOffChartAux

theorem coeff_zero_jInv_eq_zero (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    (((jInvChartInf N ℓ : ↥(chartAlgInf N ℓ)) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 = 0 := by
  have hcoe : (((jInvChartInf N ℓ : ↥(chartAlgInf N ℓ)) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = jq⁻¹ := by
    show (((jFull N)⁻¹ : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = jq⁻¹
    rw [IntermediateField.coe_inv]
    rfl
  rw [hcoe]
  have hjq : (jq : LaurentSeries ℚ) ≠ 0 := by
    intro h
    have h' := order_jq
    rw [h, HahnSeries.order_zero] at h'
    exact absurd h' (by decide)
  have hinv : (jq⁻¹ : LaurentSeries ℚ) ≠ 0 := inv_ne_zero hjq
  have hord : (jq⁻¹ : LaurentSeries ℚ).order = 1 := by
    have h := HahnSeries.order_mul_of_ne_zero (x := jq) (y := jq⁻¹)
      (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hjq) (HahnSeries.leadingCoeff_ne_zero.mpr hinv))
    rw [mul_inv_cancel₀ hjq, HahnSeries.order_one, order_jq] at h
    omega
  exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; decide)

end CuspOffChartAux

open CuspOffChartAux in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    Set.range 𝔓.εinf.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅ ∧
    Set.range 𝔓.εzero.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅ := by

  have hinf : ∀ y : ↥(Spec (CommRingCat.of (R q))), 𝔓.εinf.1.base y ∉ Set.range (IgusaScheme.ιFin (N₀ * q) q).base := by
    intro y hy
    rw [𝔓.εinf_chart] at hy

    set x := (Spec.map (CommRingCat.ofHom 𝔓.rhoInf.toRingHom)).base y with hx
    have hmem : x ∈ ιInf (N₀ * q) q ⁻¹ᵁ chartFinOpen (N₀ * q) q := by
      show (ιInf (N₀ * q) q).base x ∈ (chartFinOpen (N₀ * q) q : Set (ModularCurve.IgusaScheme (N₀ * q) q))
      exact hy
    rw [(iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N₀ * q) q).1] at hmem

    apply hmem
    show jInvChartInf (N₀ * q) q ∈ x.asIdeal
    have h0 : 𝔓.rhoInf (jInvChartInf (N₀ * q) q) = 0 := by
      have h := 𝔓.rhoInf_spec (jInvChartInf (N₀ * q) q)
      rw [coeff_zero_jInv_eq_zero] at h
      exact_mod_cast h
    show 𝔓.rhoInf.toRingHom (jInvChartInf (N₀ * q) q) ∈ y.asIdeal
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0]
    exact y.asIdeal.zero_mem
  refine ⟨?_, ?_⟩
  · ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨y, rfl⟩
    exact hinf y
  · ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨y, rfl⟩ ⟨z, hz⟩

    apply hinf y
    have hwz : (𝔓.w.hom).base (𝔓.εzero.1.base y) = 𝔓.εinf.1.base y := by
      rw [← 𝔓.w_sections]
      show ((𝔓.εinf.1 ≫ 𝔓.w.hom) ≫ 𝔓.w.hom).base y = _
      rw [Category.assoc, 𝔓.w_invol, Category.comp_id]
    rw [← hwz, ← hz]
    refine ⟨(Spec.map (CommRingCat.ofHom 𝔓.theta.toRingEquiv.toRingHom)).base z, ?_⟩
    show ((Spec.map (CommRingCat.ofHom 𝔓.theta.toRingEquiv.toRingHom)) ≫ IgusaScheme.ιFin (N₀ * q) q).base z =
      (IgusaScheme.ιFin (N₀ * q) q ≫ 𝔓.w.hom).base z
    rw [𝔓.w_chart]

end S_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty (solution)

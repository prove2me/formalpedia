-- Prove2me | solution 1 for N25.U25_geometric_ord_eq_zero_of_not_selected
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:03.846671+00:00
-- url     : https://prove2.me/submissions/cf8e8baa-10e4-4ca0-b51d-1f1dd54593f9

import Mathlib
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_cusp_constant_place_lift
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_N25_cusp_complex_endpoints
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_N25_cusp_complex_endpoint_exhausts_poles
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Theorems.Thm_N25_Endgame_simple_cusp_geometric_selected25
import Theorems.Thm_N25_unitSeries25_coeffEmb
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_N25_U25_complex_endpoint_ord_zero
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_U25_geometric_ord_eq_zero_of_not_isCusp
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve N25.Endgame

open scoped MatrixGroups

namespace N25

private theorem mem_of_order_nonnegative {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P : Place K F) (x : F) (hn : 0 ≤ P.ord x) : x ∈ P.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hx hπ
  rw [hu, show P.ord x = ((P.ord x).toNat : ℤ) from (Int.toNat_of_nonneg hn).symm,
    zpow_natCast]
  exact mul_mem (u : P.toValuationSubring).2 (pow_mem (π : P.toValuationSubring).2 _)

/-- All geometric places outside the five specified cusps have zero unit order. -/
theorem _root_.solution (i : Fin 5) (P : GPlace)
    (hP : ∀ j : Fin 5, P ≠ pG25 j) : P.ord (emb25 (U25 i)) = 0 := by
  by_cases hcusp : ModularCurve.IsCusp (emb25 j25) P
  · have hpneg : P.ord (emb25 j25) < 0 := by
      apply lt_of_not_ge
      intro hn
      exact hcusp (mem_of_order_nonnegative P (emb25 j25) hn)
    let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
    let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
    obtain ⟨κ, hκ, hlift⟩ := N25.cusp_constant_place_lift ι.toRingHom
    obtain ⟨W, hmemW, hord, _⟩ := hlift P
    have hcomp : ι.toRingHom.comp (algebraMap ℚ Qbar) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
    have hu : (κ (emb25 (U25 i)) : LaurentSeries ℂ) = unitSeries25 ℂ i := by
      rw [hκ, coe_emb25, show (U25 i).1 = unitSeries25 ℚ i from coe_U25C ℚ i]
      change coeffMap ι.toRingHom (coeffMap (algebraMap ℚ Qbar) (unitSeries25 ℚ i)) = _
      rw [coeffMap_coeffMap, hcomp]
      exact unitSeries25_coeffEmb ℂ i
    have hj : (κ (emb25 j25) : LaurentSeries ℂ) = jqModC ℂ := by
      rw [hκ, coe_emb25]
      change ((jqModC ℚ).map (algebraMap ℚ Qbar)).map ι.toRingHom = _
      rw [map_jqModC, map_jqModC]
    obtain ⟨jC, endpoint, hjC, hwidth, hmem, hlead⟩ := N25.cusp_complex_endpoints
    have heqj : jC = κ (emb25 j25) := Subtype.ext (hjC.trans hj.symm)
    subst jC
    have hWneg : W.ord (κ (emb25 j25)) < 0 := by rw [hord]; exact hpneg
    obtain ⟨B, hB⟩ := N25.cusp_complex_endpoint_exhausts_poles endpoint hmem
      (κ (emb25 j25)) hj W hWneg
    have hB25 : ¬ (25 : ℤ) ∣ B 1 0 := by
      intro hd
      have hz : (B 1 0 : ZMod 25) = 0 := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      have hc : (B 1 0 : ZMod 25).val = 0 := by rw [hz]; rfl
      have ho := hwidth B
      simp only [hc, ↓reduceIte, Nat.cast_one] at ho
      rw [hB, hord] at ho
      obtain ⟨j, hj⟩ := simple_cusp_geometric_selected25 P ho
      exact hP j hj
    let width : ℕ := if (B 1 0 : ZMod 25).val = 0 then 1
      else if (B 1 0 : ZMod 25).val % 5 = 0 then 5 else 25
    have hw : 0 < width := by dsimp only [width]; split_ifs <;> norm_num
    rw [← hord (emb25 (U25 i)), ← hB]
    exact U25_complex_endpoint_ord_zero i (κ (emb25 (U25 i))) hu (endpoint B)
      B hB25 width hw (hlead B)
  · exact U25_geometric_ord_eq_zero_of_not_isCusp i P hcusp

end N25

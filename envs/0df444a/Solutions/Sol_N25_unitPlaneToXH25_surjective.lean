-- Prove2me | solution 1 for N25.unitPlaneToXH25_surjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:10:26.097198+00:00
-- url     : https://prove2.me/submissions/5e66379e-7ca3-4a0e-815c-8ba98d893f45

import Mathlib
import Definitions.Def_N25_UnitPlaneModularMap
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitRelation25_qExpansion_certificate
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
import Definitions.Def_N25_UnitPlaneFunctionCoordinates
import Definitions.Def_N25_UnitPlaneFieldPointLift
import Theorems.Thm_N25_xH25_eq_adjoin_units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_N25_U25_zero_transcendental
import Theorems.Thm_N25_unitPlaneToXH25_coordinates

/-! The specified modular units generate the image of the plane function field. -/
namespace N25

/-- Generation by the two specified units makes their plane evaluation surjective. -/
theorem _root_.solution :
    Function.Surjective (unitPlaneFieldPointLift25 (U25 0) (U25 0 / U25 1)
      (unitRelation25_qExpansion_certificate ℚ) U25_zero_transcendental) := by
  let φ : UnitPlaneFF25 →ₐ[ℚ] N25.Endgame.FQ :=
    unitPlaneFieldPointLift25 (U25 0) (U25 0 / U25 1)
      (unitRelation25_qExpansion_certificate ℚ) U25_zero_transcendental
  change Function.Surjective φ
  let L : IntermediateField ℚ N25.Endgame.FQ :=
    { φ.toRingHom.fieldRange with
      algebraMap_mem' := fun a => ⟨algebraMap ℚ UnitPlaneFF25 a, φ.commutes a⟩ }
  have hgen : IntermediateField.adjoin ℚ
      ({U25 0, U25 0 / U25 1} : Set N25.Endgame.FQ) ≤ L := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨unitPlaneFunctionU25, unitPlaneToXH25_coordinates.1⟩
    · have hy' : y = U25 0 / U25 1 := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨unitPlaneFunctionV25, unitPlaneToXH25_coordinates.2⟩
  rw [xH25_eq_adjoin_units] at hgen
  intro y
  exact hgen (show y ∈ (⊤ : IntermediateField ℚ N25.Endgame.FQ) from trivial)

end N25

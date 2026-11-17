-- Prove2me | solution 1 for N25.cuspArithmeticCensus
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:00.4812+00:00
-- url     : https://prove2.me/submissions/a676096f-0464-4e1a-8627-71e10f27cd90

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_cusp_middle_closed_degree_lower_bound
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_not_mem_iff_ord_neg
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_N25_fricke_closed_cusp_degree_lower_bound
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
import Theorems.Thm_N25_cuspArithmeticCensus_of_degree_bounds
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension

set_option autoImplicit false

open ModularCurve AlgebraicCurve N25.Endgame

open scoped MatrixGroups

namespace N25

/-- The closed cusp degrees are five ones, four and five; there are fourteen geometric cusps. -/
theorem _root_.solution :
    ∃ P4 P5 : QPlace, P4.deg = 4 ∧ P5.deg = 5 ∧
      P4.ord j25 = -5 ∧ P5.ord j25 = -25 ∧
      (∀ P : QPlace, ModularCurve.IsCusp j25 P ↔
        (∃ i : Fin 5, P = pQ25 i) ∨ P = P4 ∨ P = P5) ∧
      Nat.card {G : GPlace // G.ord (emb25 j25) < 0} = 14 := by
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let W : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : ℝ), -1; 25, 0] (by norm_num [Matrix.det_fin_two])
  obtain ⟨P4, hc4, ho4, hl4⟩ := cusp_middle_closed_degree_lower_bound ι.toRingHom
  obtain ⟨P5, hc5, ho5, hl5⟩ := fricke_closed_cusp_degree_lower_bound ι.toRingHom W rfl
  obtain ⟨hg, _, hd4, hd5, hclass⟩ :=
    cuspArithmeticCensus_of_degree_bounds P4 P5 hc4 hc5 ho4 ho5 hl4 hl5
  refine ⟨P4, P5, hd4, hd5, ho4, ho5, hclass, ?_⟩
  let e : {G : GPlace // IsCusp (emb25 j25) G} ≃
      {G : GPlace // G.ord (emb25 j25) < 0} :=
    Equiv.subtypeEquivRight (fun G => G.not_mem_iff_ord_neg _)
  exact (Nat.card_congr e).symm.trans hg

end N25

-- Prove2me | solution 1 for N25.nonempty_K2Rows
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:01.815404+00:00
-- url     : https://prove2.me/submissions/83687cac-d85d-43db-bfa5-6a0dfbb0b576

import Mathlib
import Definitions.Def_N25_CuspidalSubgroup
import Theorems.Thm_N25_Endgame_coe_d25
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_addOrderOf_d25
import Theorems.Thm_N25_Endgame_cusp_difference_killed25
import Definitions.Def_N25_PointDifference
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
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
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_N25_Endgame_cusp_coefficient_six25
import Theorems.Thm_N25_cuspDiamondEigenvalue
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Theorems.Thm_N25_frickeCuspCharacter_psi
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_CharacterField
import Theorems.Thm_N25_exists_K2Rows
import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_N25_GlobalKummer
import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_cyclotomic_gamma
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace N25

open AlgebraicCurve Endgame

/-- The selected cusp and its Fricke image supply the exact kernel sequence. -/
theorem _root_.solution : Nonempty K2Rows := by
  let c : J := pointDiff (pG25 0) (pG25 1) ((pG25_degree 0).trans (pG25_degree 1).symm)
  have hne : c ≠ 0 := by
    intro h
    have hd : d25 = 0 := Subtype.ext (coe_d25.trans h)
    have ho := addOrderOf_d25
    rw [hd, addOrderOf_zero] at ho
    norm_num at ho
  have hk : (71 : ℕ) • c = 0 := cusp_difference_killed25 0 1
  have hkz : (71 : ℤ) • c = 0 := by exact_mod_cast hk
  have hc : gamma c = (5 : ℕ) • c := by
    exact_mod_cast (cuspDiamondEigenvalue cusp_coefficient_six25 hkz).1
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let W : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : ℝ), -1; 25, 0] (by norm_num [Matrix.det_fin_two])
  obtain ⟨w, _, hw, hgal, _, _, _⟩ :=
    frickeCuspCharacter_psi ι.toRingHom W rfl cusp_coefficient_six25 hkz hne
  have ha : SemilinearAut.ofAlgAut w • c ≠ 0 := by
    intro h
    exact hne ((smul_eq_zero_iff_eq _).mp h)
  have hak : (71 : ℕ) • (SemilinearAut.ofAlgAut w • c) = 0 := by
    change (71 : ℕ) • (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w)) c = 0
    rw [← map_nsmul, hk, map_zero]
  have hag : gamma (SemilinearAut.ofAlgAut w • c) =
      (57 : ℕ) • (SemilinearAut.ofAlgAut w • c) := by exact_mod_cast hw
  exact exists_K2Rows cyclotomic_gamma c (SemilinearAut.ofAlgAut w • c)
    hne hk hc (fun σ => by
      have h := d25.property σ
      rw [coe_d25] at h
      exact h) ha hak hag hgal

end N25

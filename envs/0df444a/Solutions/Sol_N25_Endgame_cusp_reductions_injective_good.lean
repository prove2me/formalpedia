-- Prove2me | solution 1 for N25.Endgame.cusp_reductions_injective_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:11.238413+00:00
-- url     : https://prove2.me/submissions/90350e27-b791-4c78-a1e0-793c59fde25e

import Mathlib
import Theorems.Thm_N25_Endgame_cusp_difference_killed25
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
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
import Theorems.Thm_N25_Endgame_pointDiff_eq_zero_iff_generic25
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
import Theorems.Thm_N25_Endgame_red_pointDiff25
import Theorems.Thm_N25_Endgame_eq_zero_of_red25_eq_zero
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace N25.Endgame

/-- The five rational cusps have distinct reductions in characteristics two and three. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (D : RedDatum25 p) :
    Function.Injective (fun i : Fin 5 => redPlace25 D (pG25 i)) := by
  have hp25 : ¬ p ∣ 25 := by
    rcases hp with rfl | rfl <;> norm_num
  have hp71 : ¬ p ∣ 71 := by
    rcases hp with rfl | rfl <;> norm_num
  intro i j hij
  have hred : red25 D (pointDiff (pG25 i) (pG25 j)
      ((pG25_degree i).trans (pG25_degree j).symm)) = 0 := by
    rw [red_pointDiff25]
    simp only [hij, pointDiff, sub_self]
    exact AlgebraicCurve.Pic0.mk_zero
  have hzero := eq_zero_of_red25_eq_zero hp25 D 71 hp71
    (pointDiff (pG25 i) (pG25 j)
      ((pG25_degree i).trans (pG25_degree j).symm))
    (cusp_difference_killed25 i j) hred
  exact cuspChoice25_spec.2.2.1
    ((pointDiff_eq_zero_iff_generic25 (pG25 i) (pG25 j)
      (pG25_degree i) (pG25_degree j)).mp hzero)

end N25.Endgame

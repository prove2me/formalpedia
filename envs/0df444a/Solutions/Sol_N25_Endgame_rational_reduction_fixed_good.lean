-- Prove2me | solution 1 for N25.Endgame.rational_reduction_fixed_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:33:06.648584+00:00
-- url     : https://prove2.me/submissions/36676fe8-ea13-4ccd-9d9b-fa50fa6e87c3

import Mathlib
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_cusp_zero_reduction_fixed_good
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_Endgame_pG25_rational
import Theorems.Thm_N25_Endgame_pointDiff_mem_M
import Theorems.Thm_N25_Endgame_red_mem_fixed25
import Definitions.Def_N25_Endgame
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
import Theorems.Thm_N25_Endgame_red_pointDiff25
import Theorems.Thm_N25_Endgame_redPlace25_degree
import Theorems.Thm_N25_Endgame_qExpFrobeniusPushforward25_mk
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_N25_Endgame_frobenius_pushforward_single_of_deg_one
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_N25_Endgame_xH25C_essFiniteType
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_xH25C_constantsAreBase
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_N25_genus_four
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicCurve

namespace N25.Endgame

private theorem special_pointDiff_zero
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 25) (D : RedDatum25 p)
    (P Q : SpecialPlace D.A) (hP : P.deg = 1) (hQ : Q.deg = 1)
    (hz : pointDiff P Q (hP.trans hQ.symm) = 0) : P = Q := by
  dsimp only [SpecialPlace, SpecialPic, FSpecial, FBase,
    ModularCurve.xHFunctionFieldC, FBaseAlgebra25] at *
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  let : IsCurveOver (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    xH25C_isCurveOver (κ D.A)
  let : Algebra.EssFiniteType (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    xH25C_essFiniteType (κ D.A)
  let : HasCanonicalDivisor (K := κ D.A) (F := ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    hasCanonicalDivisor_of_isCurveOver
  let : ∀ v : Place (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let : Γ25.FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH 25 N25.H25)
  obtain ⟨x, _, hx, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (κ D.A) Γ25 (ModularCurve.translation_mem_GammaH 25 N25.H25)
  have hRR : FunctionFieldRiemannRoch (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfd
  have hC : ConstantsAreBase (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    xH25C_constantsAreBase (κ D.A)
  have hWDA : WeilDualityAdelic (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR
      (stichtenothGenusExists_of_isCurveOver hC)
  have hgen : genus (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) = 4 :=
    (genus_eq_genusFF hRR hWDA hC).trans
      ((ModularCurve.genusFF_gammaH_residueField_eq_of_not_dvd
        25 N25.H25 hp D.A D.hA).trans N25.genus_four)
  by_contra hne
  have hprincipal : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1) :=
    (QuotientAddGroup.eq_zero_iff _).mp hz
  have hg0 := genus_eq_zero_of_isPrincipal_single_sub_single hRR hC hne hQ hprincipal
  rw [hgen] at hg0
  norm_num at hg0

private theorem pointDiff_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P Q R : Place K F) (hP : P.deg = 1) (hQ : Q.deg = 1) (hR : R.deg = 1) :
    pointDiff P Q (hP.trans hQ.symm) + pointDiff Q R (hQ.trans hR.symm) =
      pointDiff P R (hP.trans hR.symm) := by
  unfold pointDiff
  rw [← Pic0.mk_add]
  apply congrArg Pic0.mk
  apply Subtype.ext
  change (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) +
    (Finsupp.single Q 1 - Finsupp.single R 1) = _
  abel_nf

private theorem pointDiff_eq_zero_of_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P Q R : Place K F) (hP : P.deg = 1) (hQ : Q.deg = 1) (hR : R.deg = 1)
    (h : pointDiff P R (hP.trans hR.symm) = pointDiff Q R (hQ.trans hR.symm)) :
    pointDiff P Q (hP.trans hQ.symm) = 0 := by
  have hsum : pointDiff P Q (hP.trans hQ.symm) + pointDiff Q R (hQ.trans hR.symm) =
      0 + pointDiff Q R (hQ.trans hR.symm) := by
    rw [pointDiff_add _ _ _ hP hQ hR, h, zero_add]
  exact add_right_cancel hsum

/-- A rational place has Frobenius-fixed reduction at either small good prime. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p)
    (P : GPlace) (hP : IsRationalGeomPlace P) :
    frobPlace25 D (redPlace25 D P) = redPlace25 D P := by
  dsimp only [SpecialPlace, SpecialPic, FSpecial, FBase,
    ModularCurve.xHFunctionFieldC, FBaseAlgebra25] at *
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  have hp25 : ¬ p ∣ 25 := by rcases hp with rfl | rfl <;> norm_num
  let R : Place (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) := redPlace25 D P
  let Q : Place (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) := redPlace25 D (pG25 0)
  have hR : R.deg = 1 := (redPlace25_degree D P).trans hP.1
  have hQ : Q.deg = 1 := (redPlace25_degree D (pG25 0)).trans (pG25_rational 0).1
  have hQfix : ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p Q = Q := cusp_zero_reduction_fixed_good p hp D
  have hF : (ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R).deg = 1 := by
    have h := ModularCurve.degree_qExpFrobeniusDivPushforwardModL
      (κ D.A) Γ25 p (Finsupp.single R 1)
    rw [frobenius_pushforward_single_of_deg_one (κ D.A) Γ25 p R hR,
      Divisor.degree_single, Divisor.degree_single] at h
    have hdeg : (ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R).deg = R.deg := by
      exact_mod_cast (show ((ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R).deg : ℤ) = (R.deg : ℤ) by simpa using h)
    exact hdeg.trans hR
  have hmem := red_mem_fixed25 hp25 D
    (pointDiff P (pG25 0) (hP.1.trans (pG25_rational 0).1.symm))
    (pointDiff_mem_M P (pG25 0) hP (pG25_rational 0))
  rw [red_pointDiff25] at hmem
  have hfixed : ModularCurve.qExpFrobeniusPushforwardModL (κ D.A) Γ25 p (pointDiff R Q (hR.trans hQ.symm)) =
      pointDiff R Q (hR.trans hQ.symm) := by
    exact sub_eq_zero.mp hmem
  have hfrob : ModularCurve.qExpFrobeniusPushforwardModL (κ D.A) Γ25 p (pointDiff R Q (hR.trans hQ.symm)) =
      pointDiff (ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R) Q (hF.trans hQ.symm) := by
    let E : Divisor.degZero (K := κ D.A)
        (F := ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
      ⟨Finsupp.single R 1 - Finsupp.single Q 1, by
        change Divisor.degree (Finsupp.single R 1 - Finsupp.single Q 1) = 0
        simp only [map_sub, Divisor.degree_single, one_mul]
        exact sub_eq_zero.mpr (congrArg (fun n : ℕ => (n : ℤ)) (hR.trans hQ.symm))⟩
    have hm := qExpFrobeniusPushforward25_mk p (κ D.A) E
    have he : Pic0.mk (ModularCurve.qExpFrobeniusDegZeroPushforwardModL
          (κ D.A) Γ25 p E) =
        pointDiff (ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R) Q (hF.trans hQ.symm) := by
      apply congrArg (Pic0.mk (K := κ D.A)
        (F := ModularCurve.qExpFunctionFieldC (κ D.A) Γ25))
      apply Subtype.ext
      rw [ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL]
      dsimp only [E]
      rw [map_sub, frobenius_pushforward_single_of_deg_one (κ D.A) Γ25 p R hR,
        frobenius_pushforward_single_of_deg_one (κ D.A) Γ25 p Q hQ, hQfix]
    exact hm.trans he
  have heq := hfrob.symm.trans hfixed
  apply special_pointDiff_zero p hp25 D (ModularCurve.qExpFrobeniusPlaceModL (κ D.A) Γ25 p R) R hF hR
  exact pointDiff_eq_zero_of_eq _ _ _ hF hR hQ heq

end N25.Endgame

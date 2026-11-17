-- Prove2me | solution 1 for N25.Endgame.pointDiff_eq_zero_iff_generic25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:00.911351+00:00
-- url     : https://prove2.me/submissions/45d28638-64cc-4f7e-84ec-559343ef8562

import Mathlib
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_genus_four
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_N25_GammaH25_finiteIndex
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

/-- Positive genus separates actual geometric degree-one places in Picard degree zero. -/
theorem _root_.solution
    (P Q : GPlace) (hP : P.deg = 1) (hQ : Q.deg = 1) :
    pointDiff P Q (hP.trans hQ.symm) = 0 ↔ P = Q := by
  obtain ⟨hcurve, hfinite⟩ :=
    isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField Qbar 25 N25.H25
  let : IsCurveOver Qbar FG := hcurve
  let : Algebra.EssFiniteType Qbar FG := hfinite
  let : HasCanonicalDivisor (K := Qbar) (F := FG) := hasCanonicalDivisor_of_isCurveOver
  let : ∀ v : GPlace, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let : Γ25.FiniteIndex := N25.GammaH25_finiteIndex
  obtain ⟨x, hx, hfd⟩ := JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    Qbar Γ25 (translation_mem_GammaH 25 N25.H25)
  let : FiniteDimensional (IntermediateField.adjoin Qbar ({x} : Set FG)) FG := hfd
  have hRR : FunctionFieldRiemannRoch Qbar FG :=
    @functionFieldRiemannRoch_of_isAlgClosed_of_transcendental Qbar FG _ _ _ _ x hx hfd
  have hC : ConstantsAreBase Qbar FG := constantsAreBase_of_isAlgClosed_of_transcendental (K := Qbar) (F := FG) x hx
  have hWDA : WeilDualityAdelic Qbar FG :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR
      (stichtenothGenusExists_of_isCurveOver hC)
  have hgen : genus Qbar FG = 4 := (genus_eq_genusFF hRR hWDA hC).trans N25.genus_four
  constructor
  · intro hz
    by_contra hne
    have hprincipal : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1) :=
      (QuotientAddGroup.eq_zero_iff _).mp hz
    have hg0 := genus_eq_zero_of_isPrincipal_single_sub_single hRR hC hne hQ hprincipal
    rw [hgen] at hg0
    norm_num at hg0
  · rintro rfl
    simp only [pointDiff, sub_self]
    exact Pic0.mk_zero

end N25.Endgame

-- Prove2me | solution 1 for ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e35b7e94-2177-503f-ad53-6879f6d8eed9

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_ModuliPoint
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_ord_jBar_dvd_three
import Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two
import Theorems.Thm_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg
import Theorems.Thm_ModularCurve_natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo
import Theorems.Thm_ModularCurve_natCard_ord_jBar_eq_one_eq_nuThree
import Theorems.Thm_ModularCurve_card_eq_natCard_moduliPoint_j_eq_of_EMD
import Theorems.Thm_ModularCurve_emd_holds
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "jBar modularFunctionFieldBar jq coeff_jq_neg_one dedekindPsi coeffEmb coeffEmb_coeff nuTwo nuThree cuspCount genusFormula EMD ModuliPoint ModuliPoint.j sum_ord_jBar_sub_eq_dedekindPsi deg_eq_one_modularFunctionFieldBar jCoordinate_spec_modularFunctionFieldBar sum_neg_ord_jBar_eq_dedekindPsi ord_jBar_dvd_three ord_jBar_sub_1728_dvd_two card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo natCard_ord_jBar_eq_one_eq_nuThree card_eq_natCard_moduliPoint_j_eq_of_EMD emd_holds transcendental_coeffEmb_jq isCurveOver_modularFunctionFieldBar finiteDimensional_adjoin_coeffEmb_jq_of_neZero dedekindPsi_pos"
namespace LDivDegree
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.ModularCurve AlgebraicCurve"

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

end Generic

theorem int_eq_of_pos_of_dvd_two {e : ℤ} (he : 0 < e) (hd : e ∣ 2) : e = 1 ∨ e = 2 := by
  have hle := Int.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem int_eq_of_pos_of_dvd_three {e : ℤ} (he : 0 < e) (hd : e ∣ 3) : e = 1 ∨ e = 3 := by
  have hle := Int.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact Or.inl rfl
  · exfalso; norm_num at hd
  · exact Or.inr rfl

variable (N : ℕ) [NeZero N] (m : ℕ)

local notation "ℚb" => AlgebraicClosure ℚ
local notation "𝔽" => ModularCurve.modularFunctionFieldBar N

theorem jBar_sub_algebraMap_ne_zero (c : ℚb) : jBar N - algebraMap ℚb 𝔽 c ≠ 0 := by
  intro h
  have htr := transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  apply htr
  have : (jBar N : 𝔽) = algebraMap ℚb 𝔽 c := sub_eq_zero.mp h
  show IsAlgebraic ℚb (jBar N)
  rw [this]
  exact isAlgebraic_algebraMap c

theorem jBar_ne_zero : (jBar N : 𝔽) ≠ 0 := by
  have h := jBar_sub_algebraMap_ne_zero N 0
  rwa [map_zero, sub_zero] at h

theorem ord_sub_nonneg {v : Place ℚb 𝔽} (hv : 0 ≤ v.ord (jBar N)) (c : ℚb) :
    0 ≤ v.ord (jBar N - algebraMap ℚb 𝔽 c) := by
  rw [← v.mem_iff_ord_nonneg (jBar_sub_algebraMap_ne_zero N c)]
  exact sub_mem ((v.mem_iff_ord_nonneg (jBar_ne_zero N)).mpr hv) (v.algebraMap_mem' c)

theorem ord_eq_zero_of_pos_1728 {v : Place ℚb 𝔽} (hv : 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) :
    v.ord (jBar N) = 0 := by
  have h1728 : v.ord (algebraMap ℚb 𝔽 1728) = 0 := ord_algebraMap v (by norm_num)
  have hne : (algebraMap ℚb 𝔽 1728) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚb 𝔽).injective]; norm_num
  rcases lt_trichotomy (v.ord (jBar N)) 0 with hlt | heq | hgt
  ·
    have h : v.ord (jBar N + (-(algebraMap ℚb 𝔽 1728))) = v.ord (jBar N) :=
      v.ord_add_eq_of_lt (jBar_ne_zero N) (neg_ne_zero.mpr hne) (by rw [ord_neg, h1728]; exact hlt)
    rw [← sub_eq_add_neg] at h
    omega
  · exact heq
  ·
    have h : v.ord (-(algebraMap ℚb 𝔽 1728) + jBar N) = v.ord (-(algebraMap ℚb 𝔽 1728)) :=
      v.ord_add_eq_of_lt (neg_ne_zero.mpr hne) (jBar_ne_zero N) (by rw [ord_neg, h1728]; exact hgt)
    rw [neg_add_eq_sub, ord_neg, h1728] at h
    omega

theorem ord_1728_eq_zero_of_pos {v : Place ℚb 𝔽} (hv : 0 < v.ord (jBar N)) :
    v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 0 := by
  have h1728 : v.ord (algebraMap ℚb 𝔽 1728) = 0 := ord_algebraMap v (by norm_num)
  have hne : (algebraMap ℚb 𝔽 1728) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚb 𝔽).injective]; norm_num
  have h : v.ord (-(algebraMap ℚb 𝔽 1728) + jBar N) = v.ord (-(algebraMap ℚb 𝔽 1728)) :=
    v.ord_add_eq_of_lt (neg_ne_zero.mpr hne) (jBar_ne_zero N) (by rw [ord_neg, h1728]; exact hv)
  rw [neg_add_eq_sub, ord_neg, h1728] at h
  exact h

noncomputable def recipe (v : Place ℚb 𝔽) : ℤ :=
  if v.ord (jBar N) < 0 then (m : ℤ) * v.ord (jBar N) - 1
  else (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 + 2 * (m : ℤ) * v.ord (jBar N) / 3

theorem recipe_of_neg {v : Place ℚb 𝔽} (h : v.ord (jBar N) < 0) :
    recipe N m v = (m : ℤ) * v.ord (jBar N) - 1 := if_pos h

theorem recipe_of_nonneg {v : Place ℚb 𝔽} (h : 0 ≤ v.ord (jBar N)) :
    recipe N m v = (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 + 2 * (m : ℤ) * v.ord (jBar N) / 3 :=
  if_neg (not_lt.mpr h)

theorem recipe_of_pos {v : Place ℚb 𝔽} (h : 0 < v.ord (jBar N)) :
    recipe N m v = 2 * (m : ℤ) * v.ord (jBar N) / 3 := by
  rw [recipe_of_nonneg N m h.le, ord_1728_eq_zero_of_pos N h, mul_zero, Int.zero_ediv, zero_add]

theorem recipe_of_pos_1728 {v : Place ℚb 𝔽} (h : 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) :
    recipe N m v = (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 := by
  have h0 := ord_eq_zero_of_pos_1728 N h
  rw [recipe_of_nonneg N m h0.ge, h0, mul_zero, Int.zero_ediv, add_zero]

theorem recipe_eq_zero {v : Place ℚb 𝔽} (h0 : v.ord (jBar N) = 0)
    (h1 : ¬ 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) : recipe N m v = 0 := by
  have hge := ord_sub_nonneg N h0.ge (1728 : ℚb)
  have he : v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 0 := by omega
  rw [recipe_of_nonneg N m h0.ge, h0, he]
  simp

theorem exists_weightDivisor (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)) ∧
      (∀ v, 0 ≤ v.ord (jBar N) →
        D v ≤ (m : ℤ) * v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) / 2
          + 2 * (m : ℤ) * v.ord (jBar N) / 3) ∧
      (∀ v, v.ord (jBar N) < 0 → D v ≤ (m : ℤ) * v.ord (jBar N) - 1) := by
  classical

  have hdeg : ∀ w : Place ℚb 𝔽, w.deg = 1 := deg_eq_one_modularFunctionFieldBar N

  obtain ⟨-, hfinc, hfinI⟩ := jCoordinate_spec_modularFunctionFieldBar N
  set S0 : Finset (Place ℚb 𝔽) := (hfinc 0).toFinset with hS0def
  set S1 : Finset (Place ℚb 𝔽) := (hfinc 1728).toFinset with hS1def
  set Sinf : Finset (Place ℚb 𝔽) := hfinI.toFinset with hSIdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jBar N) := fun v => by
    rw [hS0def, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, sub_zero]
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728) :=
    fun v => by rw [hS1def, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSI : ∀ v, v ∈ Sinf ↔ v.ord (jBar N) < 0 := fun v => by
    rw [hSIdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  set S := S0 ∪ S1 ∪ Sinf with hSdef
  have hS : ∀ v, v ∈ S ↔ v ∈ S0 ∨ v ∈ S1 ∨ v ∈ Sinf := fun v => by
    simp only [hSdef, Finset.mem_union, or_assoc]
  have hoff : ∀ v, v ∉ S → recipe N m v = 0 := by
    intro v hv
    rw [hS] at hv
    push Not at hv
    obtain ⟨hv0, hv1, hvI⟩ := hv
    rw [hS0] at hv0; rw [hS1] at hv1; rw [hSI] at hvI
    exact recipe_eq_zero N m (by omega) hv1
  let D : Divisor ℚb 𝔽 := Finsupp.onFinset S (recipe N m) (fun v hv => by
    by_contra h
    exact hv (hoff v h))
  have hD : ∀ v, D v = recipe N m v := fun v => Finsupp.onFinset_apply
  refine ⟨D, ?_, fun v hv => ?_, fun v hv => ?_⟩
  rotate_left
  · rw [hD, recipe_of_nonneg N m hv]
  · rw [hD, recipe_of_neg N m hv]

  have hdisj01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    rw [hS0] at hv0; rw [hS1] at hv1
    have := ord_eq_zero_of_pos_1728 N hv1
    omega
  have hdisj0I : Disjoint (S0 ∪ S1) Sinf := by
    rw [Finset.disjoint_left]
    intro v hv hvI
    rw [hSI] at hvI
    rcases Finset.mem_union.mp hv with hv0 | hv1
    · rw [hS0] at hv0; omega
    · rw [hS1] at hv1
      have := ord_eq_zero_of_pos_1728 N hv1
      omega
  have hdegsum : D.degree = ∑ v ∈ S, recipe N m v := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    have hsupp : D.support ⊆ S := Finsupp.support_onFinset_subset
    rw [Finset.sum_subset hsupp (fun v _ hv => by
      have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      rw [this]; simp)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one, hD]
  have hsplit : ∑ v ∈ S, recipe N m v
      = ∑ v ∈ S0, recipe N m v + ∑ v ∈ S1, recipe N m v + ∑ v ∈ Sinf, recipe N m v := by
    rw [hSdef, Finset.sum_union hdisj0I, Finset.sum_union hdisj01]

  have hsum0 : 3 * ∑ v ∈ S0, recipe N m v
      = 3 * ((2 * m / 3 : ℕ) : ℤ) * ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ)
        + 2 * (m : ℤ) * ((dedekindPsi N : ℤ) - ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ)) := by
    have hψ₀ : ∑ v ∈ S0, v.ord (jBar N) = (dedekindPsi N : ℤ) := by
      have h := sum_ord_jBar_sub_eq_dedekindPsi N 0 hdeg S0 (fun v => by rw [hS0, map_zero, sub_zero])
      simpa [map_zero, sub_zero] using h

    have hcase : ∀ v ∈ S0, (v.ord (jBar N) = 1 ∧ recipe N m v = ((2 * m / 3 : ℕ) : ℤ)) ∨
        (v.ord (jBar N) = 3 ∧ recipe N m v = 2 * (m : ℤ)) := by
      intro v hv
      have hpos := (hS0 v).1 hv
      have hdvd := ord_jBar_dvd_three N v hpos
      rw [recipe_of_pos N m hpos]
      rcases int_eq_of_pos_of_dvd_three hpos hdvd with h1 | h3
      · left; refine ⟨h1, ?_⟩; rw [h1]; push_cast; omega
      · right; refine ⟨h3, ?_⟩; rw [h3]; omega
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord (jBar N) = 1)]
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord (jBar N) = 1)] at hψ₀
    have hA : ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), 3 * recipe N m v
        = 3 * ((2 * m / 3 : ℕ) : ℤ) * ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 3 * ((2 * m / 3 : ℕ) : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨-, hr⟩ | ⟨h3, -⟩
        · rw [hr]
        · omega
    have hB : ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), 3 * recipe N m v
        = 6 * (m : ℤ) * ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 6 * (m : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨-, hr⟩
        · exact absurd h1' h1
        · rw [hr]; ring
    have hψA : ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), v.ord (jBar N)
        = ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun v hv => (Finset.mem_filter.mp hv).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hψB : ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), v.ord (jBar N)
        = 3 * ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (3 : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨h3, -⟩
        · exact absurd h1' h1
        · exact h3
    rw [hA, hB]
    rw [hψA, hψB] at hψ₀
    linear_combination (2 * (m : ℤ)) * hψ₀

  have hsum1 : 2 * ∑ v ∈ S1, recipe N m v
      = 2 * ((m / 2 : ℕ) : ℤ) * ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ)
        + (m : ℤ) * ((dedekindPsi N : ℤ) - ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ)) := by
    have hψ₁ : ∑ v ∈ S1, v.ord (jBar N - algebraMap ℚb 𝔽 1728) = (dedekindPsi N : ℤ) :=
      sum_ord_jBar_sub_eq_dedekindPsi N 1728 hdeg S1 hS1
    have hcase : ∀ v ∈ S1, (v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1 ∧ recipe N m v = ((m / 2 : ℕ) : ℤ)) ∨
        (v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 2 ∧ recipe N m v = (m : ℤ)) := by
      intro v hv
      have hpos := (hS1 v).1 hv
      have hdvd := ord_jBar_sub_1728_dvd_two N v hpos
      rw [recipe_of_pos_1728 N m hpos]
      rcases int_eq_of_pos_of_dvd_two hpos hdvd with h1 | h2
      · left; refine ⟨h1, ?_⟩; rw [h1]; push_cast; omega
      · right; refine ⟨h2, ?_⟩; rw [h2]; omega
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1)]
    rw [← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1)] at hψ₁
    have hA : ∑ v ∈ S1.filter (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), 2 * recipe N m v
        = 2 * ((m / 2 : ℕ) : ℤ) * ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 2 * ((m / 2 : ℕ) : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨-, hr⟩ | ⟨h2, -⟩
        · rw [hr]
        · omega
    have hB : ∑ v ∈ S1.filter (fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), 2 * recipe N m v
        = 2 * (m : ℤ) * ((S1.filter fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 2 * (m : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨-, hr⟩
        · exact absurd h1' h1
        · rw [hr]
    have hψA : ∑ v ∈ S1.filter (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), v.ord (jBar N - algebraMap ℚb 𝔽 1728)
        = ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun v hv => (Finset.mem_filter.mp hv).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hψB : ∑ v ∈ S1.filter (fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), v.ord (jBar N - algebraMap ℚb 𝔽 1728)
        = 2 * ((S1.filter fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (2 : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨h2, -⟩
        · exact absurd h1' h1
        · exact h2
    rw [hA, hB]
    rw [hψA, hψB] at hψ₁
    linear_combination (m : ℤ) * hψ₁

  have hsumI : ∑ v ∈ Sinf, recipe N m v = -(m : ℤ) * (dedekindPsi N : ℤ) - (Sinf.card : ℤ) := by
    have hψinf : ∑ v ∈ Sinf, -v.ord (jBar N) = (dedekindPsi N : ℤ) := sum_neg_ord_jBar_eq_dedekindPsi N Sinf hSI
    rw [Finset.sum_congr rfl (g := fun v => -(m : ℤ) * (-v.ord (jBar N)) + (-1))
      (fun v hv => by rw [recipe_of_neg N m ((hSI v).1 hv)]; ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hψinf, Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    ring

  have hNC : ∀ (P : Place ℚb 𝔽 → Prop) (T : Finset (Place ℚb 𝔽)),
      (∀ v, v ∈ T ↔ P v) → Nat.card {v // P v} = T.card := by
    intro P T hT
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hT v).symm) : {v // P v} ≃ {v // v ∈ T}),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have h1728 : (jBar N - 1728 : 𝔽) = jBar N - algebraMap ℚb 𝔽 1728 := by rw [map_ofNat]
  have hε₂ : (S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card = nuTwo N := by
    have h2 : ∀ v : Place ℚb 𝔽, 0 < v.ord (jBar N - 1728) → v.ord (jBar N - 1728) ∣ 2 := fun v hv => by
      rw [h1728] at hv ⊢
      exact ord_jBar_sub_1728_dvd_two N v hv
    have hcount : Nat.card {v : Place ℚb 𝔽 // 0 < v.ord (jBar N - 1728)}
        = Nat.card {x : ModuliPoint N ℚb // ModuliPoint.j x = (1728 : ℚb)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 1728 (emd_holds N 1728) S1 hS1]
      exact hNC _ S1 (fun v => by rw [hS1, h1728])
    have h := natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo N h2 hcount
    rwa [hNC _ (S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS1, h1728]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hε₃ : (S0.filter fun v => v.ord (jBar N) = 1).card = nuThree N := by
    have h3 : ∀ v : Place ℚb 𝔽, 0 < v.ord (jBar N) → v.ord (jBar N) ∣ 3 := fun v hv => ord_jBar_dvd_three N v hv
    have hcount : Nat.card {v : Place ℚb 𝔽 // 0 < v.ord (jBar N)}
        = Nat.card {x : ModuliPoint N ℚb // ModuliPoint.j x = (0 : ℚb)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 0 (emd_holds N 0) S0 (fun v => by rw [hS0, map_zero, sub_zero])]
      exact hNC _ S0 (fun v => by rw [hS0])
    have h := natCard_ord_jBar_eq_one_eq_nuThree N h3 hcount
    rwa [hNC _ (S0.filter fun v => v.ord (jBar N) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS0]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hcard : Sinf.card = cuspCount N := card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg N Sinf hSI
  rw [hε₃] at hsum0
  rw [hε₂] at hsum1
  rw [hcard] at hsumI

  set A0 : ℤ := ∑ v ∈ S0, recipe N m v with hA0
  set A1 : ℤ := ∑ v ∈ S1, recipe N m v with hA1
  set AI : ℤ := ∑ v ∈ Sinf, recipe N m v with hAI
  have c0 : (3 : ℚ) * (A0 : ℚ) = 3 * ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ)
      + 2 * (m : ℚ) * ((dedekindPsi N : ℚ) - (nuThree N : ℚ)) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsum0
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using h
  have c1 : (2 : ℚ) * (A1 : ℚ) = 2 * ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
      + (m : ℚ) * ((dedekindPsi N : ℚ) - (nuTwo N : ℚ)) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsum1
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using h
  have cI : (AI : ℚ) = -(m : ℚ) * (dedekindPsi N : ℚ) - (cuspCount N : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsumI
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast] using h
  have eD : (D.degree : ℚ) = (A0 : ℚ) + (A1 : ℚ) + (AI : ℚ) := by
    rw [hdegsum, hsplit]; push_cast; ring
  unfold genusFormula
  linear_combination eD + (1 / 3 : ℚ) * c0 + (1 / 2 : ℚ) * c1 + cI

end ModularCurve.LDivDegree

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.ModularCurve AlgebraicCurve"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jBar modularFunctionFieldBar jq coeff_jq_neg_one dedekindPsi coeffEmb coeffEmb_coeff nuTwo nuThree cuspCount genusFormula EMD ModuliPoint ModuliPoint.j sum_ord_jBar_sub_eq_dedekindPsi deg_eq_one_modularFunctionFieldBar jCoordinate_spec_modularFunctionFieldBar sum_neg_ord_jBar_eq_dedekindPsi ord_jBar_dvd_three ord_jBar_sub_1728_dvd_two card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo natCard_ord_jBar_eq_one_eq_nuThree card_eq_natCard_moduliPoint_j_eq_of_EMD emd_holds transcendental_coeffEmb_jq isCurveOver_modularFunctionFieldBar finiteDimensional_adjoin_coeffEmb_jq_of_neZero dedekindPsi_pos"
namespace LDivIntegral
p2m_open "ModularCurve"

variable (N : ℕ) [NeZero N]

theorem jBar_ne_zero : (jBar N : modularFunctionFieldBar N) ≠ 0 := by
  intro h
  have h2 : (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 0 := by
    have h1 : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      rw [h]; rfl
    have : (coeffEmb (AlgebraicClosure ℚ) jq) = 0 := h1
    rw [this]; rfl
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h2
  exact one_ne_zero h2

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow' (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

theorem six_mul_ediv_two_le (n : ℤ) : 6 * (n / 2) ≤ 3 * n := by
  have := Int.ediv_mul_le n (by norm_num : (2 : ℤ) ≠ 0)
  linarith

theorem six_mul_ediv_three_le (n : ℤ) : 6 * (n / 3) ≤ 2 * n := by
  have := Int.ediv_mul_le n (by norm_num : (3 : ℤ) ≠ 0)
  linarith

theorem two_mul_ediv_two_le (n : ℤ) : 2 * (n / 2) ≤ n := by
  have := Int.ediv_mul_le n (by norm_num : (2 : ℤ) ≠ 0)
  linarith

end Generic

theorem isIntegral_pair_of_mem_riemannRochSpace (m : ℕ)
    (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDfin : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord (jBar N) →
      Dv v ≤ (m : ℤ) * v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) / 2
        + 2 * (m : ℤ) * v.ord (jBar N) / 3)
    (hDcusp : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord (jBar N) < 0 →
      Dv v ≤ (m : ℤ) * v.ord (jBar N) - 1)
    (x : modularFunctionFieldBar N) (hx : x ∈ riemannRochSpace Dv) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))
        (x ^ 6 * jBar N ^ (4 * m)
          * (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
        (x ^ (2 * dedekindPsi N) * jBar N ^ (m * dedekindPsi N + 1)
          * (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) ^ (m * dedekindPsi N)) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI hFD : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  set J : modularFunctionFieldBar N := jBar N with hJdef
  set ψ : ℕ := dedekindPsi N with hψdef
  set c1728 : modularFunctionFieldBar N := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728
    with hc
  have hψpos : 0 < ψ := ModularCurve.dedekindPsi_pos N (NeZero.ne N)
  have hJ0 : J ≠ 0 := jBar_ne_zero N

  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, ?_⟩
    · rw [zero_pow (by norm_num), zero_mul, zero_mul]; exact isIntegral_zero
    · rw [zero_pow (by omega), zero_mul, zero_mul]; exact isIntegral_zero

  have hxord : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), -Dv v ≤ v.ord x := by
    intro v
    rcases (mem_riemannRochSpace_iff.mp hx) v with h | h
    · exact absurd h hx0
    · exact h

  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (F := modularFunctionFieldBar N) J hJ0
  let S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    Dj.support.filter (fun v => v.ord J < 0)
  have hS : ∀ v, v ∈ S ↔ v.ord J < 0 := by
    intro v
    simp only [S, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hv
    rw [hDj v]
    exact hv.ne
  have hsum : ∑ v ∈ S, -v.ord J = (ψ : ℤ) := by
    have := ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi N S hS
    exact_mod_cast this
  have hwidth : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord J < 0 → -v.ord J ≤ (ψ : ℤ) := by
    intro v hv
    rw [← hsum]
    exact Finset.single_le_sum (f := fun w => -w.ord J)
      (fun w hw => by have := (hS w).mp hw; show (0 : ℤ) ≤ -w.ord J; omega) ((hS v).mpr hv)
  have hpole : ∃ v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v₀.ord J < 0 := by
    by_contra hno
    push_neg at hno
    have hSe : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact absurd ((hS v).mp hv) (not_lt.mpr (hno v))
    rw [hSe, Finset.sum_empty] at hsum
    have h' : (ψ : ℤ) = 0 := hsum.symm
    omega
  obtain ⟨v₀, hv₀⟩ := hpole

  have htr : Transcendental (AlgebraicClosure ℚ) J := by
    intro halg
    have hint : IsIntegral (AlgebraicClosure ℚ) J := halg.isIntegral
    have hint' : IsIntegral v₀.toValuationSubring J := hint.tower_top
    have hmem : J ∈ v₀.toValuationSubring := by
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v₀.toValuationSubring)
        (K := modularFunctionFieldBar N)).mp hint'
      rw [← hy]
      exact y.2
    have := v₀.ord_nonneg_of_mem hmem
    omega
  have h1728ne : (1728 : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  have hJne1728 : J - c1728 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := ord_algebraMap v₀ (c := (1728 : AlgebraicClosure ℚ)) h1728ne
    rw [hc] at h
    rw [← h] at this
    omega

  have hordJsub_of_neg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord J < 0 →
      v.ord (J - c1728) = v.ord J := by
    intro v hv
    have hc0 : v.ord (-c1728) = 0 := by rw [ord_neg]; exact ord_algebraMap v h1728ne
    have := v.ord_add_eq_of_lt (f := J) (g := -c1728) hJ0
      (neg_ne_zero.mpr (by rw [hc, Ne, map_eq_zero]; norm_num)) (by rw [hc0]; exact hv)
    rwa [← sub_eq_add_neg] at this
  have hordJsub_nonneg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord J →
      0 ≤ v.ord (J - c1728) := by
    intro v hv
    have hJmem : J ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hJ0).mpr hv
    exact v.ord_nonneg_of_mem (sub_mem hJmem (v.algebraMap_mem' _))
  refine ⟨?_, ?_⟩
  ·
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N) J htr _ ?_
    intro v hvJ
    have ha := hordJsub_nonneg v hvJ
    have hD := hDfin v hvJ
    have hxv := hxord v
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    have h2 := six_mul_ediv_two_le ((m : ℤ) * v.ord (J - c1728))
    have h3 := six_mul_ediv_three_le (2 * (m : ℤ) * v.ord J)
    push_cast
    nlinarith
  ·
    have htr' : Transcendental (AlgebraicClosure ℚ) J⁻¹ := by
      intro halg
      exact htr (by simpa using halg.inv)
    have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set (modularFunctionFieldBar N))
        = IntermediateField.adjoin (AlgebraicClosure ℚ) ({J} : Set (modularFunctionFieldBar N)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) J)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h1 := IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (J⁻¹)
        have h2 : (J⁻¹)⁻¹ ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set (modularFunctionFieldBar N)) :=
          inv_mem h1
        rwa [inv_inv] at h2
    haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({J⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) := by
      rw [hadj]; exact hFD
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N) J⁻¹ htr' _ ?_
    intro v hvJinv
    rw [v.ord_inv] at hvJinv
    have hvJ : v.ord J ≤ 0 := by omega
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    have hxv := hxord v
    rcases hvJ.lt_or_eq with hneg | hzero
    ·
      have hw := hwidth v hneg
      have hD := hDcusp v hneg
      rw [hordJsub_of_neg v hneg]
      have hψ1 : (1 : ℤ) ≤ ψ := by exact_mod_cast hψpos
      push_cast

      have hx1 : 1 - (m : ℤ) * v.ord J ≤ v.ord x := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℤ) ≤ 2 * (ψ : ℤ))]
    ·
      have ha := hordJsub_nonneg v hzero.ge
      have hD := hDfin v hzero.ge
      rw [hzero, mul_zero, Int.zero_ediv, add_zero] at hD
      have h2 := two_mul_ediv_two_le ((m : ℤ) * v.ord (J - c1728))
      rw [hzero]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (show -( (m : ℤ) * v.ord (J - c1728) / 2) ≤ v.ord x by linarith)
        (by positivity : (0 : ℤ) ≤ 2 * (ψ : ℤ))]

end ModularCurve.LDivIntegral

end

theorem solution (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)) ∧
      ∀ x : ↥(ModularCurve.modularFunctionFieldBar N), x ∈ AlgebraicCurve.riemannRochSpace D →
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ 6 * ModularCurve.jBar N ^ (4 * m) * (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
          IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
              (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N)) := by
  obtain ⟨D, hdeg, hDfin, hDcusp⟩ := ModularCurve.LDivDegree.exists_weightDivisor N m hm
  exact ⟨D, hdeg, fun x hx =>
    ModularCurve.LDivIntegral.isIntegral_pair_of_mem_riemannRochSpace N m D hDfin hDcusp x hx⟩

end S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace (solution)

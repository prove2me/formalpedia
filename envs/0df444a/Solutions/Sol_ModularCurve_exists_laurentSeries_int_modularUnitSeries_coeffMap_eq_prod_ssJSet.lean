-- Prove2me | solution 1 for ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/18fc2aca-6efb-5edc-9d4b-45a8a2c65858

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_card_eq_of_ssJSet
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve

universe u

namespace M1

theorem coeffMap_int_eq_prod_residueField (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (x : LaurentSeries ℤ) (hx : coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField A)]
    (S₀ : Finset (IsLocalRing.ResidueField A))
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p (IsLocalRing.ResidueField A)) :
    coeffMap (Int.castRingHom (IsLocalRing.ResidueField A)) x =
      ∏ a ∈ S₀, (jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^ (12 / jWidth a) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hpN : ¬ p ∣ 1 := hp.out.not_dvd_one

  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull (1 * p) :=
    full_degeneracy_le (dvd_mul_left p 1) (modularUnitSeries_mem_modularFunctionFieldFull p)

  obtain ⟨R, hR0, h₀, -⟩ :=
    ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd 1 p hpN A hA

  obtain ⟨hu₀, -, hres⟩ :=
    ModularCurve.residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation 1 p hp5
      A hA hmem (R 0) h₀ S₀ hS₀

  set y : LaurentSeries A := coeffMap (Int.castRingHom A) x with hy
  have hyx : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) := by
    rw [hy, coeffMap_coeffMap, coeffEmb, ← hx, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  have hymem : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p) := by
    rw [hyx]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem
  obtain ⟨hint, hresy⟩ := h₀ y hymem
  have helt : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ : modularFunctionFieldBar (1 * p))
      = ⟨coeffMap A.subtype y, hymem⟩ := Subtype.ext hyx.symm
  have hres' : (((R 0).residue ⟨_, hint⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)
      : LaurentSeries (IsLocalRing.ResidueField A)) =
      ∏ a ∈ S₀, (jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^ (12 / jWidth a) := by
    rw [← hres]
    congr 3
    exact Subtype.ext (congrArg Subtype.val helt.symm)
  rw [← hres', hresy, hy, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) x

theorem transport (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (x : LaurentSeries ℤ)
    {k₀ : Type*} [Field k₀] [CharP k₀ p] [IsAlgClosed k₀] [DecidableEq k₀]
    (S₀ : Finset k₀) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p k₀)
    (h₀ : coeffMap (Int.castRingHom k₀) x =
      ∏ a ∈ S₀, (jqModC k₀ - HahnSeries.C a) ^ (12 / jWidth a))
    {κ : Type*} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (ι : k₀ →+* κ)
    (S : Finset κ) (hS : ∀ a, a ∈ S ↔ a ∈ ssJSet p κ) :
    coeffMap (Int.castRingHom κ) x = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := by
  classical
  have h1 : coeffMap (Int.castRingHom κ) x = coeffMap ι (coeffMap (Int.castRingHom k₀) x) := by
    rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) x
  have hC : ∀ a : k₀, coeffMap ι (HahnSeries.C a) = HahnSeries.C (ι a) := fun a => by
    rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]
  rw [h1, h₀, map_prod]
  simp_rw [map_pow, map_sub, coeffMap_jqModC, hC]

  have hinj : Function.Injective ι := ι.injective
  have himg : S₀.image ι = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact (hS _).mpr (mem_ssJSet_map_of_isAlgClosed ι a ((hS₀ a).mp ha))
    · rw [Finset.card_image_of_injective _ hinj, card_eq_of_ssJSet p hp5 k₀ S₀ hS₀,
        card_eq_of_ssJSet p hp5 κ S hS]
  rw [← himg, Finset.prod_image (fun a _ b _ h => hinj h)]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [jWidth_map]

theorem main (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
      ∀ (κ : Type u) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (S : Finset κ),
        (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
        coeffMap (Int.castRingHom κ) x =
          ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hpN : ¬ p ∣ 1 := hp.out.not_dvd_one
  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull (1 * p) :=
    full_degeneracy_le (dvd_mul_left p 1) (modularUnitSeries_mem_modularFunctionFieldFull p)

  obtain ⟨W, hW0, hW1, -⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd 1 p hpN
  obtain ⟨⟨x, -, hx⟩, -⟩ :=
    ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd 1 p hpN hmem (W 0) (W 1)
      hW0 hW1
  refine ⟨x, hx.symm, ?_⟩
  intro κ _ _ _ _ S hS

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp.out⟩
  haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    ValuationSubring.residueField_charP_of_liesOverPrime A hp.out hA
  set S₀ : Finset (IsLocalRing.ResidueField A) :=
    (ssJSet_finite p (IsLocalRing.ResidueField A)).toFinset with hS₀def
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p (IsLocalRing.ResidueField A) := fun a => by
    rw [hS₀def, Set.Finite.mem_toFinset]
  have h₀ := coeffMap_int_eq_prod_residueField p hp5 x hx.symm A hA S₀ hS₀

  obtain ⟨e⟩ :=
    ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A
      (q := p) hA
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  let ι₀ : AlgebraicClosure (ZMod p) →ₐ[ZMod p] κ := IsAlgClosed.lift
  exact transport p hp5 x S₀ hS₀ h₀ (ι₀.toRingHom.comp e.toRingHom) S hS

end M1

theorem solution (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
      ∀ (κ : Type u) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (S : Finset κ),
        (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
        coeffMap (Int.castRingHom κ) x =
          ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) :=
  M1.main p hp

end S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
end P2MW
export P2MW.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet (solution)

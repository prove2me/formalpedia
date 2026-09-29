-- Prove2me | solution 1 for ModularCurve.XOneP.modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cc59e966-1303-5530-a398-6d296fb21bc7

import Mathlib
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode"
p2m_attr_erase "simp" "ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

open scoped Polynomial

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace ModularCurve
p2m_export "ModularCurve" "exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five modularUnitSeries coeff_modularUnitSeries_self coeff_modularUnitSeries_of_lt jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffEmb laurentBaseChange exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet TwoChart.chartAlgFin x1FunctionField"
namespace XOneP
namespace Dict0
p2m_open "ModularCurve~coeffMap_ofPowerSeries"

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem coeff_ofPowerSeries_neg {R : Type*} [Semiring R] (φ : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ R φ).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  have : (n : ℤ) = k := hn
  omega

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (φ : PowerSeries R) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ R φ) = HahnSeries.ofPowerSeries ℤ S (φ.map f) := by
  ext n
  rw [ModularCurve.coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_ofPowerSeries_neg _ hn, coeff_ofPowerSeries_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem order_eq_of_coeff {k : Type*} [Zero k] {z : LaurentSeries k} {m : ℤ} (h1 : z.coeff m ≠ 0)
    (h2 : ∀ n < m, z.coeff n = 0) : z.order = m := by
  have hz : z ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push_neg at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.2 hz) (h2 _ hlt)

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

noncomputable def toLS (A L : Type*) [CommRing A] [Field L] [Algebra A L] : PowerSeries A →+* LaurentSeries L :=
  (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap A L))

theorem map_map' {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T)
    (φ : PowerSeries R) : (φ.map f).map g = φ.map (g.comp f) := by
  rw [PowerSeries.map_comp]; rfl

theorem toLS_apply (x : PowerSeries A) : toLS A L x = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := rfl

theorem toLS_injective (hinj : Function.Injective (algebraMap A L)) : Function.Injective (toLS A L) := by
  intro x y h
  exact PowerSeries.map_injective (algebraMap A L) hinj (HahnSeries.ofPowerSeries_injective h)

@[scoped simp] theorem toLS_C (a : A) : toLS A L (PowerSeries.C a) = HahnSeries.C (algebraMap A L a) := by
  simp [toLS]

theorem toLS_X : toLS A L PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : L) := by
  rw [toLS, RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem toLS_X_pow (d : ℕ) : toLS A L (PowerSeries.X ^ d) = HahnSeries.single (d : ℤ) (1 : L) := by
  rw [map_pow, toLS_X, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

noncomputable def polyNum (t : ℕ) (N : PowerSeries A) (P : Polynomial A) : PowerSeries A :=
  ∑ i ∈ Finset.range (P.natDegree + 1), PowerSeries.C (P.coeff i) * (PowerSeries.X ^ (t * (P.natDegree - i)) * N ^ i)

theorem constantCoeff_polyNum {t : ℕ} (ht : 0 < t) (N : PowerSeries A) (P : Polynomial A) :
    PowerSeries.constantCoeff (polyNum t N P) = P.coeff P.natDegree * PowerSeries.constantCoeff N ^ P.natDegree := by
  classical
  unfold polyNum
  rw [map_sum, Finset.sum_eq_single P.natDegree]
  · rw [map_mul, map_mul, map_pow, map_pow, PowerSeries.constantCoeff_C, Nat.sub_self, mul_zero, pow_zero, one_mul]
  · intro i hi hne
    have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpos : t * (P.natDegree - i) ≠ 0 := Nat.mul_ne_zero ht.ne' (by omega)
    rw [map_mul, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hpos, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ P.natDegree) h

variable {K : IntermediateField L (LaurentSeries L)} [Algebra A ↥K] [IsScalarTower A L ↥K]

theorem coe_algebraMap_K (a : A) : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = toLS A L (PowerSeries.C a) := by
  rw [toLS_C, IsScalarTower.algebraMap_apply A L ↥K a]
  show ((algebraMap L ↥K (algebraMap A L a) : ↥K) : LaurentSeries L) = _
  rw [show ((algebraMap L ↥K (algebraMap A L a) : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) from rfl,
    LaurentSeries.algebraMap_apply]

theorem aeval_mul_toLS_X_pow (t : ℕ) (N : PowerSeries A) (P : Polynomial A) (z : ↥K)
    (hz : (z : LaurentSeries L) = HahnSeries.single (-(t : ℤ)) (1 : L) * toLS A L N) :
    ((Polynomial.aeval z P : ↥K) : LaurentSeries L) * toLS A L (PowerSeries.X ^ (t * P.natDegree)) =
      toLS A L (polyNum t N P) := by
  have hq : ∀ i ∈ Finset.range (P.natDegree + 1),
      (z : LaurentSeries L) ^ i * HahnSeries.single ((t * P.natDegree : ℕ) : ℤ) (1 : L) =
        HahnSeries.single ((t * (P.natDegree - i) : ℕ) : ℤ) (1 : L) * toLS A L N ^ i := by
    intro i hi
    have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hz, mul_pow, HahnSeries.single_pow, one_pow, mul_right_comm, HahnSeries.single_mul_single, one_mul]
    have e : (i • (-(t : ℤ)) + ((t * P.natDegree : ℕ) : ℤ)) = ((t * (P.natDegree - i) : ℕ) : ℤ) := by
      rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hid]; ring
    rw [e]
  rw [Polynomial.aeval_eq_sum_range, AddSubmonoidClass.coe_finset_sum, Finset.sum_mul, toLS_X_pow, polyNum, map_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Algebra.smul_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_algebraMap_K, mul_assoc, hq i hi, map_mul, map_mul,
    toLS_X_pow, map_pow, ← mul_assoc]

end ModularCurve.XOneP.Dict0
p2m_reactivate "P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve.XOneP P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve.XOneP.Dict0"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve.XOneP"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul.ModularCurve"

set_option maxHeartbeats 1600000 in
open ModularCurve.XOneP.Dict0 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (hu' : ((u' : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))))

    (σ : ↥K ≃ₐ[L] ↥K) (hσu : σ (u : ↥K) = (u' : ↥K))
    (W₁ : ValuationSubring ↥K) (hW₁ : ∀ f : ↥K, f ∈ W₁ ↔ σ f ∈ W₀)
    (P₁ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) [P₁.IsPrime] (hP₁ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ P₁ ↔ (b : ↥K) ∈ W₁.nonunits)
    :
    u ∈ P₁ ∧ u' ∉ P₁ ∧ (∀ g : ℤ[X], g.Monic → 0 < g.natDegree → Polynomial.aeval u' g ∉ P₁) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨xu, hxu⟩ : ∃ x : LaurentSeries ℤ,
      ModularCurve.coeffMap (Int.castRingHom ℚ) x = ModularCurve.modularUnitSeries p := by
    by_cases h5 : p < 5
    · obtain ⟨x, hx, -⟩ :=
        ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five.{0} p h5
      exact ⟨x, hx⟩
    · obtain ⟨x, hx, -⟩ :=
        ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet.{0} p (by omega)
      exact ⟨x, hx⟩
  have hcoeffZ : ∀ n : ℤ, ((xu.coeff n : ℤ) : ℚ) = (ModularCurve.modularUnitSeries p).coeff n := by
    intro n; rw [← hxu, ModularCurve.coeffMap_coeff]; rfl
  have hxu1 : xu.coeff (1 - (p : ℤ)) = 1 := by
    have h2 := hcoeffZ (1 - (p : ℤ))
    rw [ModularCurve.coeff_modularUnitSeries_self] at h2
    exact_mod_cast h2
  have hxu0 : ∀ n < 1 - (p : ℤ), xu.coeff n = 0 := by
    intro n hn
    have h2 := hcoeffZ n
    rw [ModularCurve.coeff_modularUnitSeries_of_lt p hn] at h2
    exact_mod_cast h2
  have hord : xu.order = 1 - (p : ℤ) := order_eq_of_coeff (by rw [hxu1]; exact one_ne_zero) hxu0

  set t : ℕ := p - 1 with ht
  have ht0 : 0 < t := by have := hp.two_le; omega
  have htz : -(1 - (p : ℤ)) = (t : ℤ) := by have := hp.one_le; omega
  set e : PowerSeries ℤ := xu.powerSeriesPart with he_def
  have he : HahnSeries.ofPowerSeries ℤ ℤ e = HahnSeries.single (t : ℤ) 1 * xu := by
    rw [he_def, LaurentSeries.ofPowerSeries_powerSeriesPart, hord, htz]
  have he0 : PowerSeries.constantCoeff e = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he_def, LaurentSeries.powerSeriesPart_coeff, hord,
      Nat.cast_zero, add_zero, hxu1]
  set N : PowerSeries A := e.map (Int.castRingHom A) with hN_def
  have hN0 : PowerSeries.constantCoeff N = 1 := by
    rw [hN_def, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, he0, map_one]
  have hxu' : xu = HahnSeries.single (-(t : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℤ e := by
    rw [he, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, one_mul, HahnSeries.single_zero_one, one_mul]
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hcomp : (algebraMap ℚ L).comp (Int.castRingHom ℚ) = (algebraMap A L).comp (Int.castRingHom A) :=
    RingHom.ext_int _ _

  have huz : ((u : ↥K) : LaurentSeries L) = HahnSeries.single (-(t : ℤ)) (1 : L) * toLS A L N := by
    rw [hu, ← hxu, hxu', ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap, map_mul, ModularCurve.coeffMap_single,
      map_one, coeffMap_ofPowerSeries, toLS_apply, hN_def, map_map', hcomp]

  have haev : ∀ {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (y : S) (g : ℤ[X]),
      φ (Polynomial.aeval y g) = Polynomial.aeval (φ y) g := by
    intro S T _ _ φ y g
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _

  have core : ∀ g : ℤ[X], g.Monic →
      ((Polynomial.aeval (u : ↥K) g : ↥K) : LaurentSeries L) ≠ 0 ∧ (Polynomial.aeval (u : ↥K) g)⁻¹ ∈ W₀ := by
    intro g hg
    set P : Polynomial A := g.map (Int.castRingHom A) with hP_def
    have hPmon : P.Monic := hg.map _
    have hPg : Polynomial.aeval (u : ↥K) P = Polynomial.aeval (u : ↥K) g := by
      rw [hP_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
      congr 1
      exact RingHom.ext_int _ _
    have hpres := aeval_mul_toLS_X_pow (K := K) t N P (u : ↥K) huz
    have hnum0 : PowerSeries.constantCoeff (polyNum t N P) = 1 := by
      rw [constantCoeff_polyNum ht0, hPmon.coeff_natDegree, hN0, one_pow, one_mul]
    have hred : (polyNum t N P).map (IsLocalRing.residue A) ≠ 0 := by
      intro h
      have h' := congrArg PowerSeries.constantCoeff h
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hnum0, map_one, map_zero] at h'
      exact one_ne_zero h'
    have hne : ((Polynomial.aeval (u : ↥K) P : ↥K) : LaurentSeries L) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hpres
      have h1 : polyNum t N P = 0 := toLS_injective hinjAL (by rw [map_zero]; exact hpres.symm)
      rw [h1, map_zero] at hnum0
      exact zero_ne_one hnum0
    rw [hPg] at hpres hne
    refine ⟨hne, (hW₀ _).mpr ⟨PowerSeries.X ^ (t * P.natDegree), polyNum t N P, hred, ?_⟩⟩
    rw [IntermediateField.coe_inv, ← toLS_apply, ← toLS_apply, ← hpres, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hcoeO : ∀ g : ℤ[X], ((Polynomial.aeval u g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (u : ↥K) g :=
    fun g => haev (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom u g

  obtain ⟨hUne, hUinv⟩ := core Polynomial.X Polynomial.monic_X
  rw [Polynomial.aeval_X] at hUne hUinv
  have hpW : (algebraMap A ↥K (p : A)) ∈ W₀.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hmem
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp hmem
    rw [IntermediateField.coe_inv, coe_algebraMap_K, ← toLS_apply, ← toLS_apply] at hxy
    have hCp : toLS A L (PowerSeries.C (p : A)) ≠ 0 := by
      rw [toLS_C, map_natCast]
      exact HahnSeries.C_ne_zero (by exact_mod_cast hp.ne_zero)
    have hy' : y = PowerSeries.C (p : A) * x := by
      apply toLS_injective hinjAL
      rw [map_mul, ← hxy, ← mul_assoc, mul_inv_cancel₀ hCp, one_mul]
    apply hy
    rw [hy', map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr hAp, map_zero, zero_mul]
  haveI : CharZero ↥K := charZero_of_injective_algebraMap (algebraMap L ↥K).injective
  have hpK0 : (p : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hUK0 : (u : ↥K) ≠ 0 := fun h => hUne (by rw [h]; rfl)
  have hu'K : (u' : ↥K) = (p : ↥K) ^ 12 * (u : ↥K)⁻¹ := by
    apply K.val.toRingHom.injective
    change ((u' : ↥K) : LaurentSeries L) = K.val.toRingHom ((p : ↥K) ^ 12 * (u : ↥K)⁻¹)
    rw [map_mul, map_pow, map_inv₀, map_natCast]
    change _ = (p : LaurentSeries L) ^ 12 * ((u : ↥K) : LaurentSeries L)⁻¹
    rw [hu', hu]
  have hU'non : (u' : ↥K) ∈ W₀.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, hu'K, map_mul, map_pow]
    have hv1 : W₀.valuation ((u : ↥K)⁻¹) ≤ 1 := (W₀.valuation_le_one_iff _).mpr hUinv
    have hvp : W₀.valuation (p : ↥K) < 1 := by
      rw [← map_natCast (algebraMap A ↥K) p]
      exact (ValuationSubring.mem_nonunits_iff _).mp hpW
    calc W₀.valuation (p : ↥K) ^ 12 * W₀.valuation ((u : ↥K)⁻¹)
        ≤ W₀.valuation (p : ↥K) ^ 12 * 1 := mul_le_mul_right hv1 _
      _ = W₀.valuation (p : ↥K) ^ 12 := mul_one _
      _ < 1 := pow_lt_one₀ zero_le' hvp (by norm_num)

  have htr : ∀ f : ↥K, f ∈ W₁.nonunits ↔ σ f ∈ W₀.nonunits := by
    intro f
    simp only [ValuationSubring.mem_nonunits_iff_or, hW₁, map_inv₀, map_eq_zero_iff σ σ.injective]
  have hσu' : σ (u' : ↥K) = (u : ↥K) := by
    rw [hu'K, map_mul, map_pow, map_natCast, map_inv₀, hσu, hu'K, mul_inv, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 12 hpK0), one_mul]
  have hcoeO' : ∀ g : ℤ[X], ((Polynomial.aeval u' g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (u' : ↥K) g :=
    fun g => haev (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom u' g
  refine ⟨?_, ?_, ?_⟩
  ·
    exact (hP₁ _).mpr ((htr _).mpr (by rw [hσu]; exact hU'non))
  ·
    intro hmem
    have hn := (htr _).mp ((hP₁ _).mp hmem)
    rw [hσu', ValuationSubring.mem_nonunits_iff_or] at hn
    rcases hn with h0 | h
    · exact hUK0 h0
    · exact h hUinv
  ·
    intro g hg _ hmem
    have hn := (htr _).mp ((hP₁ _).mp hmem)
    have hσaev : σ (Polynomial.aeval (u' : ↥K) g) = Polynomial.aeval (σ (u' : ↥K)) g := by
      simpa using haev ((σ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K) (u' : ↥K) g
    rw [hcoeO', hσaev, hσu', ValuationSubring.mem_nonunits_iff_or] at hn
    obtain ⟨hne, hinv⟩ := core g hg
    rcases hn with h0 | h
    · apply hne; rw [h0]; rfl
    · exact h hinv

end S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul (solution)

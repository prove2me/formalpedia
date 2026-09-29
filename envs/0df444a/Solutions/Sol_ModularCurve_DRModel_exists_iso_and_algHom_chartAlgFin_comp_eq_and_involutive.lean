-- Prove2me | solution 1 for ModularCurve.DRModel.exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ac394370-4339-53dc-b3d1-0489f55f4795

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
import Theorems.Thm_ModularCurve_DRModel_dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_toBase_int
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_int_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open AlgebraicCurve.TwoChartIntegralModel
p2m_open "Polynomial AlgebraicGeometry.Polynomial ModularCurve.IgusaScheme"

noncomputable section

p2m_open "Polynomial AlgebraicGeometry.Polynomial ModularCurve ModularCurve.IgusaScheme AlgebraicCurve.TwoChartIntegralModel"

namespace G4INST

theorem exists_ofPowerSeries_eq_of_forall_coeff_neg {x : LaurentSeries ℚ} (h : ∀ k : ℤ, k < 0 → x.coeff k = 0) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x := by
  refine ⟨PowerSeries.mk fun n => x.coeff (n : ℤ), ?_⟩
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg _ hk, h k hk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem coeff_neg_eq_zero_of_ofPowerSeries_eq {x : LaurentSeries ℚ} (h : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x)
    (k : ℤ) (hk : k < 0) : x.coeff k = 0 := by
  obtain ⟨y, rfl⟩ := h
  exact ofPowerSeries_coeff_of_neg y hk

theorem exists_ofPowerSeries_eq_qExpand (N : ℕ) [NeZero N] {x : LaurentSeries ℚ}
    (h : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = qExpand ℚ N x := by
  apply exists_ofPowerSeries_eq_of_forall_coeff_neg
  intro k hk
  by_cases hdvd : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact coeff_neg_eq_zero_of_ofPowerSeries_eq h m (by nlinarith)
  · exact qExpand_coeff_of_not_dvd N x hdvd

theorem coeff_zero_ofPowerSeries (y : PowerSeries ℚ) :
    (HahnSeries.ofPowerSeries ℤ ℚ y).coeff 0 = PowerSeries.constantCoeff y := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_zero_mul_of_ofPowerSeries {x x' : LaurentSeries ℚ}
    (h : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x)
    (h' : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x') :
    (x * x').coeff 0 = x.coeff 0 * x'.coeff 0 := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  rw [← map_mul (HahnSeries.ofPowerSeries ℤ ℚ), coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries,
    coeff_zero_ofPowerSeries, map_mul]

theorem coeff_zero_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) : (qExpand ℚ N x).coeff 0 = x.coeff 0 := by
  have h := qExpand_coeff_mul N x 0
  rwa [mul_zero] at h

theorem jq_inv_eq : (jq)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ⁻¹) := by
  have hj : jNumQ * jNumQ⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_jNumQ]; exact one_ne_zero)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [jq, map_mul (HahnSeries.ofPowerSeries ℤ ℚ), HahnSeries.ofPowerSeries_X, mul_mul_mul_comm,
    HahnSeries.single_mul_single, ← map_mul (HahnSeries.ofPowerSeries ℤ ℚ), hj,
    map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one, neg_add_cancel, mul_one]
  rfl

theorem exists_ofPowerSeries_eq_jq_inv : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (jq)⁻¹ :=
  ⟨_, jq_inv_eq.symm⟩

theorem coeff_zero_jq_inv : ((jq)⁻¹).coeff 0 = 0 := by
  rw [jq_inv_eq, coeff_zero_ofPowerSeries, map_mul, PowerSeries.constantCoeff_X, zero_mul]

section Chart

variable (p : ℕ) [NeZero p]

set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull p)

def valHom : FF →+* LaurentSeries ℚ where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [NeZero p] in
@[scoped simp] theorem valHom_apply (x : FF) : valHom p x = (x : LaurentSeries ℚ) := rfl

omit [NeZero p] in

theorem coe_algebraMap_int (c : ℤ) : ((algebraMap ℤ FF c : FF) : LaurentSeries ℚ) = HahnSeries.C (c : ℚ) :=
  congrArg (fun f : ℤ →+* LaurentSeries ℚ => f c)
    (Subsingleton.elim ((valHom p).comp (algebraMap ℤ FF)) ((HahnSeries.C : ℚ →+* LaurentSeries ℚ).comp (Int.castRingHom ℚ)))

theorem exists_ofPowerSeries_eq_of_mem_adjoin (g : FF)
    (hg : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = ((g⁻¹ : FF) : LaurentSeries ℚ))
    (x : FF) (hx : x ∈ Algebra.adjoin ℤ ({g⁻¹} : Set FF)) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hg
  | algebraMap c => exact ⟨PowerSeries.C (c : ℚ), by rw [HahnSeries.ofPowerSeries_C, coe_algebraMap_int]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩

theorem exists_ofPowerSeries_eq_of_mem_chartAlgInf (g : FF)
    (hg : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = ((g⁻¹ : FF) : LaurentSeries ℚ))
    (x : FF) (hx : x ∈ chartAlgInf ℤ FF g) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) := by
  classical
  set A := Algebra.adjoin ℤ ({g⁻¹} : Set FF) with hA
  obtain ⟨P, hP, hPx⟩ : IsIntegral A x := (mem_chartAlg_iff ℤ FF).mp hx

  choose lift hlift using fun a : A => exists_ofPowerSeries_eq_of_mem_adjoin p g hg (a : FF) a.2
  have hinj := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
  let L : A →+* PowerSeries ℚ :=
    { toFun := lift
      map_one' := hinj (by rw [hlift, map_one]; rfl)
      map_mul' := fun a b => hinj (by rw [hlift, map_mul, hlift, hlift]; rfl)
      map_zero' := hinj (by rw [hlift, map_zero]; rfl)
      map_add' := fun a b => hinj (by rw [hlift, map_add, hlift, hlift]; rfl) }
  have hL : ∀ a : A, HahnSeries.ofPowerSeries ℤ ℚ (L a) = ((a : FF) : LaurentSeries ℚ) := hlift
  have hcomp : (algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)).comp L =
      (valHom p).comp (algebraMap A FF) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, valHom_apply]
    exact hL a
  have hint : IsIntegral (PowerSeries ℚ) ((x : FF) : LaurentSeries ℚ) := by
    refine ⟨P.map L, hP.map L, ?_⟩
    rw [eval₂_map, hcomp, ← valHom_apply p x, ← hom_eval₂, hPx, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨y, hy⟩

theorem exists_ofPowerSeries_eq_of_mem_chartAlgInf_jFull (x : FF) (hx : x ∈ chartAlgInf ℤ FF (IgusaScheme.jFull p)) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) :=
  exists_ofPowerSeries_eq_of_mem_chartAlgInf p (IgusaScheme.jFull p)
    (by rw [IntermediateField.coe_inv, coe_jFull]; exact exists_ofPowerSeries_eq_jq_inv) x hx

theorem coe_inv_of_coe_eq_qExpand (jp : FF) (hjp : ((jp : FF) : LaurentSeries ℚ) = qExpand ℚ p jq) :
    ((jp⁻¹ : FF) : LaurentSeries ℚ) = qExpand ℚ p (jq)⁻¹ := by
  rw [IntermediateField.coe_inv, hjp, map_inv₀]

theorem exists_ofPowerSeries_eq_of_mem_chartAlgInf_of_coe_eq_qExpand (jp : FF)
    (hjp : ((jp : FF) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (x : FF) (hx : x ∈ chartAlgInf ℤ FF jp) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) :=
  exists_ofPowerSeries_eq_of_mem_chartAlgInf p jp
    (by rw [coe_inv_of_coe_eq_qExpand p jp hjp]; exact exists_ofPowerSeries_eq_qExpand p exists_ofPowerSeries_eq_jq_inv)
    x hx

theorem coeff_zero_jFull_inv : (((IgusaScheme.jFull p)⁻¹ : FF) : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [IntermediateField.coe_inv, coe_jFull, coeff_zero_jq_inv]

theorem coeff_zero_inv_of_coe_eq_qExpand (jp : FF) (hjp : ((jp : FF) : LaurentSeries ℚ) = qExpand ℚ p jq) :
    ((jp⁻¹ : FF) : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [coe_inv_of_coe_eq_qExpand p jp hjp, coeff_zero_qExpand, coeff_zero_jq_inv]

theorem coeff_zero_mul_of_mem_chartAlgInf (g : FF)
    (hg : ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = ((g⁻¹ : FF) : LaurentSeries ℚ))
    (x x' : FF) (hx : x ∈ chartAlgInf ℤ FF g) (hx' : x' ∈ chartAlgInf ℤ FF g) :
    ((x * x' : FF) : LaurentSeries ℚ).coeff 0 = (x : LaurentSeries ℚ).coeff 0 * (x' : LaurentSeries ℚ).coeff 0 := by
  rw [MulMemClass.coe_mul]
  exact coeff_zero_mul_of_ofPowerSeries (exists_ofPowerSeries_eq_of_mem_chartAlgInf p g hg x hx)
    (exists_ofPowerSeries_eq_of_mem_chartAlgInf p g hg x' hx')

end Chart

end G4INST
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive.G4INST"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive.G4INST"

namespace G4INST

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u

theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] : IsDominant (ιFin R F j) := by
  haveI : Nonempty (XFin R F j) := inferInstanceAs (Nonempty (PrimeSpectrum (chartAlgFin R F j)))
  refine ⟨?_⟩
  show Dense (Set.range (ιFin R F j).base)
  exact (ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

theorem hom_ext_of_ιFin_comp_eq (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (ιFin R F j) hFin

theorem nonunits_iff_of_mem_iff {F : Type*} [Field F] (W W' : ValuationSubring F) (σ : F ≃+* F)
    (hW : ∀ f, f ∈ W ↔ σ f ∈ W') (f : F) : f ∈ W.nonunits ↔ σ f ∈ W'.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hW, map_inv₀,
    (map_eq_zero_iff σ σ.injective)]

theorem mul_mem_nonunits {F : Type*} [Field F] (W : ValuationSubring F) {x y : F} (hx : x ∈ W)
    (hy : y ∈ W.nonunits) : x * y ∈ W.nonunits := by
  obtain ⟨hy', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨mul_mem hx hy', ?_⟩
  have : (⟨x * y, mul_mem hx hy'⟩ : W) = ⟨x, hx⟩ * ⟨y, hy'⟩ := rfl
  rw [this]
  exact Ideal.mul_mem_left _ _ hm

theorem chartAlgInf_le {F : Type} [Field F] [Algebra ℤ F] (j : F) [Fact (j ≠ 0)] (W : ValuationSubring F)
    (hj : j⁻¹ ∈ W) {x : F} (hx : x ∈ chartAlgInf ℤ F j) : x ∈ W := by
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at hx
  have hle : ∀ y ∈ Algebra.adjoin ℤ ({j⁻¹} : Set F), y ∈ W := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; subst hz; exact hj
    | algebraMap c => simpa using intCast_mem W c
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  let i : ↥(Algebra.adjoin ℤ ({j⁻¹} : Set F)) →+* W :=
    { toFun := fun y => ⟨y, hle y y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  obtain ⟨P, hPm, hPx⟩ := hx
  have hint : IsIntegral W x := by
    refine ⟨P.map i, hPm.map i, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := F)).mp hint
  rw [← hy]
  exact y.2

end G4INST
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive.G4INST"

open G4INST in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (φ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ).coeff 0) :
    ∃ (w : DRModel p ≅ DRModel p) (θ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))),
      w.hom ≫ DRModel.toBase p = DRModel.toBase p ∧
      w.hom ≫ w.hom = 𝟙 (DRModel p) ∧
      TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≫ w.hom =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
      (∀ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), θ (θ x) = x) ∧
      (∀ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
          ((θ x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) ∈ W₁ ↔
            ((x : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) ∈ W₀) ∧
      ((θ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) :
          ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) ∧
      ∃ ψ₀ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ,
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
              TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ≫ w.hom =
          Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫
            TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
        (∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ₀ a) ∧
        (∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
            (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ₀ a) := by

  let F : Type := ↥(modularFunctionFieldFull p)
  let j : F := (IgusaScheme.jFull p : F)
  let j' : F := (jp : F)

  obtain ⟨-, σ, hσj, hσj', hσσ, hW⟩ :=
    ModularCurve.DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap p jp hjp W₀ W₁ hp₀ hp₁ hne hgen
      hcomplete ht
  have hj'0 : j' ≠ 0 := by
    intro h0
    apply IgusaScheme.jFull_ne_zero p
    have : σ (IgusaScheme.jFull p) = 0 := by rw [hσj]; exact h0
    exact (map_eq_zero_iff σ σ.injective).mp this
  haveI hfact : Fact (j' ≠ 0) := ⟨hj'0⟩

  obtain ⟨t, eFin, eInf, heFin, heInf, ht_over, ht_fin, ht_inf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq ℤ F F j j' (σ.restrictScalars ℤ) hσj
  obtain ⟨t', eFin', eInf', heFin', heInf', -, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq ℤ F F j' j (σ.restrictScalars ℤ) hσj'

  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ℤ F j) := TwoChartIntegralModel.isIntegral ℤ F j
  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ℤ F j') := TwoChartIntegralModel.isIntegral ℤ F j'
  haveI : IsProper (toBase ℤ F j) := IgusaScheme.isProper_toBase_int p
  haveI : IsSeparated (toBase ℤ F j) := inferInstance
  haveI : IsSeparated (toBase ℤ F j') := by
    have e : toBase ℤ F j' = t.inv ≫ toBase ℤ F j := by rw [← ht_over, Iso.inv_hom_id_assoc]
    rw [e]; infer_instance
  obtain ⟨-, hftI⟩ := IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf p
  haveI : Algebra.FiniteType ℤ (chartAlgInf ℤ F j) := hftI
  haveI : Algebra.FiniteType ℤ (chartAlgInf ℤ F j') := by
    refine hftI.of_surjective eInf (fun y => ⟨eInf' y, Subtype.ext ?_⟩)
    rw [heInf, heInf']
    exact hσσ _

  have hfin : j' ∈ chartAlgFin ℤ F j := jp.2
  have hfin' : j ∈ chartAlgFin ℤ F j' := by
    have h := (eFin jp).2
    rw [heFin] at h
    change σ (jp : F) ∈ chartAlgFin ℤ F j' at h
    rwa [hσj'] at h
  obtain ⟨hvis, hvis'⟩ :=
    ModularCurve.forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand p p (jp : F) hjp

  obtain ⟨c, ιF, s, ψ, hιF, hιFbij, hs, hψ, hc_over, hc_fin, hc_inf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem ℤ F j j'
      hfin hfin' hvis hvis'

  let w : DRModel p ≅ DRModel p := c ≪≫ t.symm
  have h1 : w.hom ≫ toBase ℤ F j = toBase ℤ F j := by
    show (c.hom ≫ t.inv) ≫ toBase ℤ F j = toBase ℤ F j
    have htinv : t.inv ≫ toBase ℤ F j = toBase ℤ F j' := by rw [← ht_over, Iso.inv_hom_id_assoc]
    rw [Category.assoc, htinv, hc_over]

  let θ : chartAlgFin ℤ F j →ₐ[ℤ] chartAlgFin ℤ F j := ιF.comp eFin
  have hθval : ∀ x : chartAlgFin ℤ F j, ((θ x : chartAlgFin ℤ F j) : F) = σ x := by
    intro x
    show ((ιF (eFin x) : chartAlgFin ℤ F j) : F) = σ x
    rw [hιF, heFin]
    rfl
  have hθθ : θ.comp θ = AlgHom.id ℤ _ := by
    ext x
    rw [AlgHom.comp_apply, hθval, hθval, hσσ]
    rfl
  have hwFin : ιFin ℤ F j ≫ w.hom = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ ιFin ℤ F j := by
    show ιFin ℤ F j ≫ (c.hom ≫ t.inv) = _
    rw [← Category.assoc, hc_fin, Category.assoc, ← ht_fin, ← Category.assoc, ← Spec.map_comp]
    rfl

  obtain ⟨hC4a, hC4b⟩ :=
    ModularCurve.DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime p jp hjp W₀ W₁ hp₀ hp₁ hne hgen
      hcomplete ht φ hφ

  have hjinv : j⁻¹ ∈ W₀ := by
    have h := (hgen 0 Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).2
    rwa [Polynomial.eval₂_X] at h
  have hAW : ∀ x : F, x ∈ chartAlgInf ℤ F j → x ∈ W₀ := fun x hx => G4INST.chartAlgInf_le j W₀ hjinv hx

  have hσnu : ∀ f : F, f ∈ W₁.nonunits ↔ σ f ∈ W₀.nonunits :=
    G4INST.nonunits_iff_of_mem_iff W₁ W₀ σ.toRingEquiv hW

  have hPSj : ∀ x : F, x ∈ chartAlgInf ℤ F j →
      ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) :=
    fun x hx => G4INST.exists_ofPowerSeries_eq_of_mem_chartAlgInf_jFull p x hx
  have hPSj' : ∀ x : F, x ∈ chartAlgInf ℤ F j' →
      ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) :=
    fun x hx => G4INST.exists_ofPowerSeries_eq_of_mem_chartAlgInf_of_coe_eq_qExpand p j' hjp x hx
  have hPSmul : ∀ {x x' : LaurentSeries ℚ}, (∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x) →
      (∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x') →
      ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x * x' := by
    rintro x x' ⟨y, rfl⟩ ⟨y', rfl⟩; exact ⟨y * y', map_mul _ _ _⟩
  have hPSpow : ∀ {x : LaurentSeries ℚ}, (∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x) →
      ∀ n : ℕ, ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = x ^ n := by
    rintro x ⟨y, rfl⟩ n; exact ⟨y ^ n, map_pow _ _ _⟩

  have hcoeff1 : ∀ (g a : F), (∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = ((g⁻¹ : F) : LaurentSeries ℚ)) →
      ((g⁻¹ : F) : LaurentSeries ℚ).coeff 0 = 0 →
      (∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (a : LaurentSeries ℚ)) →
      ((1 + g⁻¹ * a : F) : LaurentSeries ℚ).coeff 0 = 1 := by
    intro g a hg hg0 ha
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one, HahnSeries.coeff_add,
      G4INST.coeff_zero_mul_of_ofPowerSeries hg ha, hg0, zero_mul, add_zero]
    simp

  obtain ⟨a₀, hs_eq⟩ := hs
  have hs_coeff : ((s : F) : LaurentSeries ℚ).coeff 0 = 1 := by
    have : (s : F) = 1 + j⁻¹ * (a₀ : F) := by rw [hs_eq]; rfl
    rw [this]
    exact hcoeff1 j a₀ (hPSj _ (jInvChartInf ℤ F j).2) (G4INST.coeff_zero_jFull_inv p) (hPSj _ a₀.2)
  have hφs : φ s = 1 := by
    have h := hφ s
    rw [hs_coeff] at h
    exact_mod_cast h

  have hunit : IsUnit (φ.toRingHom s) := by
    rw [show φ.toRingHom s = φ s from rfl, hφs]; exact isUnit_one
  let φt : Localization.Away s →+* ℤ := IsLocalization.Away.lift s hunit
  have hφt : ∀ a, φt (algebraMap _ (Localization.Away s) a) = φ a := fun a =>
    IsLocalization.Away.lift_eq s hunit a
  let ψ₀ : chartAlgInf ℤ F j →ₐ[ℤ] ℤ := ((φt.comp ψ.toRingHom).comp eInf.toRingHom).toIntAlgHom
  have hψ₀ : ∀ (a : chartAlgInf ℤ F j) (n : ℕ) (z : chartAlgInf ℤ F j),
      ψ (eInf a) * algebraMap _ (Localization.Away s) (s ^ n) = algebraMap _ (Localization.Away s) z →
      ψ₀ a = φ z := by
    intro a n z h
    have h' := congrArg φt h
    rw [map_mul, hφt, hφt, map_pow, hφs, one_pow, mul_one] at h'
    exact h'
  refine ⟨w, θ, h1, ?_, hwFin, ?_, ?_, ?_, ψ₀, ?_, ?_, ?_⟩
  ·
    refine G4INST.hom_ext_of_ιFin_comp_eq ℤ F j (w.hom ≫ w.hom) (𝟙 _) (toBase ℤ F j)
      (by rw [Category.assoc, h1, h1, Category.id_comp]) ?_
    rw [Category.comp_id, ← Category.assoc, hwFin, Category.assoc, hwFin, ← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom θ.toRingHom ≫ CommRingCat.ofHom θ.toRingHom = 𝟙 _ := by
      rw [← CommRingCat.ofHom_comp]
      change CommRingCat.ofHom (θ.comp θ).toRingHom = _
      rw [hθθ]
      rfl
    rw [this, Spec.map_id, Category.id_comp]
  ·
    intro x
    have := congrArg (fun f : chartAlgFin ℤ F j →ₐ[ℤ] chartAlgFin ℤ F j => f x) hθθ
    simpa using this
  ·
    intro x
    rw [hθval, hW, hσσ]
  ·
    show ((θ (TwoChartIntegralModel.jChartFin ℤ F j) : chartAlgFin ℤ F j) : F) = j'
    rw [hθval]
    exact hσj
  ·
    have hφfac : CommRingCat.ofHom φ.toRingHom =
        CommRingCat.ofHom (algebraMap (chartAlgInf ℤ F j) (Localization.Away s)) ≫ CommRingCat.ofHom φt := by
      rw [← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
    have hψ₀fac : CommRingCat.ofHom ψ₀.toRingHom =
        CommRingCat.ofHom eInf.toRingHom ≫ CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom φt := by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]; rfl
    show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf ℤ F j) ≫ (c.hom ≫ t.inv) = _
    rw [hφfac, hψ₀fac]
    simp only [Spec.map_comp, Category.assoc]
    rw [reassoc_of% hc_inf, ← ht_inf]
  ·
    intro a ha
    obtain ⟨n, z, hz, hψz⟩ := hψ (eInf a)
    rw [hψ₀ a n z hψz]
    apply hC4a
    rw [← hz, heInf]
    exact G4INST.mul_mem_nonunits W₀ (pow_mem (hAW _ s.2) n) ((hσnu a).mp ha)
  ·
    obtain ⟨b, hb, hpb⟩ := hC4b
    obtain ⟨s₁, hs₁, ⟨a₁, ha₁, hs₁eq⟩, hmem⟩ := hvis (eInf b) (eInf b).2
    refine ⟨⟨s₁ * (eInf b : F), hmem⟩, ?_, ?_⟩
    · show s₁ * (eInf b : F) ∈ W₀.nonunits
      rw [heInf]
      exact G4INST.mul_mem_nonunits W₀ (hAW _ hs₁) ((hσnu b).mp hb)
    · obtain ⟨n, z, hz, hψz⟩ := hψ (eInf ⟨s₁ * (eInf b : F), hmem⟩)
      rw [hψ₀ _ n z hψz]

      have e2 : ((eInf ⟨s₁ * (eInf b : F), hmem⟩ : chartAlgInf ℤ F j') : F) = (eInf ⟨s₁, hs₁⟩ : F) * b := by
        rw [heInf ⟨s₁ * (eInf b : F), hmem⟩, heInf ⟨s₁, hs₁⟩]
        change σ (s₁ * (eInf b : F)) = σ s₁ * b
        rw [map_mul, heInf b]
        change σ s₁ * σ (σ (b : F)) = σ s₁ * b
        rw [hσσ]
      have hzF : (z : F) = (s : F) ^ n * ((eInf ⟨s₁, hs₁⟩ : F) * b) := by rw [← hz, e2]
      have hσs₁ : ((eInf ⟨s₁, hs₁⟩ : F) : LaurentSeries ℚ).coeff 0 = 1 := by
        have e1 : (eInf ⟨s₁, hs₁⟩ : F) = 1 + j'⁻¹ * (eInf ⟨a₁, ha₁⟩ : F) := by
          rw [heInf, heInf]
          change σ s₁ = 1 + j'⁻¹ * σ a₁
          rw [hs₁eq, map_add, map_one, map_mul, map_inv₀, hσj]
        rw [e1]
        exact hcoeff1 j' _ (hPSj' _ (jInvChartInf ℤ F j').2) (G4INST.coeff_zero_inv_of_coe_eq_qExpand p j' hjp)
          (hPSj' _ (eInf ⟨a₁, ha₁⟩).2)
      have hzcoeff : ((z : F) : LaurentSeries ℚ).coeff 0 = ((b : F) : LaurentSeries ℚ).coeff 0 := by
        rw [hzF, MulMemClass.coe_mul, SubmonoidClass.coe_pow, MulMemClass.coe_mul]
        rw [G4INST.coeff_zero_mul_of_ofPowerSeries (hPSpow (hPSj _ s.2) n) (hPSmul (hPSj' _ (eInf ⟨s₁, hs₁⟩).2) (hPSj _ b.2)),
          G4INST.coeff_zero_mul_of_ofPowerSeries (hPSj' _ (eInf ⟨s₁, hs₁⟩).2) (hPSj _ b.2), hσs₁, one_mul]
        have hspow : ∀ m : ℕ, (((s : F) : LaurentSeries ℚ) ^ m).coeff 0 = 1 := by
          intro m
          induction m with
          | zero => simp
          | succ k ih =>
            rw [pow_succ, G4INST.coeff_zero_mul_of_ofPowerSeries (hPSpow (hPSj _ s.2) k) (hPSj _ s.2), ih,
              hs_coeff, one_mul]
        rw [hspow n, one_mul]
      have hφz : φ z = φ b := by
        have h1 := hφ z
        have h2 := hφ b
        rw [hzcoeff, ← h2] at h1
        exact_mod_cast h1
      rwa [hφz]

end S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive (solution)

-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e9c447bc-782e-57eb-9b14-af061d0b5957

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_finite_etale_quotient_span_aeval_chartAlgFin
import Theorems.Thm_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
import Theorems.Thm_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.coe_jqNGen ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel Polynomial AlgebraicGeometry.Polynomial"
open scoped MatrixGroups

set_option maxHeartbeats 3200000

noncomputable section

namespace SNearAlg

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

private def toZ (q : ℕ) [Fact q.Prime] : R q →+* ZMod q :=
  have hq : (q : ℕ).Prime := Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (g := Int.castRingHom (ZMod q)) (fun y => by
    rw [isUnit_iff_ne_zero, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := y.2
    rwa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] at this)

private theorem toZ_comp_algebraMap (q : ℕ) [Fact q.Prime] : (toZ q).comp (algebraMap ℤ (R q)) = Int.castRingHom (ZMod q) :=
  RingHom.ext_int _ _

private theorem isCoprime_map_of_monic (q : ℕ) [Fact q.Prime] (p₁ p₂ : ℤ[X]) (h₁ : p₁.Monic)
    (h : IsCoprime (p₁.map (Int.castRingHom (ZMod q))) (p₂.map (Int.castRingHom (ZMod q)))) :
    IsCoprime (p₁.map (algebraMap ℤ (R q))) (p₂.map (algebraMap ℤ (R q))) := by
  have hq : (q : ℕ).Prime := Fact.out
  haveI : IsLocalRing (R q) := GaloisRep.ratLocalizedAt.isLocalRing hq
  refine Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker (toZ q) ?_ _ _ (h₁.map _) ?_
  · rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_natCast]
    exact ZMod.natCast_self q
  · rwa [Polynomial.map_map, Polynomial.map_map, toZ_comp_algebraMap]

private theorem sup_span_aeval_eq_top {T S : Type*} [CommRing T] [CommRing S] [Algebra T S] (x : S) {f g : T[X]}
    (h : IsCoprime f g) : Ideal.span {aeval x f} ⊔ Ideal.span {aeval x g} = (⊤ : Ideal S) := by
  obtain ⟨a, b, hab⟩ := h
  rw [Ideal.eq_top_iff_one]
  have : (1 : S) = aeval x a * aeval x f + aeval x b * aeval x g := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

private theorem sup_span_aeval_eq_top_int (q : ℕ) [Fact q.Prime] {S : Type*} [CommRing S] [Algebra (R q) S] (x : S) (p₁ p₂ : ℤ[X]) (h₁ : p₁.Monic)
    (h : IsCoprime (p₁.map (Int.castRingHom (ZMod q))) (p₂.map (Int.castRingHom (ZMod q)))) :
    Ideal.span {aeval x p₁} ⊔ Ideal.span {aeval x p₂} = (⊤ : Ideal S) := by
  have := sup_span_aeval_eq_top x (isCoprime_map_of_monic q p₁ p₂ h₁ h)
  rwa [Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap] at this

private def twist (q : ℕ) (g : ℤ[X]) (D : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (D + 1), C (g.coeff k * (q : ℤ) ^ (12 * k)) * Polynomial.X ^ (D - k)

private theorem twist_map (q : ℕ) (g : ℤ[X]) (D : ℕ) (hq : (q : ZMod q) = 0) :
    (twist q g D).map (Int.castRingHom (ZMod q)) = C ((g.map (Int.castRingHom (ZMod q))).coeff 0) * Polynomial.X ^ D := by
  rw [twist, Polynomial.map_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Polynomial.map_mul, Polynomial.map_pow]
  · intro k _
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hq,
      zero_pow (by omega), mul_zero, C_0, zero_mul]

private theorem aeval_twist (q : ℕ) {S : Type*} [CommRing S] (v v' : S) (hvv' : v * v' = (q : S) ^ 12)
    (g : ℤ[X]) (D : ℕ) (hD : g.natDegree ≤ D) :
    aeval v (twist q g D) = v ^ D * aeval v' g := by
  rw [twist, map_sum, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hD) v', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, aeval_X, aeval_C, zsmul_eq_mul, map_mul, eq_intCast, eq_intCast, Int.cast_pow, Int.cast_natCast]

  have : (q : S) ^ (12 * k) * v ^ (D - k) = v ^ D * v' ^ k := by
    rw [pow_mul, ← hvv', mul_pow]
    calc v ^ k * v' ^ k * v ^ (D - k) = (v ^ k * v ^ (D - k)) * v' ^ k := by ring
      _ = v ^ D * v' ^ k := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [mul_assoc, this]
  ring

end SNearAlg

end

open SNearAlg _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹)
    (v' : ↥(chartAlgFin p (ΓM M H) hj)) (hvv' : v * v' = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12)
    (A₀ B₀ n₀ : ℕ) :
    ∃ (b N₁ : ℕ) (_ : A₀ * b ^ n₀ + B₀ < N₁) (g : Fin N₁ → ℤ[X]) (rk : Fin N₁ → ℕ),
      (∀ i, (g i).Monic) ∧
      (∀ i, Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧
        Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i) ∧
      (∀ i, 1 ≤ rk i) ∧ (∀ i, rk i ≤ b) ∧
      (Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) ∧
      (∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v' (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) ∧
      (∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) := by
  classical
  have hq : (p : ℕ).Prime := Fact.out

  obtain ⟨avoid, havoid, c₀, hc₀, K, hN2⟩ := ModularCurve.XHDRModelAtP.exists_finite_etale_quotient_span_aeval_chartAlgFin p M H hpM hpM2 hHp hj 𝔛 v hv

  obtain ⟨D, Mb, g, hD2, hDN, hM, hmon, hirr, -, hcop, hav, h0⟩ :=
    Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime p n₀ A₀ B₀ K (c₀.natDegree + 1) avoid havoid
  have hndvd : ∀ i, ¬ g i ∣ c₀ := fun i hdvd => by
    have := Polynomial.natDegree_le_of_dvd hdvd hc₀
    rw [(hmon i).2] at this
    omega
  have hdeg1 : ∀ i, 1 ≤ (g i).natDegree := fun i => by rw [(hmon i).2]; omega
  have hB := fun i => hN2 (g i) (hmon i).1 (hdeg1 i) (hirr i) (hav i) (hndvd i)
  haveI hfin : ∀ i, Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).1
  haveI het : ∀ i, Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).2.1
  haveI hfree : ∀ i, Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).2.2.1

  have hX : ∀ i, IsCoprime ((g i).map (Int.castRingHom (ZMod p))) Polynomial.X := by
    intro i
    refine isCoprime_comm.mp ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr ?_)
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h0 i
  refine ⟨K * D, Mb, hM, g, fun i => Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}), fun i => (hmon i).1,
    fun i => ⟨hfin i, het i, hfree i, rfl⟩, fun i => (hB i).2.2.2.1, fun i => ?_, ?_, ?_, ?_⟩
  ·
    have := (hB i).2.2.2.2
    rwa [(hmon i).2] at this
  ·
    intro i j hij
    exact sup_span_aeval_eq_top_int p v (g i) (g j) (hmon i).1 (hcop i j hij)
  ·
    intro i j
    have hqA : (p : ZMod p) = 0 := ZMod.natCast_self p
    have hcop' : IsCoprime ((g i).map (Int.castRingHom (ZMod p))) ((twist p (g j) D).map (Int.castRingHom (ZMod p))) := by
      rw [twist_map p (g j) D hqA]
      refine (isCoprime_mul_unit_left_right ?_ _ _).mpr ((hX i).pow_right)
      refine isUnit_C.mpr (IsUnit.mk0 _ ?_)
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact h0 j
    have htop := sup_span_aeval_eq_top_int p v (g i) (twist p (g j) D) (hmon i).1 hcop'
    have hvv'A : (v : ↥(chartAlgFin p (ΓM M H) hj)) * v' = ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12 := hvv'
    rw [aeval_twist p v v' hvv'A (g j) D (le_of_eq (hmon j).2)] at htop

    refine top_le_iff.mp (htop.symm.le.trans (sup_le_sup_left ?_ _))
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  ·
    intro i
    have := sup_span_aeval_eq_top_int p v (g i) Polynomial.X (hmon i).1 (by rw [Polynomial.map_X]; exact hX i)
    rwa [aeval_X] at this

end S_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin (solution)

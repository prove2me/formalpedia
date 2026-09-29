-- Prove2me | solution 1 for ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d9f392ef-8074-5c67-828a-97ee925bacfa

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP.ModularCurve AlgebraicCurve Polynomial AlgebraicGeometry.Polynomial"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase modularFunctionFieldFull IgusaScheme.jFull IgusaScheme DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace SplitK
p2m_open "ModularCurve"

section Algebra

variable {A : Type} [CommRing A] (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p]

noncomputable def liftPoly (f : A →+* k[X]) : A ⊗[ℤ] k →+* k[X] :=
  (Algebra.TensorProduct.lift (Algebra.ofId k k[X]) f.toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom.comp
    (Algebra.TensorProduct.comm ℤ A k).toRingHom

theorem liftPoly_tmul (f : A →+* k[X]) (a : A) (x : k) : liftPoly k f (a ⊗ₜ x) = Polynomial.C x * f a := by
  dsimp only [liftPoly, RingHom.coe_comp, Function.comp_apply]
  erw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.lift_tmul]
  rw [Algebra.ofId_apply, Polynomial.algebraMap_eq]
  rfl

theorem natCast_tensor_eq_zero : ((p : ℕ) : A ⊗[ℤ] k) = 0 := by
  have : ((p : ℕ) : A ⊗[ℤ] k) = (1 : A) ⊗ₜ[ℤ] ((p : ℕ) : k) := by
    rw [← map_natCast (Algebra.TensorProduct.includeRight : k →ₐ[ℤ] A ⊗[ℤ] k)]
    rfl
  rw [this, CharP.cast_eq_zero, TensorProduct.tmul_zero]

theorem not_irreducibleSpace_primeSpectrum_tensor (𝔭₀ 𝔭₁ : Ideal A) (hmul : 𝔭₀ * 𝔭₁ ≤ Ideal.span {((p : ℕ) : A)})
    (f₀ f₁ : A →+* k[X]) (hf₀ : ∀ a ∈ 𝔭₀, f₀ a = 0) (hf₁ : ∀ a ∈ 𝔭₁, f₁ a = 0)
    (t₁ : A) (ht₁ : t₁ ∈ 𝔭₀) (ht₁' : f₁ t₁ ≠ 0) (t₀ : A) (ht₀ : t₀ ∈ 𝔭₁) (ht₀' : f₀ t₀ ≠ 0) :
    Nontrivial (A ⊗[ℤ] k) ∧ ¬ IrreducibleSpace (PrimeSpectrum (A ⊗[ℤ] k)) := by

  let ι : A →+* A ⊗[ℤ] k := (Algebra.TensorProduct.includeLeft : A →ₐ[ℤ] A ⊗[ℤ] k).toRingHom
  let Q₀ : Ideal (A ⊗[ℤ] k) := 𝔭₀.map ι
  let Q₁ : Ideal (A ⊗[ℤ] k) := 𝔭₁.map ι
  have hι : ∀ a : A, ι a = a ⊗ₜ 1 := fun a => rfl

  have hQ : Q₀ * Q₁ = ⊥ := by
    rw [← Ideal.map_mul, eq_bot_iff]
    refine (Ideal.map_mono hmul).trans ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast, natCast_tensor_eq_zero p k, Ideal.span_singleton_zero]

  let φ₀ : A ⊗[ℤ] k →+* k[X] := liftPoly k f₀
  let φ₁ : A ⊗[ℤ] k →+* k[X] := liftPoly k f₁
  have hφ : ∀ (f : A →+* k[X]) (a : A), (liftPoly k f) (ι a) = f a := by
    intro f a; rw [hι, liftPoly_tmul, map_one, one_mul]
  haveI : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  haveI : (RingHom.ker φ₁).IsPrime := RingHom.ker_isPrime φ₁
  let 𝔮₀ : PrimeSpectrum (A ⊗[ℤ] k) := ⟨RingHom.ker φ₀, inferInstance⟩
  let 𝔮₁ : PrimeSpectrum (A ⊗[ℤ] k) := ⟨RingHom.ker φ₁, inferInstance⟩
  have hQ₀ : Q₀ ≤ RingHom.ker φ₀ := by
    rw [Ideal.map_le_iff_le_comap]; intro a ha; rw [Ideal.mem_comap, RingHom.mem_ker, hφ]; exact hf₀ a ha
  have hQ₁ : Q₁ ≤ RingHom.ker φ₁ := by
    rw [Ideal.map_le_iff_le_comap]; intro a ha; rw [Ideal.mem_comap, RingHom.mem_ker, hφ]; exact hf₁ a ha
  have h₁ : ¬ Q₀ ≤ RingHom.ker φ₁ := fun h => ht₁' (by
    have := h (Ideal.mem_map_of_mem ι ht₁); rwa [RingHom.mem_ker, hφ] at this)
  have h₀ : ¬ Q₁ ≤ RingHom.ker φ₀ := fun h => ht₀' (by
    have := h (Ideal.mem_map_of_mem ι ht₀); rwa [RingHom.mem_ker, hφ] at this)

  refine ⟨φ₀.domain_nontrivial, ?_⟩
  intro hirr
  have hcov : PrimeSpectrum.zeroLocus (Q₀ : Set (A ⊗[ℤ] k)) ∪ PrimeSpectrum.zeroLocus (Q₁ : Set (A ⊗[ℤ] k)) = Set.univ := by
    rw [← PrimeSpectrum.zeroLocus_mul, hQ]
    exact PrimeSpectrum.zeroLocus_bot

  have hU : IsOpen (PrimeSpectrum.zeroLocus (Q₀ : Set (A ⊗[ℤ] k)))ᶜ := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hV : IsOpen (PrimeSpectrum.zeroLocus (Q₁ : Set (A ⊗[ℤ] k)))ᶜ := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have h1U : 𝔮₁ ∈ (PrimeSpectrum.zeroLocus (Q₀ : Set (A ⊗[ℤ] k)))ᶜ := fun h => h₁ ((PrimeSpectrum.mem_zeroLocus _ _).mp h)
  have h0V : 𝔮₀ ∈ (PrimeSpectrum.zeroLocus (Q₁ : Set (A ⊗[ℤ] k)))ᶜ := fun h => h₀ ((PrimeSpectrum.mem_zeroLocus _ _).mp h)
  obtain ⟨z, -, hzU, hzV⟩ := hirr.isPreirreducible_univ _ _ hU hV ⟨𝔮₁, Set.mem_univ _, h1U⟩ ⟨𝔮₀, Set.mem_univ _, h0V⟩
  have hz : z ∈ PrimeSpectrum.zeroLocus (Q₀ : Set (A ⊗[ℤ] k)) ∪ PrimeSpectrum.zeroLocus (Q₁ : Set (A ⊗[ℤ] k)) := by
    rw [hcov]; trivial
  exact hz.elim hzU hzV

end Algebra

section Chart

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]

abbrev Afin : Type := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

theorem X_sub_X_pow_sq_ne_zero (k : Type) [Field k] : (X : k[X]) - (X ^ p) ^ p ≠ 0 := by
  rw [← pow_mul]
  intro h
  have h1 : ((X : k[X]) - X ^ (p * p)).coeff 1 = 0 := by rw [h, coeff_zero]
  have hp2 : p * p ≠ 1 := by
    have := hp.out.two_le; nlinarith
  rw [coeff_sub, coeff_X_one, coeff_X_pow, if_neg (Ne.symm hp2), sub_zero] at h1
  exact one_ne_zero h1

theorem not_irreducibleSpace_primeSpectrum_chartAlgFin_tensor (k : Type) [Field k] [CharP k p] :
    Nontrivial (Afin p ⊗[ℤ] k) ∧ ¬ IrreducibleSpace (PrimeSpectrum (Afin p ⊗[ℤ] k)) := by
  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hne, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨𝔭₀, 𝔭₁, -, -, hmin, hne', ⟨e₀, he₀j, he₀jp⟩, ⟨e₁, he₁jp, he₁j⟩⟩ :=
    ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial p jp hjp W₀ W₁ hp₀ hp₁ hne hgen
      hcomplete ht hres₀ hres₁
  obtain ⟨hred, -, -, -⟩ := ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int p

  set I : Ideal (Afin p) := Ideal.span {((p : ℕ) : Afin p)} with hI
  have hrad : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).mpr hred
  have hmul : 𝔭₀ * 𝔭₁ ≤ I := by
    rw [← hrad.radical, ← Ideal.sInf_minimalPrimes, hmin]
    intro x hx
    rw [Submodule.mem_sInf]
    rintro q (rfl | rfl)
    · exact Ideal.mul_le_left hx
    · exact Ideal.mul_le_right hx

  let j : Afin p := TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let m : (ZMod p)[X] →+* k[X] := Polynomial.mapRingHom (algebraMap (ZMod p) k)
  have hm : Function.Injective m := Polynomial.map_injective _ (algebraMap (ZMod p) k).injective
  let f₀ : Afin p →+* k[X] := m.comp (e₀.toRingHom.comp (Ideal.Quotient.mk 𝔭₀))
  let f₁ : Afin p →+* k[X] := m.comp (e₁.toRingHom.comp (Ideal.Quotient.mk 𝔭₁))
  have hf₀ : ∀ a ∈ 𝔭₀, f₀ a = 0 := fun a ha => by
    show m (e₀ (Ideal.Quotient.mk 𝔭₀ a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
  have hf₁ : ∀ a ∈ 𝔭₁, f₁ a = 0 := fun a ha => by
    show m (e₁ (Ideal.Quotient.mk 𝔭₁ a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

  have e₀t₁ : e₀ (Ideal.Quotient.mk 𝔭₀ (jp - j ^ p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_pow, he₀jp, he₀j, sub_self]
  have e₁t₁ : e₁ (Ideal.Quotient.mk 𝔭₁ (jp - j ^ p)) = X - (X ^ p) ^ p := by
    rw [map_sub, map_pow, map_sub, map_pow, he₁jp, he₁j]
  have e₁t₀ : e₁ (Ideal.Quotient.mk 𝔭₁ (j - jp ^ p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_pow, he₁jp, he₁j, sub_self]
  have e₀t₀ : e₀ (Ideal.Quotient.mk 𝔭₀ (j - jp ^ p)) = X - (X ^ p) ^ p := by
    rw [map_sub, map_pow, map_sub, map_pow, he₀jp, he₀j]
  have ht₁ : jp - j ^ p ∈ 𝔭₀ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact e₀.injective (e₀t₁.trans (map_zero _).symm)
  have ht₀ : j - jp ^ p ∈ 𝔭₁ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact e₁.injective (e₁t₀.trans (map_zero _).symm)
  have ht₁' : f₁ (jp - j ^ p) ≠ 0 := by
    show m (e₁ (Ideal.Quotient.mk 𝔭₁ (jp - j ^ p))) ≠ 0
    rw [e₁t₁, map_ne_zero_iff m hm]; exact X_sub_X_pow_sq_ne_zero p (ZMod p)
  have ht₀' : f₀ (j - jp ^ p) ≠ 0 := by
    show m (e₀ (Ideal.Quotient.mk 𝔭₀ (j - jp ^ p))) ≠ 0
    rw [e₀t₀, map_ne_zero_iff m hm]; exact X_sub_X_pow_sq_ne_zero p (ZMod p)
  exact not_irreducibleSpace_primeSpectrum_tensor p k 𝔭₀ 𝔭₁ hmul f₀ f₁ hf₀ hf₁ _ ht₁ ht₁' _ ht₀ ht₀'

theorem not_irreducibleSpace_pullback_toBase (k : Type) [Field k] [CharP k p] :
    ¬ IrreducibleSpace ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
  intro hirr

  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  let ιF := TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  let e : pullback (ιF ≫ DRModel.toBase p) s ≅ Spec (CommRingCat.of (Afin p ⊗[ℤ] k)) :=
    (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) rfl) ≪≫
      pullbackSpecIso ℤ (Afin p) k
  let u : Spec (CommRingCat.of (Afin p ⊗[ℤ] k)) ⟶ pullback (DRModel.toBase p) s :=
    e.inv ≫ pullback.map (ιF ≫ DRModel.toBase p) s (DRModel.toBase p) s ιF (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion (pullback.map (ιF ≫ DRModel.toBase p) s (DRModel.toBase p) s ιF (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])) := by
    infer_instance
  haveI : IsOpenImmersion u := inferInstance
  obtain ⟨hnt, hne⟩ := not_irreducibleSpace_primeSpectrum_chartAlgFin_tensor p k
  haveI := hnt
  haveI : Nonempty ↥(Spec (CommRingCat.of (Afin p ⊗[ℤ] k))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Afin p ⊗[ℤ] k)))
  exact hne u.isOpenEmbedding.irreducibleSpace

end Chart

end ModularCurve.SplitK

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP.ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (k : Type) [Field k] [CharP k p] :
    ¬ IrreducibleSpace ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) :=
  ModularCurve.SplitK.not_irreducibleSpace_pullback_toBase p k

end S_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP
end P2MW
export P2MW.S_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP (solution)

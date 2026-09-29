-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e6592731-6bc2-550b-9a8a-c1c46a1db5e1

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace A2Coef

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

section Naturality

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def coef (f : A →+ B) : H1 M H A →+ H1 M H B := AddMonoidHom.compHom f

@[scoped simp] theorem coef_apply (f : A →+ B) (φ : H1 M H A) : coef M H f φ = f.comp φ := rfl

theorem heckeT_comp (ℓ : ℕ) [NeZero ℓ] (f : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (f.comp φ) = f.comp (heckeT M H ℓ A φ) := by
  ext u
  show (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M H ℓ))
      (Additive.toMul u)).toAdd =
    f ((MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ))
      (Additive.toMul u)).toAdd)
  rw [MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [Subgroup.leftTransversals.diff, toAdd_prod, map_sum, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, AddMonoidHom.comp_apply]

theorem diamondRaw_comp (σ : Gamma0 M) (f : A →+ B) (φ : H1 M H A) :
    diamondRaw M H B σ (f.comp φ) = f.comp (diamondRaw M H A σ φ) := rfl

theorem isParabolicHom_comp (f : A →+ B) (φ : H1 M H A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M H) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M H) (f.comp φ) := fun γ hγ => by
  rw [AddMonoidHom.comp_apply, hφ γ hγ, map_zero]

end Naturality

section Coordinates

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
  (𝒪 : Type) [CommRing 𝒪] [Algebra ℤ_[p] 𝒪] [Module.Finite ℤ_[p] 𝒪] [Module.Free ℤ_[p] 𝒪]

abbrev basisO : Module.Basis (Module.Free.ChooseBasisIndex ℤ_[p] 𝒪) ℤ_[p] 𝒪 :=
  Module.Free.chooseBasis ℤ_[p] 𝒪

local notation "J" => Module.Free.ChooseBasisIndex ℤ_[p] 𝒪

def vco (j : J) : H1 M H 𝒪 →+ H1 M H ℤ_[p] :=
  coef M H ((basisO p 𝒪).coord j).toAddMonoidHom

theorem vco_apply (j : J) (v : H1 M H 𝒪) (γ : Additive ↥(GammaH M H)) :
    vco p M H 𝒪 j v γ = (basisO p 𝒪).repr (v γ) j := rfl

def incl : H1 M H ℤ_[p] →+ H1 M H 𝒪 := coef M H (algebraMap ℤ_[p] 𝒪).toAddMonoidHom

theorem incl_apply (u : H1 M H ℤ_[p]) (γ : Additive ↥(GammaH M H)) :
    incl p M H 𝒪 u γ = algebraMap ℤ_[p] 𝒪 (u γ) := rfl

theorem sum_smul_incl_vco (v : H1 M H 𝒪) :
    ∑ j, (basisO p 𝒪 j) • incl p M H 𝒪 (vco p M H 𝒪 j v) = v := by
  refine AddMonoidHom.ext fun γ => ?_
  rw [AddMonoidHom.finsetSum_apply]
  simp only [AddMonoidHom.smul_apply, incl_apply, vco_apply]
  conv_rhs => rw [← (basisO p 𝒪).sum_repr (v γ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, Algebra.smul_def, mul_comm]

theorem vco_sum_smul_incl (u : J → H1 M H ℤ_[p]) (j : J) :
    vco p M H 𝒪 j (∑ i, (basisO p 𝒪 i) • incl p M H 𝒪 (u i)) = u j := by
  refine AddMonoidHom.ext fun γ => ?_
  rw [vco_apply, AddMonoidHom.finsetSum_apply]
  simp only [AddMonoidHom.smul_apply, incl_apply]
  have : ∑ i, basisO p 𝒪 i • (algebraMap ℤ_[p] 𝒪) (u i γ) = ∑ i, (u i γ) • basisO p 𝒪 i :=
    Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, Algebra.smul_def, mul_comm]
  rw [this, (basisO p 𝒪).repr_sum_self]

theorem vco_smul (c : 𝒪) (v : H1 M H 𝒪) (j : J) :
    vco p M H 𝒪 j (c • v) = ∑ i, ((basisO p 𝒪).repr (c * basisO p 𝒪 i) j) • vco p M H 𝒪 i v := by
  refine AddMonoidHom.ext fun γ => ?_
  rw [vco_apply, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  simp only [AddMonoidHom.smul_apply, vco_apply, smul_eq_mul]
  conv_lhs => rw [← (basisO p 𝒪).sum_repr (v γ), Finset.mul_sum]
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem vco_opFamily (g : CohCarrier.Gen M S) (j : J) (v : H1 M H 𝒪) :
    vco p M H 𝒪 j (opFamily M H S 𝒪 g v) = opFamily M H S ℤ_[p] g (vco p M H 𝒪 j v) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show ((basisO p 𝒪).coord j).toAddMonoidHom.comp (heckeT M H ℓ 𝒪 v) =
      heckeT M H ℓ ℤ_[p] (((basisO p 𝒪).coord j).toAddMonoidHom.comp v)
    rw [heckeT_comp]
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show ((basisO p 𝒪).coord j).toAddMonoidHom.comp (heckeT M H q 𝒪 v) =
      heckeT M H q ℤ_[p] (((basisO p 𝒪).coord j).toAddMonoidHom.comp v)
    rw [heckeT_comp]
  | dia d => rfl

theorem vco_mem_parabolicHoms (j : J) (v : H1 M H 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    vco p M H 𝒪 j v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] :=
  isParabolicHom_comp M H _ v hv

theorem incl_mem_parabolicHoms (u : H1 M H ℤ_[p])
    (hu : u ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p]) :
    incl p M H 𝒪 u ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪 :=
  isParabolicHom_comp M H _ u hu

variable (Ta : Type) [AddCommGroup Ta] [Module ℤ_[p] Ta]
  (Φ : H1 M H ℤ_[p] →ₗ[ℤ_[p]] (Ta →ₗ[ℤ_[p]] ℤ_[p]))

def chi (v : H1 M H 𝒪) : Ta →ₗ[ℤ_[p]] 𝒪 :=
  ∑ j, (Φ (vco p M H 𝒪 j v)).smulRight (basisO p 𝒪 j)

theorem chi_apply (v : H1 M H 𝒪) (x : Ta) :
    chi p M H 𝒪 Ta Φ v x = ∑ j, Φ (vco p M H 𝒪 j v) x • basisO p 𝒪 j := by
  simp only [chi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply]

theorem chi_add (v w : H1 M H 𝒪) (x : Ta) :
    chi p M H 𝒪 Ta Φ (v + w) x = chi p M H 𝒪 Ta Φ v x + chi p M H 𝒪 Ta Φ w x := by
  simp only [chi_apply, map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]

theorem chi_smul (c : 𝒪) (v : H1 M H 𝒪) (x : Ta) :
    chi p M H 𝒪 Ta Φ (c • v) x = c * chi p M H 𝒪 Ta Φ v x := by
  rw [chi_apply, chi_apply, Finset.mul_sum]
  simp only [vco_smul, map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, Finset.sum_smul, smul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]
  conv_rhs => rw [← (basisO p 𝒪).sum_repr (c * basisO p 𝒪 i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm]

def PhiO : H1 M H 𝒪 →ₗ[𝒪] Module.Dual 𝒪 (𝒪 ⊗[ℤ_[p]] Ta) where
  toFun v := (chi p M H 𝒪 Ta Φ v).liftBaseChange 𝒪
  map_add' v w := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    show (chi p M H 𝒪 Ta Φ (v + w)).liftBaseChange 𝒪 (a ⊗ₜ x) =
      (chi p M H 𝒪 Ta Φ v).liftBaseChange 𝒪 (a ⊗ₜ x) + (chi p M H 𝒪 Ta Φ w).liftBaseChange 𝒪 (a ⊗ₜ x)
    simp only [LinearMap.liftBaseChange_tmul, chi_add, smul_add]
  map_smul' c v := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    show (chi p M H 𝒪 Ta Φ (c • v)).liftBaseChange 𝒪 (a ⊗ₜ x) =
      c • (chi p M H 𝒪 Ta Φ v).liftBaseChange 𝒪 (a ⊗ₜ x)
    simp only [LinearMap.liftBaseChange_tmul, chi_smul, smul_eq_mul]
    ring

theorem PhiO_tmul (v : H1 M H 𝒪) (a : 𝒪) (x : Ta) :
    PhiO p M H 𝒪 Ta Φ v (a ⊗ₜ x) = a * ∑ j, Φ (vco p M H 𝒪 j v) x • basisO p 𝒪 j :=
  (LinearMap.liftBaseChange_tmul 𝒪 (chi p M H 𝒪 Ta Φ v) a x).trans (by rw [chi_apply, smul_eq_mul])

variable {Φ}
variable (τ : CohCarrier.Gen M S → Module.End ℤ_[p] Ta)
  (hΦeq : ∀ (g : CohCarrier.Gen M S) (v : H1 M H ℤ_[p]),
    v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] →
      Φ (opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ τ g)
  (hΦsurj : (ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p]).map Φ = ⊤)
  (hΦinj : ∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p], Φ v = 0 → v = 0)

include hΦeq in

theorem PhiO_opFamily (g : CohCarrier.Gen M S) (v : H1 M H 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    PhiO p M H 𝒪 Ta Φ (opFamily M H S 𝒪 g v) =
      (PhiO p M H 𝒪 Ta Φ v) ∘ₗ (τ g).baseChange 𝒪 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have key : ∀ j : J, Φ (vco p M H 𝒪 j (opFamily M H S 𝒪 g v)) x =
      Φ (vco p M H 𝒪 j v) (τ g x) := fun j => by
    rw [vco_opFamily, hΦeq g _ (vco_mem_parabolicHoms p M H 𝒪 j v hv), LinearMap.comp_apply]
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, PhiO_tmul, key]

include hΦsurj in

theorem map_PhiO_eq_top :
    (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪).map (PhiO p M H 𝒪 Ta Φ) = ⊤ := by
  rw [eq_top_iff]
  rintro F -

  let F₁ : Ta →ₗ[ℤ_[p]] 𝒪 := (F.restrictScalars ℤ_[p]) ∘ₗ ((TensorProduct.mk ℤ_[p] 𝒪 Ta) 1)
  have hF₁ : ∀ x, F₁ x = F (1 ⊗ₜ x) := fun x => rfl
  have hcoord : ∀ j : J, ∃ u ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p],
      Φ u = ((basisO p 𝒪).coord j) ∘ₗ F₁ := fun j => by
    have : ((basisO p 𝒪).coord j) ∘ₗ F₁ ∈
        (ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p]).map Φ := by
      rw [hΦsurj]; exact Submodule.mem_top
    exact Submodule.mem_map.mp this
  choose u hu hΦu using hcoord
  refine ⟨∑ i, (basisO p 𝒪 i) • incl p M H 𝒪 (u i), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (incl_mem_parabolicHoms p M H 𝒪 (u i) (hu i))
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    have e1 : ∑ j, Φ (vco p M H 𝒪 j (∑ i, (basisO p 𝒪 i) • incl p M H 𝒪 (u i))) x • basisO p 𝒪 j =
        F₁ x := by
      conv_rhs => rw [← (basisO p 𝒪).sum_repr (F₁ x)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [vco_sum_smul_incl, hΦu, LinearMap.comp_apply, Module.Basis.coord_apply]
    have e2 : a * F₁ x = F (a ⊗ₜ x) := by
      rw [hF₁, ← smul_eq_mul, ← F.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [PhiO_tmul, e1, e2]

include hΦinj in

theorem PhiO_inj (v : H1 M H 𝒪) (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪)
    (h0 : PhiO p M H 𝒪 Ta Φ v = 0) : v = 0 := by
  have hcoef : ∀ (x : Ta) (j : J), Φ (vco p M H 𝒪 j v) x = 0 := by
    intro x
    have h1 : PhiO p M H 𝒪 Ta Φ v ((1 : 𝒪) ⊗ₜ x) = 0 := by rw [h0]; rfl
    simp only [PhiO_tmul, one_mul] at h1
    exact Fintype.linearIndependent_iff.mp (basisO p 𝒪).linearIndependent _ h1
  have hvj : ∀ j : J, vco p M H 𝒪 j v = 0 := fun j =>
    hΦinj _ (vco_mem_parabolicHoms p M H 𝒪 j v hv) (LinearMap.ext fun x => hcoef x j)
  rw [← sum_smul_incl_vco p M H 𝒪 v]
  simp [hvj]

end Coordinates

theorem main (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (𝒪 : Type) [CommRing 𝒪] [Algebra ℤ_[p] 𝒪] [Module.Finite ℤ_[p] 𝒪] [Module.Free ℤ_[p] 𝒪] :
    ∃ Φ : CohCarrier.H1 M H 𝒪 →ₗ[𝒪]
        Module.Dual 𝒪 (𝒪 ⊗[ℤ_[p]] TateModule p (ModularCurve.JH M H)),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          Φ (CohCarrier.opFamily M H S 𝒪 g v) =
            (Φ v) ∘ₗ (ModularCurve.tateGenOpH M H S p g).baseChange 𝒪) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪, Φ v = 0 → v = 0) := by
  refine (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH M p H S hin).elim
    fun Φ hΦ => ?_
  rcases hΦ with ⟨hΦeq, hΦsurj, hΦinj⟩
  refine ⟨PhiO p M H 𝒪 (TateModule p (ModularCurve.JH M H)) Φ, ?_, ?_, ?_⟩
  · exact PhiO_opFamily p M H S 𝒪 (TateModule p (ModularCurve.JH M H))
      (ModularCurve.tateGenOpH M H S p) hΦeq
  · exact map_PhiO_eq_top p M H 𝒪 (TateModule p (ModularCurve.JH M H)) hΦsurj
  · exact PhiO_inj p M H 𝒪 (TateModule p (ModularCurve.JH M H)) hΦinj

end A2Coef
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH.A2Coef"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH.A2Coef"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (𝒪 : Type) [CommRing 𝒪] [Algebra ℤ_[p] 𝒪] [Module.Finite ℤ_[p] 𝒪] [Module.Free ℤ_[p] 𝒪] :
    ∃ Φ : CohCarrier.H1 M H 𝒪 →ₗ[𝒪]
        Module.Dual 𝒪 (𝒪 ⊗[ℤ_[p]] TateModule p (ModularCurve.JH M H)),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          Φ (CohCarrier.opFamily M H S 𝒪 g v) =
            (Φ v) ∘ₗ (ModularCurve.tateGenOpH M H S p g).baseChange 𝒪) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪, Φ v = 0 → v = 0) :=
  A2Coef.main M p H S hin 𝒪

end S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH (solution)

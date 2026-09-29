-- Prove2me | solution 1 for ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/628fa4c5-6ff6-5c54-9b1f-8cbbc6997c43

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "periodOf periodLatticeOf periodOf_mem_periodLatticeOf period Period.IsParabolicHom Period.parabolicHoms exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Period.exists_basis_parabolicHoms_of_isAddTorsionFree periodMapOf_mem_parabolicHoms periodMapOf_apply_eq_periodOf"
namespace CpairK2Of
p2m_open "ModularCurve"

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem exists_isParabolicHom_apply_eq_periodOf :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ (CuspForm Γ 2), ModularCurve.Period.IsParabolicHom Γ Φ ∧
      ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.periodOf Γ γ := by
  refine ⟨AddMonoidHom.mk' (fun x => ModularCurve.periodOf Γ (Additive.toMul x)) ?_, ?_, fun γ => rfl⟩
  · intro x y
    apply LinearMap.ext
    intro f
    show ModularCurve.periodOf Γ (Additive.toMul x * Additive.toMul y) f =
      ModularCurve.periodOf Γ (Additive.toMul x) f + ModularCurve.periodOf Γ (Additive.toMul y) f
    rw [← ModularCurve.periodMapOf_apply_eq_periodOf, ← ModularCurve.periodMapOf_apply_eq_periodOf,
      ← ModularCurve.periodMapOf_apply_eq_periodOf, ofMul_mul, map_add]
  · intro γ hγ
    apply LinearMap.ext
    intro f
    show ModularCurve.periodOf Γ γ f = 0
    rw [← ModularCurve.periodMapOf_apply_eq_periodOf]
    exact ModularCurve.periodMapOf_mem_parabolicHoms Γ f γ hγ

theorem exists_basis_periodLatticeOf_card_eq (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (m : ℕ) (_ : Module.Basis (Fin m) ℤ (ModularCurve.periodLatticeOf Γ)),
      m = 2 * Module.finrank ℂ (CuspForm Γ 2) := by
  obtain ⟨m, c, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup Γ hΓ
  refine ⟨m, c, ?_⟩
  haveI : FiniteDimensional ℂ (CuspForm Γ 2) :=
    CuspForm.finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) 2
  let bR : Module.Basis (Fin m) ℝ (Module.Dual ℂ (CuspForm Γ 2)) :=
    Module.Basis.mk hli (by rw [hsp])
  have h1 : Module.finrank ℝ (Module.Dual ℂ (CuspForm Γ 2)) = m := by
    rw [Module.finrank_eq_card_basis bR, Fintype.card_fin]
  have h2 : Module.finrank ℝ (Module.Dual ℂ (CuspForm Γ 2)) =
      2 * Module.finrank ℂ (Module.Dual ℂ (CuspForm Γ 2)) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ (CuspForm Γ 2)), Complex.finrank_real_complex]
  rw [← h1, h2, Subspace.dual_finrank_eq]

theorem exists_basis_parabolicHoms_card_le (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (_ : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      n ≤ 2 * Module.finrank ℂ (CuspForm Γ 2) := by
  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  obtain ⟨_, -⟩ := hb ℤ
  refine ⟨n, b, ?_⟩
  have h1 : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [← h1]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ

def rel : Submodule ℤ (Γ →₀ ℤ) :=
  Submodule.span ℤ
    ({x | ∃ γ δ : Γ, x = Finsupp.single (γ * δ) 1 - Finsupp.single γ 1 - Finsupp.single δ 1} ∪
     {x | ∃ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 ∧ x = Finsupp.single γ 1})

abbrev Q : Type := (Γ →₀ ℤ) ⧸ rel Γ

def cls (γ : Γ) : Q Γ := Submodule.Quotient.mk (Finsupp.single γ 1)

omit [Γ.FiniteIndex] in
theorem cls_mul (γ δ : Γ) : cls Γ (γ * δ) = cls Γ γ + cls Γ δ := by
  rw [cls, cls, cls, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have : Finsupp.single (γ * δ) (1 : ℤ) - (Finsupp.single γ 1 + Finsupp.single δ 1) =
      Finsupp.single (γ * δ) 1 - Finsupp.single γ 1 - Finsupp.single δ 1 := by abel
  rw [this]
  exact Submodule.subset_span (Or.inl ⟨γ, δ, rfl⟩)

omit [Γ.FiniteIndex] in
theorem cls_eq_zero_of_trace (γ : Γ)
    (h : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : cls Γ γ = 0 := by
  rw [cls, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inr ⟨γ, h, rfl⟩)

omit [Γ.FiniteIndex] in

theorem rel_le_ker (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) :
    rel Γ ≤ LinearMap.ker (Finsupp.linearCombination ℤ
      (fun γ : Γ => (ψ : Additive Γ →+ ℤ) (Additive.ofMul γ))) := by
  apply Submodule.span_le.mpr
  rintro x (⟨γ, δ, rfl⟩ | ⟨γ, hγ, rfl⟩)
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul, ofMul_mul, map_add]
    abel
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single, one_smul]
    exact ψ.2 γ hγ

noncomputable def barOf (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Q Γ →ₗ[ℤ] ℤ :=
  (rel Γ).liftQ _ (rel_le_ker Γ ψ)

omit [Γ.FiniteIndex] in
@[scoped simp] theorem barOf_cls (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (γ : Γ) :
    barOf Γ ψ (cls Γ γ) = (ψ : Additive Γ →+ ℤ) (Additive.ofMul γ) := by
  show (rel Γ).liftQ _ (rel_le_ker Γ ψ) (Submodule.Quotient.mk (Finsupp.single γ 1)) = _
  rw [Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]

def ofBar (χ : Q Γ →ₗ[ℤ] ℤ) : ModularCurve.Period.parabolicHoms ℤ Γ ℤ :=
  ⟨{ toFun := fun x => χ (cls Γ (Additive.toMul x))
     map_zero' := by
       have h := cls_mul Γ 1 1
       rw [mul_one] at h
       have h0 : cls Γ 1 = 0 := by
         have := congrArg (fun t => t - cls Γ 1) h
         simp at this
         exact this.symm
       show χ (cls Γ 1) = 0
       rw [h0, map_zero]
     map_add' := fun x y => by
       show χ (cls Γ (Additive.toMul x * Additive.toMul y)) = _
       rw [cls_mul, map_add] },
   fun γ hγ => by
     show χ (cls Γ γ) = 0
     rw [cls_eq_zero_of_trace Γ γ hγ, map_zero]⟩

omit [Γ.FiniteIndex] in
@[scoped simp] theorem ofBar_apply (χ : Q Γ →ₗ[ℤ] ℤ) (γ : Γ) :
    (ofBar Γ χ : Additive Γ →+ ℤ) (Additive.ofMul γ) = χ (cls Γ γ) := rfl

noncomputable def dualEquiv :
    ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (Q Γ) where
  toFun := barOf Γ
  invFun := ofBar Γ
  map_add' ψ ψ' := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : Γ →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf Γ (ψ + ψ') (cls Γ γ) = n • (barOf Γ ψ (cls Γ γ) + barOf Γ ψ' (cls Γ γ))
    rw [barOf_cls, barOf_cls, barOf_cls]
    rfl
  map_smul' k ψ := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : Γ →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf Γ (k • ψ) (cls Γ γ) = n • (k • barOf Γ ψ (cls Γ γ))
    rw [barOf_cls, barOf_cls]
    rfl
  left_inv ψ := by
    apply Subtype.ext
    ext x
    show barOf Γ ψ (cls Γ (Additive.toMul x)) = _
    rw [barOf_cls]
    rfl
  right_inv χ := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : Γ →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf Γ (ofBar Γ χ) (cls Γ γ) = n • χ (cls Γ γ)
    rw [barOf_cls, ofBar_apply]

def perΛ (γ : Γ) : ModularCurve.periodLatticeOf Γ :=
  ⟨ModularCurve.periodOf Γ γ, ModularCurve.periodOf_mem_periodLatticeOf Γ γ⟩

omit [Γ.FiniteIndex] in
theorem span_perΛ : Submodule.span ℤ (Set.range (perΛ Γ)) = ⊤ := by
  apply Submodule.map_injective_of_injective (ModularCurve.periodLatticeOf Γ).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

theorem rel_le_ker_period :
    rel Γ ≤ LinearMap.ker (Finsupp.linearCombination ℤ (perΛ Γ)) := by
  obtain ⟨Φ, hΦpar, hΦ⟩ := exists_isParabolicHom_apply_eq_periodOf Γ
  have hval : ∀ γ, ((perΛ Γ γ : ModularCurve.periodLatticeOf Γ) :
      Module.Dual ℂ (CuspForm Γ 2)) = Φ (Additive.ofMul γ) :=
    fun γ => (hΦ γ).symm
  apply Submodule.span_le.mpr
  rintro x (⟨γ, δ, rfl⟩ | ⟨γ, hγ, rfl⟩)
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul]
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, hval, ofMul_mul, map_add]
    abel
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single, one_smul]
    apply Subtype.ext
    rw [hval, ZeroMemClass.coe_zero]
    exact hΦpar γ hγ

def phiBar : Q Γ →ₗ[ℤ] ModularCurve.periodLatticeOf Γ :=
  (rel Γ).liftQ _ (rel_le_ker_period Γ)

@[scoped simp] theorem phiBar_cls (γ : Γ) : phiBar Γ (cls Γ γ) = perΛ Γ γ := by
  show (rel Γ).liftQ _ (rel_le_ker_period Γ) (Submodule.Quotient.mk (Finsupp.single γ 1)) = _
  rw [Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]

theorem phiBar_surjective : Function.Surjective (phiBar Γ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_perΛ Γ, Submodule.span_le]
  rintro _ ⟨γ, rfl⟩
  exact ⟨cls Γ γ, phiBar_cls Γ γ⟩

theorem dual_ker_phiBar_eq_zero (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (χ : Module.Dual ℤ (LinearMap.ker (phiBar Γ))) : χ = 0 := by

  obtain ⟨m, c, hm⟩ := exists_basis_periodLatticeOf_card_eq Γ hΓ
  obtain ⟨n, b, hn⟩ := exists_basis_parabolicHoms_card_le Γ hΓ
  have hnm : n ≤ m := hm ▸ hn
  haveI : Module.Free ℤ (ModularCurve.periodLatticeOf Γ) := Module.Free.of_basis c
  haveI : Module.Finite ℤ (ModularCurve.periodLatticeOf Γ) := Module.Finite.of_basis c

  obtain ⟨sec, hsec⟩ := (phiBar Γ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (phiBar_surjective Γ))

  set K := LinearMap.ker (phiBar Γ) with hK
  have hsecapp : ∀ y, phiBar Γ (sec y) = y := fun y => by
    have := congrArg (fun f => f y) hsec
    simpa using this
  let split : Q Γ →ₗ[ℤ] ModularCurve.periodLatticeOf Γ × K :=
    LinearMap.prod (phiBar Γ)
      (LinearMap.codRestrict K (LinearMap.id - sec ∘ₗ phiBar Γ) (fun x => by
        simp [hK, LinearMap.mem_ker, map_sub, hsecapp]))
  let unsplit : ModularCurve.periodLatticeOf Γ × K →ₗ[ℤ] Q Γ :=
    sec ∘ₗ LinearMap.fst ℤ _ _ + K.subtype ∘ₗ LinearMap.snd ℤ _ _
  have h1 : ∀ x, unsplit (split x) = x := fun x => by
    simp [split, unsplit]
  have h2 : ∀ y, split (unsplit y) = y := by
    rintro ⟨y, k⟩
    have hk : phiBar Γ (k : Q Γ) = 0 := k.2
    apply Prod.ext
    · simp [split, unsplit, hsecapp, hk]
    · apply Subtype.ext
      simp [split, unsplit, hsecapp, hk]
  let e : Q Γ ≃ₗ[ℤ] ModularCurve.periodLatticeOf Γ × K :=
    { split with invFun := unsplit, left_inv := h1, right_inv := h2 }

  let eD : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ]
      Module.Dual ℤ (ModularCurve.periodLatticeOf Γ) × Module.Dual ℤ K :=
    (dualEquiv Γ).trans (e.symm.dualMap.trans (Module.dualProdDualEquivDual ℤ _ _).symm)

  haveI : Module.Finite ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) := Module.Finite.of_basis b
  haveI : Module.Free ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) := Module.Free.of_basis b
  haveI : Module.Finite ℤ (Module.Dual ℤ K) :=
    Module.Finite.of_surjective
      ((LinearMap.snd ℤ (Module.Dual ℤ (ModularCurve.periodLatticeOf Γ)) (Module.Dual ℤ K)).comp
        eD.toLinearMap)
      (fun χ => ⟨eD.symm (0, χ), by simp⟩)
  haveI : Module.Free ℤ (Module.Dual ℤ K) := inferInstance
  haveI : Module.Free ℤ (Module.Dual ℤ (ModularCurve.periodLatticeOf Γ)) :=
    Module.Free.of_basis c.dualBasis
  haveI : Module.Finite ℤ (Module.Dual ℤ (ModularCurve.periodLatticeOf Γ)) :=
    Module.Finite.of_basis c.dualBasis

  have hP : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hΛ : Module.finrank ℤ (Module.Dual ℤ (ModularCurve.periodLatticeOf Γ)) = m := by
    rw [Module.finrank_eq_card_basis c.dualBasis, Fintype.card_fin]
  have hsum := eD.finrank_eq
  rw [Module.finrank_prod, hP, hΛ] at hsum
  have hK0 : Module.finrank ℤ (Module.Dual ℤ K) = 0 := by omega
  have hsub : Subsingleton (Module.Dual ℤ K) := Module.finrank_zero_iff.mp hK0
  exact Subsingleton.elim _ _

theorem main (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (ModularCurve.periodLatticeOf Γ),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
        EV ψ ⟨ModularCurve.periodOf Γ δ, ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
          (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) := by
  obtain ⟨m, c, -⟩ := exists_basis_periodLatticeOf_card_eq Γ hΓ
  haveI : Module.Free ℤ (ModularCurve.periodLatticeOf Γ) := Module.Free.of_basis c
  obtain ⟨sec, hsec⟩ := (phiBar Γ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (phiBar_surjective Γ))
  have hsecapp : ∀ y, phiBar Γ (sec y) = y := fun y => by
    have := congrArg (fun f => f y) hsec
    simpa using this

  have key : ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x : Q Γ),
      barOf Γ ψ x = barOf Γ ψ (sec (phiBar Γ x)) := by
    intro ψ x
    have hx : x - sec (phiBar Γ x) ∈ LinearMap.ker (phiBar Γ) := by
      rw [LinearMap.mem_ker, map_sub, hsecapp, sub_self]
    have h0 := dual_ker_phiBar_eq_zero Γ hΓ ((barOf Γ ψ).comp (LinearMap.ker (phiBar Γ)).subtype)
    have := congrArg (fun f => f ⟨_, hx⟩) h0
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, map_sub,
      LinearMap.zero_apply] at this
    linarith
  let EV₀ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ]
      Module.Dual ℤ (ModularCurve.periodLatticeOf Γ) :=
    sec.dualMap ∘ₗ (dualEquiv Γ).toLinearMap
  have hEV₀ : ∀ ψ y, EV₀ ψ y = barOf Γ ψ (sec y) := fun ψ y => rfl
  have hval : ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
      EV₀ ψ (perΛ Γ δ) = (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) := by
    intro ψ δ
    rw [hEV₀, ← phiBar_cls, ← key, barOf_cls]
  have hinj : Function.Injective EV₀ := by
    intro ψ ψ' h
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    have h1 := hval ψ (Additive.toMul x)
    have h2 := hval ψ' (Additive.toMul x)
    rw [h] at h1
    rw [ofMul_toMul] at h1 h2
    rw [← h1, ← h2]
  have hsurj : Function.Surjective EV₀ := by
    intro μ
    refine ⟨ofBar Γ (μ ∘ₗ phiBar Γ), ?_⟩
    apply LinearMap.ext_on_range (span_perΛ Γ)
    intro δ
    rw [hval, ofBar_apply, LinearMap.comp_apply, phiBar_cls]
  refine ⟨LinearEquiv.ofBijective EV₀ ⟨hinj, hsurj⟩, fun ψ δ => ?_⟩
  rw [LinearEquiv.ofBijective_apply]
  exact hval ψ δ

end ModularCurve.CpairK2Of
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.ModularCurve.CpairK2Of"
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.ModularCurve.CpairK2Of"

theorem solution (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (ModularCurve.periodLatticeOf Γ),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
        EV ψ ⟨ModularCurve.periodOf Γ δ, ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
          (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) := by
  haveI : Γ.FiniteIndex := hΓ.finiteIndex
  exact ModularCurve.CpairK2Of.main Γ hΓ

end S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
end P2MW
export P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup (solution)

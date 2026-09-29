-- Prove2me | solution 1 for ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/420182b6-53d2-5b6f-953c-a2f13b596477

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
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
open CongruenceSubgroup Module

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "periodOf periodLatticeOf periodOf_mem_periodLatticeOf period Period.IsParabolicHom Period.parabolicHoms eq_zero_of_forall_re_periodOf_eq_zero finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Period.exists_basis_parabolicHoms_of_isAddTorsionFree periodMapOf_mem_parabolicHoms periodMapOf_apply_eq_periodOf"
namespace PeriodRealStructureOf
p2m_open "ModularCurve"

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

local notation "V" => CuspForm Γ 2
local notation "D" => Module.Dual ℂ (CuspForm Γ 2)

omit [Γ.FiniteIndex] in

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem fg_Gamma : Group.FG Γ := by
  haveI := fg_SL2Z
  infer_instance

omit [Γ.FiniteIndex] in

theorem addMonoidHom_eq_of_eqOn_gen {A : Type*} [AddCommGroup A] {S : Set Γ}
    (hS : Subgroup.closure S = ⊤) (φ ψ : Additive Γ →+ A)
    (h : ∀ s ∈ S, φ (Additive.ofMul s) = ψ (Additive.ofMul s)) : φ = ψ := by
  suffices H : ∀ γ ∈ Subgroup.closure S, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) by
    ext x
    exact H (Additive.toMul x) (by rw [hS]; exact Subgroup.mem_top _)
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => change φ 0 = ψ 0; rw [map_zero, map_zero]
  | mul y z _ _ hy hz =>
    have : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
    change φ (Additive.ofMul (y * z)) = ψ (Additive.ofMul (y * z))
    rw [this, map_add, map_add]
    exact congrArg₂ (· + ·) hy hz
  | inv y _ hy =>
    have : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
    change φ (Additive.ofMul y⁻¹) = ψ (Additive.ofMul y⁻¹)
    rw [this, map_neg, map_neg]
    exact congrArg Neg.neg hy

theorem finite_addMonoidHom_real : Module.Finite ℝ (Additive Γ →+ ℝ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma Γ)
  haveI : Fintype S := hSfin.fintype
  let res : (Additive Γ →+ ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun φ s => φ (Additive.ofMul (s : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective res ?_
  intro φ ψ hφψ
  refine addMonoidHom_eq_of_eqOn_gen Γ hS φ ψ fun s hs => ?_
  exact congrFun hφψ ⟨s, hs⟩

theorem exists_isParabolicHom_apply_eq_periodOf :
    ∃ Φ : Additive Γ →+ D, ModularCurve.Period.IsParabolicHom Γ Φ ∧
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

theorem finrank_parabolicHoms_real_le (hΓ : IsCongruenceSubgroup Γ) :
    Module.Finite ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ∧
      Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ≤ 2 * Module.finrank ℂ V := by
  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  obtain ⟨bR, -⟩ := hb ℝ
  refine ⟨Module.Finite.of_basis bR, ?_⟩
  rw [Module.finrank_eq_card_basis bR, ← Module.finrank_eq_card_basis b]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ

theorem main (hΓ : IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) : D)) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) : D)) = ⊤ := by
  classical
  haveI : FiniteDimensional ℂ V :=
    CuspForm.finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) 2

  obtain ⟨Φ, hΦpar, hΦ⟩ := exists_isParabolicHom_apply_eq_periodOf Γ
  set Λ : Submodule ℤ D := ModularCurve.periodLatticeOf Γ with hΛdef
  have hΦmem : ∀ x : Additive Γ, Φ x ∈ Λ := fun x => by
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl, hΦ]
    exact ModularCurve.periodOf_mem_periodLatticeOf Γ _

  let Φ' : Additive Γ →+ Λ := Φ.codRestrict Λ hΦmem
  have hΦ'coe : ∀ x, ((Φ' x : Λ) : D) = Φ x := fun x => rfl
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    have : ∀ y ∈ Λ, ∃ x, Φ x = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨Additive.ofMul γ, hΦ γ⟩
      | zero => exact ⟨0, map_zero Φ⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨c, rfl⟩ := hz
        exact ⟨a + c, map_add Φ a c⟩
      | smul m y _ hy =>
        obtain ⟨a, rfl⟩ := hy
        exact ⟨m • a, map_zsmul Φ m a⟩
    obtain ⟨x, hx⟩ := this y hy
    exact ⟨x, Subtype.ext hx⟩

  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma Γ)

  have hΛfg : Λ.FG := by
    refine Submodule.fg_def.mpr ⟨(fun s : Γ => ModularCurve.periodOf Γ s) '' S, hSfin.image _, ?_⟩
    rw [hΛdef]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · unfold ModularCurve.periodLatticeOf
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγ : γ ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top _
      induction hγ using Subgroup.closure_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | one =>
        rw [← hΦ]
        change Φ 0 ∈ _
        rw [map_zero]; exact Submodule.zero_mem _
      | mul y z _ _ hy hz =>
        rw [← hΦ] at hy hz ⊢
        have : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
        rw [this, map_add]
        exact Submodule.add_mem _ hy hz
      | inv y _ hy =>
        rw [← hΦ] at hy ⊢
        have : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
        rw [this, map_neg]
        exact Submodule.neg_mem _ hy
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  haveI : IsAddTorsionFree D := IsAddTorsionFree.of_isTorsionFree ℂ D
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'

  set n := Module.finrank ℤ Λ
  let b : Module.Basis (Fin n) ℤ Λ := Module.finBasis ℤ Λ

  have hU : Submodule.span ℝ (Set.range fun γ : Γ => ModularCurve.periodOf Γ γ) =
      (⊤ : Submodule ℝ D) := by
    by_contra hne
    obtain ⟨g, hg0, hUg⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)

    let G : Module.Dual ℂ D := Module.Dual.extendRCLike (𝕜 := ℂ) g
    obtain ⟨v, hv⟩ := (Module.evalEquiv ℂ V).surjective G
    have hGv : ∀ φ : D, G φ = φ v := fun φ => by
      rw [← hv, Module.evalEquiv_apply, Module.Dual.eval_apply]
    have hgre : ∀ φ : D, g φ = (φ v).re := fun φ => by
      rw [← hGv]
      exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) g φ).symm
    have hv0 : v = 0 := by
      refine ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero Γ v fun γ => ?_
      rw [← hgre]
      have := hUg (Submodule.subset_span ⟨γ, rfl⟩)
      simpa using this
    apply hg0
    ext φ
    rw [hgre, hv0, map_zero]
    simp

  haveI : Module.Finite ℝ (Additive Γ →+ ℝ) := finite_addMonoidHom_real Γ

  let ψ₀ : Fin n → (Additive Γ →+ ℝ) := fun i =>
    (Int.castAddHom ℝ).comp ((b.coord i).toAddMonoidHom.comp Φ')
  have hψ₀ : ∀ i x, ψ₀ i x = ((b.coord i (Φ' x) : ℤ) : ℝ) := fun i x => rfl
  have hψpar : ∀ i, ModularCurve.Period.IsParabolicHom Γ (ψ₀ i) := by
    intro i γ hγ
    have h0 : Φ' (Additive.ofMul γ) = 0 := Subtype.ext (by rw [hΦ'coe, hΦpar γ hγ]; rfl)
    rw [hψ₀, h0, map_zero, Int.cast_zero]
  let ψ : Fin n → ModularCurve.Period.parabolicHoms ℝ Γ ℝ := fun i => ⟨ψ₀ i, hψpar i⟩
  have hψli : LinearIndependent ℝ ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hc' : ∀ x : Additive Γ, ∑ i, c i * ((b.coord i (Φ' x) : ℤ) : ℝ) = 0 := by
      intro x
      have := congrArg (fun χ : ModularCurve.Period.parabolicHoms ℝ Γ ℝ =>
        ((χ : Additive Γ →+ ℝ) x)) hc
      simpa [ψ, hψ₀, Submodule.coe_sum, AddMonoidHom.finsetSum_apply] using this
    obtain ⟨x, hx⟩ := hΦ'surj (b j)
    have := hc' x
    rw [hx] at this
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using this
  obtain ⟨hparfin, hparle⟩ := finrank_parabolicHoms_real_le Γ hΓ
  haveI := hparfin
  have hn_le_par : n ≤ Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) := by
    simpa using hψli.fintype_card_le_finrank
  have hDfin : Module.finrank ℝ D = 2 * Module.finrank ℂ V := by
    rw [← Module.finrank_mul_finrank ℝ ℂ D, Complex.finrank_real_complex, Subspace.dual_finrank_eq]
  have hn_le : n ≤ Module.finrank ℝ D := by
    rw [hDfin]
    exact hn_le_par.trans hparle

  let w : Fin n → D := fun i => ((b i : Λ) : D)
  have hΛw : Submodule.span ℤ (Set.range w) = Λ := by
    have h := congrArg (Submodule.map Λ.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hΛ_le : ∀ y ∈ Λ, y ∈ Submodule.span ℝ (Set.range w) := by
    intro y hy
    rw [← hΛw] at hy
    exact Submodule.span_le_restrictScalars ℤ ℝ _ hy
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    rw [eq_top_iff, ← hU, Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    exact hΛ_le _ (ModularCurve.periodOf_mem_periodLatticeOf Γ γ)
  haveI : Module.Finite ℝ D := by
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_range w)
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ D := by
    refine le_antisymm (by simpa using hn_le) ?_
    have h1 := finrank_range_le_card (R := ℝ) w
    rw [Set.finrank, hspan, finrank_top] at h1
    exact h1
  exact ⟨n, b, linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard, hspan⟩

end ModularCurve.PeriodRealStructureOf

end

theorem solution (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) = ⊤ := by
  haveI : Γ.FiniteIndex := hΓ.finiteIndex
  exact ModularCurve.PeriodRealStructureOf.main Γ hΓ

end S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
end P2MW
export P2MW.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup (solution)

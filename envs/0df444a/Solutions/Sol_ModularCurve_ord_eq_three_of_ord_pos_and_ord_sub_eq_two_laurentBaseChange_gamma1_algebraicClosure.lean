-- Prove2me | solution 1 for ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1e109a5a-0444-59e3-8325-4799324db6be

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers
import Theorems.Thm_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq
import Theorems.Thm_ModularCurve_LevelN_Descent_fixer_le
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure.ModularCurve"
open scoped MatrixGroups IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jGen laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers LevelN.Descent.fixer_le JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace NoEllAux
p2m_open "ModularCurve"

theorem isDomain_levelN_ring (N : ℕ) [NeZero N] : IsDomain ↥(ModularCurve.LevelN.ring N) := by
  have h := WLight.levelN_structure_package N (fun τ => PeriodPair.ofTau τ) (fun τ => ⟨rfl, rfl⟩)
    (ModularCurve.LevelN.wp N) (fun v τ => rfl) (ModularCurve.LevelN.fricke N) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := h
  haveI : NoZeroDivisors ↥(ModularCurve.LevelN.ring N) := ⟨fun {a b} hab => by
    have := hdom a b a.2 b.2 (by rw [← Subalgebra.coe_mul, hab]; rfl)
    rcases this with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0⟩
  haveI : Nontrivial ↥(ModularCurve.LevelN.ring N) := inferInstance
  exact NoZeroDivisors.to_isDomain _

theorem mem_sup_zpowers_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ H ∨ -g ∈ H := by
  haveI hN : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute ((-1 : SL(2, ℤ)) ^ k) g := (Commute.neg_one_left g).zpow_left k
    rw [← hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  have hpm : ∀ n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)), n = 1 ∨ n = -1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_ofNat]
      simp
    · right
      rw [zpow_add, zpow_mul, zpow_ofNat, zpow_one]
      simp
  constructor
  · intro hg
    have hg' : g ∈ ((H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨h, hh, n, hn, rfl⟩ := Set.mem_mul.mp hg'
    rcases hpm n hn with rfl | rfl
    · left; simpa using hh
    · right; simpa using hh
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have : g = (-g) * (-1) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem ST_smul_ρ : (ModularGroup.S * ModularGroup.T) • UpperHalfPlane.ρ = UpperHalfPlane.ρ :=
  ModularGroup.stabilizer_ρ.mpr (by simp)

theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I :=
  ModularGroup.stabilizer_I.mpr (by simp)

end ModularCurve.NoEllAux

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC jGen laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers LevelN.Descent.fixer_le JOneES.exists_transcendental_finiteDimensional_laurentBaseChange" namespace NoEllAux end ModularCurve.NoEllAux
p2m_open_scoped "ModularCurve" in
open ModularCurve.NoEllAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem ModularCurve.NoEllAux.main
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    (0 < P.ord y → P.ord y = 3) ∧ (0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by
  classical
  haveI : IsDomain ↥(ModularCurve.LevelN.ring M) := isDomain_levelN_ring M
  let K : Type := FractionRing ↥(ModularCurve.LevelN.ring M)
  letI algCK : Algebra ℂ K := inferInstance
  haveI : IsScalarTower ℂ ↥(ModularCurve.LevelN.ring M) K := inferInstance
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    constructor
    intro x
    obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
    refine ⟨p, hp0, ?_⟩
    rw [Polynomial.aeval_def] at hp ⊢
    convert hp using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  let ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom
  have hΓM : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
    intro γ hγ
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]

  obtain ⟨Φ, E', hE'j, hE'Φ, hΦc, hΦy, hΦfix⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion M
      (CongruenceSubgroup.Gamma1 M) hΓM hT ι K

  obtain ⟨hst, σ, hσ, hker, hfix, htr, hfd, hdeg, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin M K

  have hM2 : 2 ≤ M := by omega
  obtain ⟨⟨W0, hW0, hD0⟩, ⟨W1728, hW1728, hD1728⟩⟩ :=
    ModularCurve.LevelN.exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers M hM2 K hst σ hσ hker
      hfix hfd hgal
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  let t : K := algebraMap ↥(ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)
  have hΦy' : Φ y = t := hΦy y hy
  let E : IntermediateField ℂ K := IntermediateField.adjoin ℂ (Set.range Φ)
  have hΦmem : ∀ f, Φ f ∈ E := fun f => IntermediateField.subset_adjoin ℂ _ ⟨f, rfl⟩
  let ΦE : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) →+* ↥E := Φ.codRestrict E hΦmem
  have hΦE : ∀ f, ((ΦE f : ↥E) : K) = Φ f := fun f => RingHom.codRestrict_apply Φ E hΦmem f
  have hcoeC : ∀ z : ℂ, ((algebraMap ℂ ↥E z : ↥E) : K) = algebraMap ℂ K z := fun _ => rfl
  letI algFE : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) ↥E := ΦE.toAlgebra
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQE : Algebra (AlgebraicClosure ℚ) ↥E := ((algebraMap ℂ ↥E).comp ι).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) ↥E := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (by
      change ((algebraMap ℂ ↥E (ι c) : ↥E) : K) = ((ΦE (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) c) : ↥E) : K)
      rw [hcoeC, hΦE, hΦc])
  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd

  have htr' : Transcendental ℂ (ΦE y) := fun h => htr (by
    have h' := IntermediateField.isAlgebraic_iff.mp h
    rwa [hΦE, hΦy'] at h')
  haveI := hfd
  have hEfd : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E)) ↥E := by

    have hlift : IntermediateField.lift (IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E)) = IntermediateField.adjoin ℂ ({t} : Set K) := by
      rw [IntermediateField.lift_adjoin_simple, hΦE, hΦy']
    have hle' : IntermediateField.adjoin ℂ ({t} : Set K) ≤ E := by rw [← hlift]; exact IntermediateField.lift_le _
    let E₂ : IntermediateField ↥(IntermediateField.adjoin ℂ ({t} : Set K)) K := IntermediateField.extendScalars hle'
    haveI hE₂ : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥E₂ := inferInstance
    let e₁ : ↥(IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E)) ≃ₐ[ℂ] ↥(IntermediateField.adjoin ℂ ({t} : Set K)) :=
      (IntermediateField.liftAlgEquiv _).trans (IntermediateField.equivOfEq hlift)
    let e₂ : ↥E₂ ≃+* ↥E := RingEquiv.refl _
    exact Module.Finite.of_equiv_equiv e₁.symm.toRingEquiv e₂ (by
      refine RingHom.ext fun w => Subtype.ext ?_
      have h1 : ∀ v : ↥(IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E)), ((e₁ v : ↥(IntermediateField.adjoin ℂ ({t} : Set K))) : K) = ((v : ↥E) : K) := fun v => rfl
      have h2 := congrArg (fun u : ↥(IntermediateField.adjoin ℂ ({t} : Set K)) => (u : K)) (e₁.apply_symm_apply w)
      simp only [h1] at h2
      exact h2)
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) ↥E)) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have : Subtype.val '' Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) ↥E) = Set.range Φ := by
      ext w
      constructor
      · rintro ⟨_, ⟨f, rfl⟩, rfl⟩; exact ⟨f, (hΦE f).symm⟩
      · rintro ⟨f, rfl⟩; exact ⟨ΦE f, ⟨f, rfl⟩, hΦE f⟩
    rw [this]
  obtain ⟨P', -, hP'ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) ℂ ↥E ⟨x₀, hx₀tr, hx₀fd⟩ ⟨ΦE y, htr', hEfd⟩ hgen P

  have hvaly : E.val (ΦE y) = t := by rw [IntermediateField.coe_val]; exact (hΦE y).trans hΦy'
  have hint : ∀ ψ : ↥E →ₐ[ℂ] K, ψ (ΦE y) = t → ψ.toRingHom.IsIntegral := by
    intro ψ hψ

    let S : Subalgebra ℂ K := ψ.range
    have hleS : (IntermediateField.adjoin ℂ ({t} : Set K)).toSubalgebra ≤ S := by
      have : IntermediateField.adjoin ℂ ({t} : Set K) ≤ ψ.fieldRange :=
        IntermediateField.adjoin_simple_le_iff.mpr ⟨ΦE y, hψ⟩
      intro w hw
      exact (AlgHom.mem_fieldRange.mp (this hw))
    letI algRS : Algebra ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥S := (Subalgebra.inclusion hleS).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ↥S K := Module.Finite.of_restrictScalars_finite ↥(IntermediateField.adjoin ℂ ({t} : Set K)) _ _
    haveI : Algebra.IsIntegral ↥S K := Algebra.IsIntegral.of_finite _ _
    have hS : (algebraMap ↥S K).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥S) x
    let e : ↥E ≃ₐ[ℂ] ↥S := AlgEquiv.ofInjective ψ ψ.toRingHom.injective
    have he : ψ.toRingHom = (algebraMap ↥S K).comp e.toAlgHom.toRingHom := by
      refine RingHom.ext fun x => ?_
      change ψ x = ((e x : ↥S) : K)
      rw [AlgEquiv.ofInjective_apply]
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective e.toAlgHom.toRingHom e.surjective) hS

  have hΦfixσ : ∀ γ ∈ CongruenceSubgroup.Gamma1 M, ∀ u, σ γ (Φ u) = Φ u :=
    fun γ hγ u => hΦfix γ hγ (hst γ⁻¹) (σ γ) (hσ γ) u
  have keyEQ : ∀ (j₀ : ℂ) (W₀ : Place ℂ K) (γ₀ : SL(2, ℤ)) (τ₀ : UpperHalfPlane), γ₀ • τ₀ = τ₀ →
      0 < W₀.ord (t - algebraMap ℂ K j₀) →
      (∀ g : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K,
        SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W₀ = W₀ → ∃ k : ℕ, g.restrictScalars ℂ = σ γ₀ ^ k) →
      ∀ w : Place ℂ ↥E, 0 < w.ord (ΦE y - algebraMap ℂ ↥E j₀) →
        w.ord (ΦE y - algebraMap ℂ ↥E j₀) = W₀.ord (t - algebraMap ℂ K j₀) := by
    intro j₀ W₀ γ₀ τ₀ hγτ hW₀ hD w hw
    obtain ⟨h1, -, h3, h4, h5⟩ := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ (ΦE y) t j₀ E.val hvaly
      hfd hgal hint W₀ hW₀
    obtain ⟨ψ, hψ, rfl⟩ := h3 w hw
    rw [h5 ψ hψ, h1]
    haveI := hfd
    haveI := hgal

    have htmem : t ∈ IntermediateField.adjoin ℂ ({t} : Set K) := IntermediateField.mem_adjoin_simple_self ℂ t
    have hσt : ∀ g : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K, g t = t := fun g =>
      g.commutes (⟨t, htmem⟩ : ↥(IntermediateField.adjoin ℂ ({t} : Set K)))
    have hle' : IntermediateField.adjoin ℂ ({t} : Set K) ≤ E :=
      IntermediateField.adjoin_simple_le_iff.mpr (hΦy' ▸ hΦmem y)

    let rSH : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K) →* (K ≃ₐ[ℂ] K) :=
      { toFun := fun g => g.restrictScalars ℂ
        map_one' := AlgEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
    have hrSH : ∀ g z, rSH g z = g z := fun _ _ => rfl
    have rSH_inj : Function.Injective rSH := fun g h hgh => AlgEquiv.ext fun z => by
      have := congrArg (fun f : K ≃ₐ[ℂ] K => f z) hgh
      exact this
    have hfixL : ∀ (d : SL(2, ℤ)), ∀ z ∈ IntermediateField.adjoin ℂ ({t} : Set K), σ d z = z := fun d z hz => by
      rw [← hfix] at hz
      exact (IntermediateField.mem_fixedField_iff _ z).mp hz _ ⟨d, rfl⟩
    have hrange : σ.range = rSH.range := by
      have hle : σ.range ≤ rSH.range := by
        rintro _ ⟨d, rfl⟩
        exact ⟨{ (σ d).toRingEquiv with commutes' := fun z => hfixL d z z.2 }, AlgEquiv.ext fun _ => rfl⟩
      haveI : Finite rSH.range := inferInstance
      refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
      show Nat.card rSH.range = Nat.card σ.range
      rw [← Subgroup.index_ker σ, hker, ← hdeg, ← IsGalois.card_aut_eq_finrank]
      exact (Nat.card_congr (MonoidHom.ofInjective rSH_inj).toEquiv).symm

    let gmap : {g : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
          SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W₀ = W₀} →
        {ψ' : {ψ' : ↥E →ₐ[ℂ] K // ψ' (ΦE y) = t} //
          W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := fun g =>
      have hψg : (((g.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ) (ΦE y) = t := by
        rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hψ]; exact hσt g.1
      ⟨⟨((g.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ, hψg⟩,
        ((h4 ψ _ hψ hψg).mpr ⟨g.1, g.2, rfl⟩).symm⟩
    have hsurj : Function.Surjective gmap := by
      rintro ⟨⟨ψ', hψ'⟩, heq⟩
      obtain ⟨g, hg, rfl⟩ := (h4 ψ ψ' hψ hψ').mp heq.symm
      exact ⟨⟨g, hg⟩, rfl⟩

    have hclaim : ∀ g : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K,
        SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W₀ = W₀ → (∀ e : ↥E, g (ψ e) = ψ e) → g = 1 := by
      intro g hgW hgψ
      obtain ⟨k, hk⟩ := hD g hgW

      have hψfix : ∀ (z : K) (hz : z ∈ IntermediateField.adjoin ℂ ({t} : Set K)), ψ ⟨z, hle' hz⟩ = z := by
        intro z hz
        let T : IntermediateField ℂ ↥E := (AlgHom.equalizer ψ E.val).toIntermediateField (fun x hx => by
          rw [AlgHom.mem_equalizer] at hx ⊢
          rw [map_inv₀, map_inv₀, hx])
        have hTle : IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E) ≤ T := by
          rw [IntermediateField.adjoin_simple_le_iff]
          show ψ (ΦE y) = E.val (ΦE y)
          rw [hψ, hvaly]
        have hzmem : (⟨z, hle' hz⟩ : ↥E) ∈ IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E) := by
          rw [← IntermediateField.mem_lift (⟨z, hle' hz⟩ : ↥E), IntermediateField.lift_adjoin_simple]
          have : ((ΦE y : ↥E) : K) = t := (hΦE y).trans hΦy'
          rw [this]; exact hz
        exact hTle hzmem

      let E₂ : IntermediateField ↥(IntermediateField.adjoin ℂ ({t} : Set K)) K := IntermediateField.extendScalars hle'
      let ψ₂ : ↥E₂ →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K :=
        { ψ.toRingHom with
          commutes' := fun z => hψfix z z.2 }
      have hψ₂ : ∀ e : ↥E, ψ₂ e = ψ e := fun _ => rfl
      haveI : Normal ↥(IntermediateField.adjoin ℂ ({t} : Set K)) K := inferInstance
      let φ' : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K := ψ₂.liftNormal K
      have hφ' : ∀ e : ↥E, φ' (e : K) = ψ e := fun e => by
        have := AlgHom.liftNormal_commutes ψ₂ K (e : ↥E₂)
        exact this
      haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℂ ({t} : Set K)) K := Algebra.IsAlgebraic.of_finite _ _
      let g' : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K :=
        AlgEquiv.ofBijective φ' (Algebra.IsAlgebraic.algHom_bijective φ')
      have hg' : ∀ e : ↥E, g' (e : K) = ψ e := hφ'

      obtain ⟨δ', hδ'⟩ : rSH g' ∈ σ.range := by rw [hrange]; exact ⟨g', rfl⟩

      set η : SL(2, ℤ) := δ'⁻¹ * γ₀ ^ k * δ' with hη
      have hσg : rSH g = σ (γ₀ ^ k) := by rw [map_pow]; exact hk
      have hση : σ η = rSH (g'⁻¹ * g * g') := by
        rw [hη, map_mul, map_mul, map_inv, hδ', map_mul, map_mul, map_inv, hσg]
      have hηfix : ∀ u, σ η (Φ u) = Φ u := by
        intro u
        rw [hση, hrSH, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        have h1 : g' (Φ u) = ψ ⟨Φ u, hΦmem u⟩ := hg' ⟨Φ u, hΦmem u⟩
        rw [h1, hgψ, ← h1]
        exact g'.symm_apply_apply _

      have hηmem := ModularCurve.LevelN.Descent.fixer_le M K t σ hker hfd hgal hdeg ι Φ E' hE'j hE'Φ y hy hΦy' hΦfixσ η hηfix
      rw [mem_sup_zpowers_neg_one_iff] at hηmem

      have hγpow : ∀ n : ℕ, (γ₀ ^ n) • τ₀ = τ₀ := fun n => by
        induction n with
        | zero => rw [pow_zero, one_smul]
        | succ n ih => rw [pow_succ, mul_smul, hγτ, ih]
      have hηpt : η • (δ'⁻¹ • τ₀) = δ'⁻¹ • τ₀ := by
        rw [hη, mul_smul, mul_smul, smul_inv_smul, hγpow k]

      have hη1 := CongruenceSubgroup.eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq M hM η hηmem (δ'⁻¹ • τ₀) hηpt
      have hγk1 : σ (γ₀ ^ k) = 1 := by
        have hconj : γ₀ ^ k = δ' * η * δ'⁻¹ := by rw [hη]; group
        have hneg1 : σ (-1) = 1 := by
          have : (-1 : SL(2, ℤ)) ∈ σ.ker := by rw [hker]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
          exact this
        rcases hη1 with h | h
        · rw [hconj, h, mul_one, mul_inv_cancel, map_one]
        · rw [hconj, h]
          rw [show δ' * -1 * δ'⁻¹ = (-1 : SL(2, ℤ)) by simp, hneg1]
      apply rSH_inj
      rw [hσg, hγk1, map_one]
    have hinj : Function.Injective gmap := by
      rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ heq
      have hcomp : ((g₁ : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ =
          ((g₂ : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ :=
        congrArg (fun e => e.1.1) heq
      have hg : g₂⁻¹ * g₁ = 1 := by
        refine hclaim (g₂⁻¹ * g₁) ?_ ?_
        · rw [show (g₂⁻¹ * g₁).restrictScalars ℂ = (g₂.restrictScalars ℂ)⁻¹ * g₁.restrictScalars ℂ from
            AlgEquiv.ext fun _ => rfl, map_mul, map_inv, mul_smul, hg₁, inv_smul_eq_iff, hg₂]
        · intro e
          have h12 : g₁ (ψ e) = g₂ (ψ e) := by
            have := congrArg (fun f : ↥E →ₐ[ℂ] K => f e) hcomp
            exact this
          rw [AlgEquiv.mul_apply, h12]
          exact g₂.symm_apply_apply _
      apply Subtype.ext
      exact (inv_mul_eq_one.mp hg).symm
    exact_mod_cast (Nat.card_eq_of_bijective gmap ⟨hinj, hsurj⟩).symm

  have h0E : P'.ord (ΦE y) = P.ord y := by rw [← hP'ord y]; rfl
  have h1728E : P'.ord (ΦE y - 1728) = P.ord (y - 1728) := by rw [← hP'ord (y - 1728), map_sub, map_ofNat]; rfl
  refine ⟨fun hpos => ?_, fun hpos => ?_⟩
  · have hk := keyEQ 0 W0 (ModularGroup.S * ModularGroup.T) UpperHalfPlane.ρ ST_smul_ρ
      (by rw [map_zero, sub_zero, hW0]; norm_num) hD0 P'
    simp only [map_zero, sub_zero] at hk
    rw [h0E, hW0] at hk
    exact hk hpos
  · have hk := keyEQ 1728 W1728 ModularGroup.S UpperHalfPlane.I S_smul_I
      (by rw [map_ofNat, hW1728]; norm_num) hD1728 P'
    simp only [map_ofNat] at hk
    rw [h1728E, hW1728] at hk
    exact hk hpos

theorem solution
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    (0 < P.ord y → P.ord y = 3) ∧ (0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) :=
  ModularCurve.NoEllAux.main M hM y hy P

end
end S_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
end P2MW
export P2MW.S_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure (solution)

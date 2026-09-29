-- Prove2me | solution 1 for ModularCurve.natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1eccfff4-914e-51f0-8fec-6cd7a9837145

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
import Theorems.Thm_AlgebraicCurve_natCard_place_ord_sub_pos_le_natCard_doubleCoset
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero"
p2m_attr_erase "simp" "TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open UpperHalfPlane
open scoped MatrixGroups IntermediateField Manifold

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset jGen coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff coeffMap_mem_laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen coeffMap_jqModC LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN natCard_doubleCoset_le_card_fibres_of_finrank_eq_index finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC jqModC_mem_intFormRatiosC exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange"
namespace CuspFibreGamma1
p2m_open "ModularCurve"

abbrev Gpm (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
  intro g hg
  rw [CongruenceSubgroup.Gamma_mem] at hg
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]

theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

section Galois

variable {L : Type*} [Field L] [Algebra ℂ L]

theorem adjoin_inv_eq (t : L) : ℂ⟮t⁻¹⟯ = ℂ⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t⁻¹)
    rwa [inv_inv] at this

theorem natCard_place_le_natCard_doubleCoset (t : L) (L₀ : IntermediateField ℂ L) (hL₀ : L₀ = ℂ⟮t⟯)
    [FiniteDimensional L₀ L] [IsGalois L₀ L]
    {Γ₀ : Type*} [Group Γ₀] (σ : Γ₀ →* (L ≃ₐ[L₀] L)) (hσ : Function.Surjective σ)
    (Γ Kst : Subgroup Γ₀) [Γ.FiniteIndex]
    (E : IntermediateField L₀ L) (hE : ∀ γ ∈ Γ, ∀ e : E, σ γ (e : L) = e)
    (c : ℂ) (W : AlgebraicCurve.Place ℂ L) (hW : 0 < W.ord (t - algebraMap ℂ L c))
    (hD : ∀ k ∈ Kst, AlgebraicCurve.SemilinearAut.ofAlgAut ((σ k).restrictScalars ℂ) • W = W)
    (x : E) (hx : (x : L) = t) :
    Nat.card {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (x - algebraMap ℂ E c)} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀)) := by
  subst hL₀
  exact AlgebraicCurve.natCard_place_ord_sub_pos_le_natCard_doubleCoset ℂ t inferInstance inferInstance
    σ hσ Γ Kst E hE c W hW hD x hx

theorem algebraMap_mem_adjoin (t : L) (E : IntermediateField ℂ⟮t⟯ L) (x : E) (hx : (x : L) = t)
    (l : ℂ⟮t⟯) : algebraMap ℂ⟮t⟯ E l ∈ IntermediateField.adjoin ℂ ({x} : Set E) := by
  let f : E →ₐ[ℂ] L := (IntermediateField.val E).restrictScalars ℂ
  have hfx : f x = t := hx
  have hmap : (IntermediateField.adjoin ℂ ({x} : Set E)).map f = ℂ⟮t⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hfx]
  have hl : (l : L) ∈ (IntermediateField.adjoin ℂ ({x} : Set E)).map f := by
    rw [hmap]; exact l.2
  obtain ⟨a, ha, hal⟩ := (IntermediateField.mem_map _).mp hl
  have : a = algebraMap ℂ⟮t⟯ E l := Subtype.ext hal
  rw [← this]; exact ha

theorem finiteDimensional_adjoin (t : L) (E : IntermediateField ℂ⟮t⟯ L) [FiniteDimensional ℂ⟮t⟯ E]
    (x : E) (hx : (x : L) = t) :
    FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set E)) E := by
  let A : IntermediateField ℂ E := IntermediateField.adjoin ℂ ({x} : Set E)
  letI : Algebra ℂ⟮t⟯ A :=
    ((algebraMap ℂ⟮t⟯ E).codRestrict A (algebraMap_mem_adjoin t E x hx)).toAlgebra
  haveI : IsScalarTower ℂ⟮t⟯ A E := IsScalarTower.of_algebraMap_eq (fun l => rfl)
  exact Module.Finite.of_restrictScalars_finite ℂ⟮t⟯ A E

end Galois

section Lift

variable {L : Type*} [Field L] [Algebra ℂ L]

def liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) : L ≃ₐ[E'] L :=
  { φ.toRingEquiv with commutes' := fun e => hφ e e.2 }

@[scoped simp]
theorem liftE_apply (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) (x : L) :
    liftE E' φ hφ x = φ x := rfl

theorem restrictScalars_liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) :
    (liftE E' φ hφ).restrictScalars ℂ = φ :=
  AlgEquiv.ext fun _ => rfl

def liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L) (σ : Γ →* (L ≃ₐ[ℂ] L))
    (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) : Γ →* (L ≃ₐ[E'] L) where
  toFun γ := liftE E' (σ γ) (hσ γ)
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

@[scoped simp]
theorem liftHom_apply {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) (x : L) :
    liftHom E' σ hσ γ x = σ γ x := rfl

theorem restrictScalars_liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) :
    (liftHom E' σ hσ γ).restrictScalars ℂ = σ γ :=
  restrictScalars_liftE E' (σ γ) (hσ γ)

theorem liftHom_eq_one_iff {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) :
    liftHom E' σ hσ γ = 1 ↔ γ ∈ σ.ker := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (AlgEquiv.restrictScalars ℂ) h
    rw [restrictScalars_liftHom] at this
    rw [this]
    ext x
    rfl
  · intro h
    ext x
    change σ γ x = x
    rw [h]
    rfl

theorem liftHom_ker {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) :
    (liftHom E' σ hσ).ker = σ.ker := by
  ext γ
  rw [MonoidHom.mem_ker, liftHom_eq_one_iff]

end Lift

section LevelN

variable (M : ℕ) [NeZero M]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (LevelN.ring M) K]
  [IsScalarTower ℂ (LevelN.ring M) K] [IsFractionRing (LevelN.ring M) K]

theorem galoisPackage :
    ∃ (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring M,
        (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring M)
      (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)),
      (∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring M),
          σ γ (algebraMap (ModularCurve.LevelN.ring M) K ⟨F, hF⟩) =
            algebraMap (ModularCurve.LevelN.ring M) K
              ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩) ∧
      σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      IntermediateField.fixedField σ.range =
        IntermediateField.adjoin ℂ
          ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K) ∧
      Transcendental ℂ (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) ∧
      FiniteDimensional
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K)) K ∧
      Module.finrank
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K)) K =
        (CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      IsGalois
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K)) K :=
  ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin M K

include K in

theorem comp_smul_mem (γ : SL(2, ℤ)) (F : ℍ → ℂ) (hF : F ∈ LevelN.ring M) :
    (fun τ : ℍ => F (γ • τ)) ∈ LevelN.ring M :=
  (galoisPackage M K).choose γ F hF

def σK : SL(2, ℤ) →* (K ≃ₐ[ℂ] K) := (galoisPackage M K).choose_spec.choose

abbrev jK : K := algebraMap (LevelN.ring M) K (LevelN.jGen M)

theorem σK_algebraMap (γ : SL(2, ℤ)) (F : ℍ → ℂ) (hF : F ∈ LevelN.ring M) :
    σK M K γ (algebraMap (LevelN.ring M) K ⟨F, hF⟩) =
      algebraMap (LevelN.ring M) K ⟨fun τ : ℍ => F (γ⁻¹ • τ), comp_smul_mem M K γ⁻¹ F hF⟩ :=
  (galoisPackage M K).choose_spec.choose_spec.1 γ F hF

theorem σK_ker : (σK M K).ker = Gpm M := (galoisPackage M K).choose_spec.choose_spec.2.1

theorem fixedField_σK : IntermediateField.fixedField (σK M K).range = ℂ⟮jK M K⟯ :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.1

theorem transcendental_jK : Transcendental ℂ (jK M K) :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.1

theorem finiteDimensional_jK : FiniteDimensional ℂ⟮jK M K⟯ K :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.1

theorem finrank_jK : Module.finrank ℂ⟮jK M K⟯ K = (Gpm M).index :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.2.1

theorem isGalois_jK : IsGalois ℂ⟮jK M K⟯ K :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.2.2

theorem σK_fix (γ : SL(2, ℤ)) : ∀ x ∈ ℂ⟮jK M K⟯, σK M K γ x = x := fun x hx => by
  rw [← fixedField_σK] at hx
  exact (IntermediateField.mem_fixedField_iff (σK M K).range x).mp hx (σK M K γ) ⟨γ, rfl⟩

def σ' : SL(2, ℤ) →* (K ≃ₐ[ℂ⟮jK M K⟯] K) := liftHom ℂ⟮jK M K⟯ (σK M K) (σK_fix M K)

theorem restrictScalars_σ' (γ : SL(2, ℤ)) : (σ' M K γ).restrictScalars ℂ = σK M K γ :=
  restrictScalars_liftHom _ _ _ γ

@[scoped simp]
theorem σ'_apply (γ : SL(2, ℤ)) (x : K) : σ' M K γ x = σK M K γ x := rfl

theorem σ'_ker : (σ' M K).ker = Gpm M := by
  rw [σ', liftHom_ker, σK_ker]

theorem σ'_eq_one_iff (γ : SL(2, ℤ)) : σ' M K γ = 1 ↔ γ ∈ Gpm M := by
  rw [← MonoidHom.mem_ker, σ'_ker]

theorem σ'_surjective : Function.Surjective (σ' M K) := by
  haveI := finiteDimensional_jK M K
  haveI := isGalois_jK M K
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, σ'_ker, ← finrank_jK M K, IsGalois.card_aut_eq_finrank]

theorem exists_place_infty :
    ∃ W : AlgebraicCurve.Place ℂ K, 0 < W.ord ((jK M K)⁻¹ - algebraMap ℂ K 0) ∧
      ∀ k ∈ Subgroup.zpowers (ModularGroup.T : SL(2, ℤ)) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)),
        AlgebraicCurve.SemilinearAut.ofAlgAut ((σ' M K k).restrictScalars ℂ) • W = W := by
  obtain ⟨W, hW, hWfix⟩ :=
    ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq M K (comp_smul_mem M K ModularGroup.T⁻¹)
  change W.ord (jK M K) < 0 at hW
  have hW' : 0 < W.ord ((jK M K)⁻¹ - algebraMap ℂ K 0) := by
    rw [map_zero, sub_zero, AlgebraicCurve.Place.ord_inv]; omega
  refine ⟨W, hW', ?_⟩
  let S : Subgroup SL(2, ℤ) :=
    (MulAction.stabilizer (AlgebraicCurve.SemilinearAut ℂ K) W).comap
      (AlgebraicCurve.SemilinearAut.ofAlgAut.comp (σK M K))
  have hS : ∀ k, k ∈ S ↔ AlgebraicCurve.SemilinearAut.ofAlgAut (σK M K k) • W = W := fun k => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]; rfl
  have hT : ModularGroup.T ∈ S := (hS _).mpr (hWfix (σK M K _) (σK_algebraMap M K _))
  have hneg : (-1 : SL(2, ℤ)) ∈ S := by
    rw [hS]
    have : σK M K (-1) = 1 := by
      rw [← MonoidHom.mem_ker, σK_ker]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [this, map_one, one_smul]
  have hle : Subgroup.zpowers (ModularGroup.T : SL(2, ℤ)) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ S :=
    sup_le ((Subgroup.zpowers_le).mpr hT) ((Subgroup.zpowers_le).mpr hneg)
  intro k hk
  rw [restrictScalars_σ']
  exact (hS k).mp (hle hk)

end LevelN

section ConstantField

variable {F : Type*} [Field F]
variable {L : Type*} [Field L] [Algebra ℂ L] (t : L) (E : IntermediateField ℂ⟮t⟯ L) [Algebra F E]

theorem adjoin_adjoin_subset {L : Type*} [Field L] [Algebra ℂ L] (S : Set L) (t : L)
    (ht : t ∈ IntermediateField.adjoin ℂ S) :
    ((IntermediateField.adjoin ℂ⟮t⟯ S : IntermediateField ℂ⟮t⟯ L) : Set L) ⊆
      ((IntermediateField.adjoin ℂ S : IntermediateField ℂ L) : Set L) := by
  have h1 : ((IntermediateField.adjoin ℂ⟮t⟯ S : IntermediateField ℂ⟮t⟯ L) : Set L) =
      (IntermediateField.restrictScalars ℂ (IntermediateField.adjoin ℂ⟮t⟯ S) : Set L) := rfl
  rw [h1, IntermediateField.restrictScalars_adjoin]
  have hle : IntermediateField.adjoin ℂ ((ℂ⟮t⟯ : Set L) ∪ S) ≤ IntermediateField.adjoin ℂ S := by
    rw [IntermediateField.adjoin_le_iff]
    apply Set.union_subset
    · have : ℂ⟮t⟯ ≤ IntermediateField.adjoin ℂ S := IntermediateField.adjoin_simple_le_iff.mpr ht
      exact SetLike.coe_subset_coe.mpr this
    · exact IntermediateField.subset_adjoin _ _
  exact SetLike.coe_subset_coe.mpr hle

theorem adjoin_range_eq_top
    (hEle : (E : Set L) ⊆
      ((IntermediateField.adjoin ℂ (Set.range fun u : F => (algebraMap F E u : L)) :
        IntermediateField ℂ L) : Set L)) :
    IntermediateField.adjoin ℂ (Set.range (algebraMap F E)) = ⊤ := by
  let f : E →ₐ[ℂ] L := E.val.restrictScalars ℂ
  set A := IntermediateField.adjoin ℂ (Set.range (algebraMap F E)) with hA
  have hmapA : A.map f = IntermediateField.adjoin ℂ (Set.range fun u : F => (algebraMap F E u : L)) := by
    rw [hA, IntermediateField.adjoin_map, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  intro e _
  have he : (e : L) ∈ A.map f := by
    rw [hmapA]; exact hEle e.2
  obtain ⟨a, ha, hae⟩ := (IntermediateField.mem_map A).mp he
  have : a = e := Subtype.ext hae
  rw [← this]; exact ha

end ConstantField

section Main

variable (M : ℕ) [NeZero M]

theorem isDomain_ring : IsDomain (LevelN.ring M) := by
  have h := WLight.levelN_structure_package M PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (LevelN.wp M)
    (fun v τ => rfl) (LevelN.fricke M) (fun v τ => rfl) LevelN.jAnalytic (fun τ => rfl)
  have hzd := h.2.2.2.2.2
  have hnz : NoZeroDivisors (LevelN.ring M) := ⟨fun {a b} hab => by
    rcases hzd a b a.2 b.2 (by simpa using congrArg Subtype.val hab) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)⟩
  have hnt : Nontrivial (LevelN.ring M) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) UpperHalfPlane.I
    simp at this⟩⟩
  exact NoZeroDivisors.to_isDomain _

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (LevelN.ring M) K]
  [IsScalarTower ℂ (LevelN.ring M) K] [IsFractionRing (LevelN.ring M) K]

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))

include K in
set_option maxHeartbeats 6400000 in

theorem natCard_place_ord_lt_zero_le (ι : ℚ̄ →+* ℂ) (y : FF) (hy : (y : LaurentSeries ℚ̄) = jqModC ℚ̄) :
    Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // P.ord y < 0} ≤
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) := by
  classical
  haveI := finiteDimensional_jK M K
  haveI := isGalois_jK M K
  haveI hKc : CharZero ℚ̄ := charZero_of_injective_algebraMap (algebraMap ℚ ℚ̄).injective
  haveI hΓfi : (CongruenceSubgroup.Gamma1 M).FiniteIndex :=
    (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  have hΓM : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := Gamma_le_Gamma1 M
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := T_mem_Gamma1 M

  obtain ⟨Φ, hΦc, hΦy, hΦfix⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN M
      (CongruenceSubgroup.Gamma1 M) hΓM hT ι K
  set L₀ : IntermediateField ℂ K := ℂ⟮jK M K⟯ with hL₀
  let E : IntermediateField L₀ K := IntermediateField.adjoin L₀ (Set.range Φ)
  have hΦE : ∀ u, Φ u ∈ E := fun u => IntermediateField.subset_adjoin _ _ ⟨u, rfl⟩
  let ΦE : FF →+* E := Φ.codRestrict E hΦE

  letI : Algebra ℚ̄ ℂ := ι.toAlgebra
  letI : Algebra FF E := ΦE.toAlgebra
  letI : Algebra ℚ̄ E := ((algebraMap ℂ E).comp ι).toAlgebra
  haveI : IsScalarTower ℚ̄ ℂ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℚ̄ FF E := IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap ℂ K (ι c) = Φ (algebraMap ℚ̄ FF c)
    rw [hΦc])

  obtain ⟨hyT, hfin⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      ℚ̄ (CongruenceSubgroup.Gamma1 M) hT y hy
  haveI := hfin
  haveI : AlgebraicCurve.IsCurveOver ℚ̄ FF :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hyT hfin

  have hjE : jK M K ∈ E := E.algebraMap_mem (⟨jK M K, IntermediateField.mem_adjoin_simple_self ℂ _⟩ : L₀)
  let xE : E := ⟨jK M K, hjE⟩
  have hyt : ((algebraMap FF E y : E) : K) = jK M K := hΦy y hy
  have hΦEy : algebraMap FF E y = xE := Subtype.ext hyt
  haveI hfinE : FiniteDimensional L₀ E := IntermediateField.finiteDimensional_left E
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap FF E)) = ⊤ := by
    apply adjoin_range_eq_top (jK M K) E
    change ((IntermediateField.adjoin L₀ (Set.range Φ) : IntermediateField L₀ K) : Set K) ⊆
      ((IntermediateField.adjoin ℂ (Set.range fun u => Φ u) : IntermediateField ℂ K) : Set K)
    apply adjoin_adjoin_subset
    exact IntermediateField.subset_adjoin _ _ ⟨y, hΦy y hy⟩
  have hxT : Transcendental ℂ xE := by
    intro halg
    apply transcendental_jK M K
    have h' : IsAlgebraic ℂ ((IntermediateField.val E).restrictScalars ℂ xE) := halg.algHom _
    exact h'
  have hxfin : FiniteDimensional (IntermediateField.adjoin ℂ ({xE} : Set E)) E :=
    finiteDimensional_adjoin (jK M K) E xE rfl

  have hσE : ∀ γ ∈ CongruenceSubgroup.Gamma1 M, ∀ e : E, σ' M K γ (e : K) = e := by
    intro γ hγ e
    have hle : E ≤ IntermediateField.fixedField (Subgroup.zpowers (σ' M K γ)) := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨u, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      have hst : σ' M K γ ∈ MulAction.stabilizer (K ≃ₐ[L₀] K) (Φ u) := by
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, σ'_apply]
        exact hΦfix γ hγ (comp_smul_mem M K γ⁻¹) (σK M K γ) (σK_algebraMap M K γ) u
      have := (Subgroup.zpowers_le.mpr hst) hg
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    exact (IntermediateField.mem_fixedField_iff _ (e : K)).mp (hle e.2) _ (Subgroup.mem_zpowers _)

  have hy0 : y ≠ 0 := fun h => by
    rw [h] at hyT; exact hyT isAlgebraic_zero
  obtain ⟨-, hplaces⟩ :=
    AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin y hyT
      (jK M K) (transcendental_jK M K) E hyt hgen
  haveI hfinE' : Finite {P : AlgebraicCurve.Place ℂ E // P.ord (algebraMap FF E y) < 0} :=
    ((hplaces y hy0).2).1

  have hDC := fun P : AlgebraicCurve.Place ℚ̄ FF =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension ℚ̄ FF ℂ E
      ⟨y, hyT, hfin⟩ ⟨xE, hxT, hxfin⟩ hgen P
  choose lift hcomap hord huniq using hDC
  have hinj : Function.Injective lift := fun P₁ P₂ h =>
    AlgebraicCurve.Place.ext (by rw [← hcomap P₁, ← hcomap P₂, h])
  let ι' : {P : AlgebraicCurve.Place ℚ̄ FF // P.ord y < 0} →
      {P : AlgebraicCurve.Place ℂ E // P.ord (algebraMap FF E y) < 0} :=
    fun P => ⟨lift P.1, by rw [hord]; exact P.2⟩
  have hι' : Function.Injective ι' := fun P₁ P₂ h =>
    Subtype.ext (hinj (congrArg (fun Q : {P : AlgebraicCurve.Place ℂ E //
      P.ord (algebraMap FF E y) < 0} => Q.1) h))
  have h1 : Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // P.ord y < 0} ≤
      Nat.card {P : AlgebraicCurve.Place ℂ E // P.ord (algebraMap FF E y) < 0} :=
    Nat.card_le_card_of_injective ι' hι'

  obtain ⟨W, hW, hD⟩ := exists_place_infty M K
  have hiff : ∀ P : AlgebraicCurve.Place ℂ E,
      0 < P.ord (xE⁻¹ - algebraMap ℂ E 0) ↔ P.ord (algebraMap FF E y) < 0 := by
    intro P
    rw [map_zero, sub_zero, AlgebraicCurve.Place.ord_inv, hΦEy]
    omega
  let eqv : {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (xE⁻¹ - algebraMap ℂ E 0)} ≃
      {P : AlgebraicCurve.Place ℂ E // P.ord (algebraMap FF E y) < 0} :=
    Equiv.subtypeEquivRight hiff
  have h2 := natCard_place_le_natCard_doubleCoset (jK M K)⁻¹ L₀ (adjoin_inv_eq _).symm (σ' M K)
    (σ'_surjective M K) (CongruenceSubgroup.Gamma1 M)
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) E hσE 0 W hW hD xE⁻¹ rfl
  rw [Nat.card_congr eqv] at h2
  exact h1.trans h2

theorem natCard_place_ord_lt_zero_eq (y : FF) (hy : (y : LaurentSeries ℚ̄) = jqModC ℚ̄) :
    Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // P.ord y < 0} =
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) := by
  haveI := isDomain_ring M
  haveI : Algebra.IsAlgebraic ℚ ℚ̄ := AlgebraicClosure.isAlgebraic ℚ
  let ι : ℚ̄ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := ℚ̄)).toRingHom
  refine le_antisymm (natCard_place_ord_lt_zero_le M (FractionRing (LevelN.ring M)) ι y hy) ?_
  have hfull :=
    ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index ℚ̄ M y hy
  exact (ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index M
    (CongruenceSubgroup.Gamma1 M) le_rfl y hy hfull).2.2

end Main

end ModularCurve.CuspFibreGamma1
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve.CuspFibreGamma1"
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset jGen coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff coeffMap_mem_laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen coeffMap_jqModC LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN natCard_doubleCoset_le_card_fibres_of_finrank_eq_index finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC jqModC_mem_intFormRatiosC exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange"
namespace CuspTransport
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve IntermediateField AlgebraicCurve"

section CoeffMap

variable {κ k : Type*} [Field κ] [Field k] [Algebra ℚ κ] [Algebra ℚ k] (τ : κ →ₐ[ℚ] k)

theorem algebraMap_laurentSeries_eq_C {L : Type*} [Field L] (a : L) :
    algebraMap L (LaurentSeries L) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap L (PowerSeries L) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem coeffMap_algebraMap' (a : κ) :
    coeffMap τ.toRingHom (algebraMap κ (LaurentSeries κ) a) = algebraMap k (LaurentSeries k) (τ a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffMap_single]
  rfl

theorem coeffMap_coeffEmb' (z : LaurentSeries ℚ) :
    coeffMap τ.toRingHom (coeffEmb κ z) = coeffEmb k z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (τ.comp_algebraMap) z

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_mem_laurentBaseChange {x : LaurentSeries κ} (hx : x ∈ laurentBaseChange κ F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange k F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  have hle : Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ (⇑(coeffEmb κ) '' (F₀ : Set (LaurentSeries ℚ)))) ≤
      (laurentBaseChange k F₀).toSubfield.comap (coeffMap τ.toRingHom) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | ⟨w, hw, rfl⟩)
    · change coeffMap τ.toRingHom (algebraMap κ (LaurentSeries κ) a) ∈ laurentBaseChange k F₀
      rw [coeffMap_algebraMap']
      exact IntermediateField.algebraMap_mem _ _
    · change coeffMap τ.toRingHom (coeffEmb κ w) ∈ laurentBaseChange k F₀
      rw [coeffMap_coeffEmb']
      exact coeffEmb_mem_laurentBaseChange k hw
  exact hle hx

noncomputable def psi : ↥(laurentBaseChange κ F₀) →+* ↥(laurentBaseChange k F₀) :=
  RingHom.codRestrict ((coeffMap τ.toRingHom).comp (algebraMap ↥(laurentBaseChange κ F₀) (LaurentSeries κ)))
    (laurentBaseChange k F₀) (fun f => coeffMap_mem_laurentBaseChange τ F₀ f.2)

theorem coe_psi (f : ↥(laurentBaseChange κ F₀)) :
    ((psi τ F₀ f : ↥(laurentBaseChange k F₀)) : LaurentSeries k) = coeffMap τ.toRingHom (f : LaurentSeries κ) := rfl

end CoeffMap
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve.CuspFibreGamma1"

theorem jqModC_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    jqModC L ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
  have h := intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
  have e : coeffEmb L (jqModC ℚ) = jqModC L := coeffMap_jqModC _
  exact e ▸ coeffEmb_mem_laurentBaseChange L h

open scoped MatrixGroups in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem natCard_place_ord_lt_zero_laurentBaseChange_eq
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (yK : ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hyK : (yK : LaurentSeries K) = jqModC K)
    (y : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Nat.card {P : Place K ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) // P.ord yK < 0} =
      Nat.card {P : Place (AlgebraicClosure ℚ)
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) // P.ord y < 0} := by
  classical

  let F₀ : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let τ : (AlgebraicClosure ℚ) →ₐ[ℚ] K := IsAlgClosed.lift
  let Ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →+* ↥(laurentBaseChange K F₀) := psi τ F₀
  have hΨ : ∀ f, ((Ψ f : ↥(laurentBaseChange K F₀)) : LaurentSeries K) = coeffMap τ.toRingHom (f : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun f => rfl
  have hΨy : Ψ y = yK := by
    apply Subtype.ext
    rw [hΨ, hy, hyK, coeffMap_jqModC]

  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  obtain ⟨htr, hfin⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) hT y hy
  obtain ⟨htrK, hfinK⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      K (CongruenceSubgroup.Gamma1 M) hT yK hyK
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfin

  letI : Algebra (AlgebraicClosure ℚ) K := τ.toRingHom.toAlgebra
  letI : Algebra ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀) := Ψ.toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) ↥(laurentBaseChange K F₀) :=
    ((algebraMap K ↥(laurentBaseChange K F₀)).comp τ.toRingHom).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) K ↥(laurentBaseChange K F₀) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    change ((algebraMap K ↥(laurentBaseChange K F₀) (τ a) : ↥(laurentBaseChange K F₀)) : LaurentSeries K) =
      ((Ψ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) a) : ↥(laurentBaseChange K F₀)) : LaurentSeries K)
    rw [hΨ]
    exact (coeffMap_algebraMap' τ a).symm
  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀))) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    have hv' := (mem_laurentBaseChange_iff).mp hv
    have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
        (⇑(coeffEmb K) '' (F₀ : Set (LaurentSeries ℚ)))) ≤
        (IntermediateField.adjoin K
          (Set.range (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀)))).toSubfield.map
          (algebraMap ↥(laurentBaseChange K F₀) (LaurentSeries K)) := by
      rw [Subfield.closure_le]
      rintro z (⟨a, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨algebraMap K ↥(laurentBaseChange K F₀) a, IntermediateField.algebraMap_mem _ a,
          (IsScalarTower.algebraMap_apply K ↥(laurentBaseChange K F₀) (LaurentSeries K) a).symm⟩
      · refine ⟨Ψ ⟨coeffEmb (AlgebraicClosure ℚ) w, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hw⟩,
          IntermediateField.subset_adjoin K _ ⟨_, rfl⟩, ?_⟩
        change ((Ψ _ : ↥(laurentBaseChange K F₀)) : LaurentSeries K) = coeffEmb K w
        rw [hΨ]
        exact coeffMap_coeffEmb' τ w
    obtain ⟨w, hwA, hwv⟩ := hle hv'
    have hw : w = ⟨v, hv⟩ := Subtype.ext hwv
    rw [← hw]
    exact hwA

  have hlift := fun P : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)
      K ↥(laurentBaseChange K F₀) ⟨y, htr, hfin⟩ ⟨yK, htrK, hfinK⟩ hgen P
  let lift : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) → Place K ↥(laurentBaseChange K F₀) := fun P => (hlift P).choose
  have hlift_comap : ∀ P, (lift P).toValuationSubring.comap
      (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀)) = P.toValuationSubring :=
    fun P => (hlift P).choose_spec.1
  have hlift_ord : ∀ P f, (lift P).ord (Ψ f) = P.ord f := fun P f => (hlift P).choose_spec.2.1 f
  have hlift_uniq : ∀ P Q', Q'.toValuationSubring.comap
      (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) ↥(laurentBaseChange K F₀)) = P.toValuationSubring → Q' = lift P :=
    fun P Q' h => (hlift P).choose_spec.2.2 Q' h

  let g : {P : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) // P.ord y < 0} →
      {Q : Place K ↥(laurentBaseChange K F₀) // Q.ord yK < 0} :=
    fun P => ⟨lift P.1, by rw [← hΨy, hlift_ord]; exact P.2⟩
  have ginj : Function.Injective g := by
    rintro ⟨P₁, h₁⟩ ⟨P₂, h₂⟩ h
    have h' : lift P₁ = lift P₂ := congrArg Subtype.val h
    apply Subtype.ext
    apply AlgebraicCurve.Place.ext
    rw [← hlift_comap P₁, ← hlift_comap P₂, h']
  have gsurj : Function.Surjective g := by
    rintro ⟨Q, hQ⟩

    have hQy : Q.ord (Ψ y) ≠ 0 := by rw [hΨy]; exact ne_of_lt hQ
    obtain ⟨P₀, hP₀⟩ :=
      ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange K (CongruenceSubgroup.Gamma1 M) hT
        τ Ψ hΨ Q ⟨y, hQy⟩
    have hP₀y : P₀.ord y < 0 := by rw [← hP₀ y, hΨy]; exact hQ
    refine ⟨⟨P₀, hP₀y⟩, ?_⟩
    apply Subtype.ext
    change lift P₀ = Q
    symm
    apply hlift_uniq
    ext f
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · rw [AlgebraicCurve.Place.mem_comap_iff_ord_nonneg hf, AlgebraicCurve.Place.mem_iff_ord_nonneg P₀ hf]
      change 0 ≤ Q.ord (Ψ f) ↔ 0 ≤ P₀.ord f
      rw [hP₀ f]
  exact (Nat.card_congr (Equiv.ofBijective g ⟨ginj, gsurj⟩)).symm

end ModularCurve.CuspTransport
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve.CuspFibreGamma1"
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve.CuspFibreGamma1"

end
p2m_reactivate "P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve.CuspFibreGamma1"

p2m_open "ModularCurve P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.ModularCurve CongruenceSubgroup AlgebraicCurve"
open scoped MatrixGroups

theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Nat.card {P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) // P.ord y < 0} =
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) := by
  let y₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) :=
    ⟨ModularCurve.jqModC (AlgebraicClosure ℚ),
      ModularCurve.CuspTransport.jqModC_mem_laurentBaseChange (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M)⟩
  rw [ModularCurve.CuspTransport.natCard_place_ord_lt_zero_laurentBaseChange_eq K M y hy y₀ rfl]
  exact ModularCurve.CuspFibreGamma1.natCard_place_ord_lt_zero_eq M y₀ rfl

example
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Nat.card {P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) // P.ord y < 0} =
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) :=
  solution K M y hy

end S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset
end P2MW
export P2MW.S_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset (solution)

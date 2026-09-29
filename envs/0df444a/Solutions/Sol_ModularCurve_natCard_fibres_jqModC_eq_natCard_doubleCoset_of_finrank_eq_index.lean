-- Prove2me | solution 1 for ModularCurve.natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/87a69c46-737f-545a-a06e-0640f3d48d2d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
import Theorems.Thm_AlgebraicCurve_natCard_place_ord_sub_pos_le_natCard_doubleCoset
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open UpperHalfPlane
open scoped MatrixGroups IntermediateField Manifold

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jGen laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq LevelN.exists_place_ord_sub_pos_forall_smul_eq exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN natCard_doubleCoset_le_card_fibres_of_finrank_eq_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC"
namespace FibresGamma
p2m_open "ModularCurve"

private abbrev Gpm (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

private theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
  intro g hg
  rw [CongruenceSubgroup.Gamma_mem] at hg
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

private theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]

private theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

section Galois

variable {L : Type*} [Field L] [Algebra ℂ L]

private theorem adjoin_inv_eq (t : L) : ℂ⟮t⁻¹⟯ = ℂ⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t⁻¹)
    rwa [inv_inv] at this

private theorem natCard_place_le_natCard_doubleCoset (t : L) (L₀ : IntermediateField ℂ L) (hL₀ : L₀ = ℂ⟮t⟯)
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

private theorem algebraMap_mem_adjoin (t : L) (E : IntermediateField ℂ⟮t⟯ L) (x : E) (hx : (x : L) = t)
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

private theorem finiteDimensional_adjoin (t : L) (E : IntermediateField ℂ⟮t⟯ L) [FiniteDimensional ℂ⟮t⟯ E]
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

private def liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) : L ≃ₐ[E'] L :=
  { φ.toRingEquiv with commutes' := fun e => hφ e e.2 }

@[scoped simp]
private theorem liftE_apply (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) (x : L) :
    liftE E' φ hφ x = φ x := rfl

private theorem restrictScalars_liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) :
    (liftE E' φ hφ).restrictScalars ℂ = φ :=
  AlgEquiv.ext fun _ => rfl

private def liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L) (σ : Γ →* (L ≃ₐ[ℂ] L))
    (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) : Γ →* (L ≃ₐ[E'] L) where
  toFun γ := liftE E' (σ γ) (hσ γ)
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

@[scoped simp]
private theorem liftHom_apply {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) (x : L) :
    liftHom E' σ hσ γ x = σ γ x := rfl

private theorem restrictScalars_liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) :
    (liftHom E' σ hσ γ).restrictScalars ℂ = σ γ :=
  restrictScalars_liftE E' (σ γ) (hσ γ)

private theorem liftHom_eq_one_iff {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
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

private theorem liftHom_ker {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) :
    (liftHom E' σ hσ).ker = σ.ker := by
  ext γ
  rw [MonoidHom.mem_ker, liftHom_eq_one_iff]

end Lift

section LevelN

variable (M : ℕ) [NeZero M]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (LevelN.ring M) K]
  [IsScalarTower ℂ (LevelN.ring M) K] [IsFractionRing (LevelN.ring M) K]

private theorem galoisPackage :
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

private theorem comp_smul_mem (γ : SL(2, ℤ)) (F : ℍ → ℂ) (hF : F ∈ LevelN.ring M) :
    (fun τ : ℍ => F (γ • τ)) ∈ LevelN.ring M :=
  (galoisPackage M K).choose γ F hF

private def σK : SL(2, ℤ) →* (K ≃ₐ[ℂ] K) := (galoisPackage M K).choose_spec.choose

private abbrev jK : K := algebraMap (LevelN.ring M) K (LevelN.jGen M)

private theorem σK_algebraMap (γ : SL(2, ℤ)) (F : ℍ → ℂ) (hF : F ∈ LevelN.ring M) :
    σK M K γ (algebraMap (LevelN.ring M) K ⟨F, hF⟩) =
      algebraMap (LevelN.ring M) K ⟨fun τ : ℍ => F (γ⁻¹ • τ), comp_smul_mem M K γ⁻¹ F hF⟩ :=
  (galoisPackage M K).choose_spec.choose_spec.1 γ F hF

private theorem σK_ker : (σK M K).ker = Gpm M := (galoisPackage M K).choose_spec.choose_spec.2.1

private theorem fixedField_σK : IntermediateField.fixedField (σK M K).range = ℂ⟮jK M K⟯ :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.1

private theorem transcendental_jK : Transcendental ℂ (jK M K) :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.1

private theorem finiteDimensional_jK : FiniteDimensional ℂ⟮jK M K⟯ K :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.1

private theorem finrank_jK : Module.finrank ℂ⟮jK M K⟯ K = (Gpm M).index :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.2.1

private theorem isGalois_jK : IsGalois ℂ⟮jK M K⟯ K :=
  (galoisPackage M K).choose_spec.choose_spec.2.2.2.2.2.2

private theorem σK_fix (γ : SL(2, ℤ)) : ∀ x ∈ ℂ⟮jK M K⟯, σK M K γ x = x := fun x hx => by
  rw [← fixedField_σK] at hx
  exact (IntermediateField.mem_fixedField_iff (σK M K).range x).mp hx (σK M K γ) ⟨γ, rfl⟩

private def σ' : SL(2, ℤ) →* (K ≃ₐ[ℂ⟮jK M K⟯] K) := liftHom ℂ⟮jK M K⟯ (σK M K) (σK_fix M K)

private theorem restrictScalars_σ' (γ : SL(2, ℤ)) : (σ' M K γ).restrictScalars ℂ = σK M K γ :=
  restrictScalars_liftHom _ _ _ γ

@[scoped simp]
private theorem σ'_apply (γ : SL(2, ℤ)) (x : K) : σ' M K γ x = σK M K γ x := rfl

private theorem σ'_ker : (σ' M K).ker = Gpm M := by
  rw [σ', liftHom_ker, σK_ker]

private theorem σ'_eq_one_iff (γ : SL(2, ℤ)) : σ' M K γ = 1 ↔ γ ∈ Gpm M := by
  rw [← MonoidHom.mem_ker, σ'_ker]

private theorem σ'_surjective : Function.Surjective (σ' M K) := by
  haveI := finiteDimensional_jK M K
  haveI := isGalois_jK M K
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, σ'_ker, ← finrank_jK M K, IsGalois.card_aut_eq_finrank]

private theorem exists_place_infty :
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

private theorem exists_place_elliptic (τ₀ : ℍ) (Kst : Subgroup SL(2, ℤ)) (hKst : ∀ k ∈ Kst, k • τ₀ = τ₀) :
    ∃ W : AlgebraicCurve.Place ℂ K, 0 < W.ord (jK M K - algebraMap ℂ K (LevelN.jAnalytic τ₀)) ∧
      ∀ k ∈ Kst, AlgebraicCurve.SemilinearAut.ofAlgAut ((σ' M K k).restrictScalars ℂ) • W = W := by
  obtain ⟨W, hW, hWfix⟩ := ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq M K τ₀
  refine ⟨W, hW, ?_⟩
  intro k hk
  rw [restrictScalars_σ']
  exact hWfix k (hKst k hk) (comp_smul_mem M K k⁻¹) (σK M K k) (σK_algebraMap M K k)

end LevelN

section ConstantField

variable {F : Type*} [Field F]
variable {L : Type*} [Field L] [Algebra ℂ L] (t : L) (E : IntermediateField ℂ⟮t⟯ L) [Algebra F E]

private theorem adjoin_adjoin_subset {L : Type*} [Field L] [Algebra ℂ L] (S : Set L) (t : L)
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

private theorem adjoin_range_eq_top
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

private theorem isDomain_ring : IsDomain (LevelN.ring M) := by
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
variable (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

include K hΓ in
set_option maxHeartbeats 1600000 in

private theorem natCard_place_ord_lt_zero_le (ι : ℚ̄ →+* ℂ) (y : FF) (hy : (y : LaurentSeries ℚ̄) = jqModC ℚ̄) :
    Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // P.ord y < 0} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) := by
  classical
  haveI := finiteDimensional_jK M K
  haveI := isGalois_jK M K
  haveI hKc : CharZero ℚ̄ := charZero_of_injective_algebraMap (algebraMap ℚ ℚ̄).injective
  haveI hΓfi1 : (CongruenceSubgroup.Gamma1 M).FiniteIndex :=
    (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  haveI hΓfi : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hΓM : CongruenceSubgroup.Gamma M ≤ Γ := (Gamma_le_Gamma1 M).trans hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (T_mem_Gamma1 M)

  obtain ⟨Φ, hΦc, hΦy, hΦfix⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN M
      Γ hΓM hT ι K
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
      ℚ̄ Γ hT y hy
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

  have hσE : ∀ γ ∈ Γ, ∀ e : E, σ' M K γ (e : K) = e := by
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
    (σ'_surjective M K) Γ
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) E hσE 0 W hW hD xE⁻¹ rfl
  rw [Nat.card_congr eqv] at h2
  exact h1.trans h2

include K hΓ in
set_option maxHeartbeats 1600000 in

private theorem natCard_place_ord_sub_pos_le (ι : ℚ̄ →+* ℂ) (y : FF) (hy : (y : LaurentSeries ℚ̄) = jqModC ℚ̄)
    (τ₀ : ℍ) (Kst : Subgroup SL(2, ℤ)) (hKst : ∀ k ∈ Kst, k • τ₀ = τ₀)
    (c : ℚ̄) (hc : ι c = LevelN.jAnalytic τ₀) :
    Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // 0 < P.ord (y - algebraMap ℚ̄ FF c)} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (Kst : Set SL(2, ℤ))) := by
  classical
  haveI := finiteDimensional_jK M K
  haveI := isGalois_jK M K
  haveI hKc : CharZero ℚ̄ := charZero_of_injective_algebraMap (algebraMap ℚ ℚ̄).injective
  haveI hΓfi1 : (CongruenceSubgroup.Gamma1 M).FiniteIndex :=
    (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  haveI hΓfi : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hΓM : CongruenceSubgroup.Gamma M ≤ Γ := (Gamma_le_Gamma1 M).trans hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (T_mem_Gamma1 M)

  obtain ⟨Φ, hΦc, hΦy, hΦfix⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN M
      Γ hΓM hT ι K
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
      ℚ̄ Γ hT y hy
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

  have hσE : ∀ γ ∈ Γ, ∀ e : E, σ' M K γ (e : K) = e := by
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
  have hyc0 : y - algebraMap ℚ̄ FF c ≠ 0 := fun h => by
    apply hyT
    have : y = algebraMap ℚ̄ FF c := sub_eq_zero.mp h
    rw [this]; exact isAlgebraic_algebraMap c
  haveI hfinE' : Finite {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c))} :=
    ((hplaces _ hyc0).1).1

  have hDC := fun P : AlgebraicCurve.Place ℚ̄ FF =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension ℚ̄ FF ℂ E
      ⟨y, hyT, hfin⟩ ⟨xE, hxT, hxfin⟩ hgen P
  choose lift hcomap hord huniq using hDC
  have hinj : Function.Injective lift := fun P₁ P₂ h =>
    AlgebraicCurve.Place.ext (by rw [← hcomap P₁, ← hcomap P₂, h])
  let ι' : {P : AlgebraicCurve.Place ℚ̄ FF // 0 < P.ord (y - algebraMap ℚ̄ FF c)} →
      {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c))} :=
    fun P => ⟨lift P.1, by rw [hord]; exact P.2⟩
  have hι' : Function.Injective ι' := fun P₁ P₂ h =>
    Subtype.ext (hinj (congrArg (fun Q : {P : AlgebraicCurve.Place ℂ E //
      0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c))} => Q.1) h))
  have h1 : Nat.card {P : AlgebraicCurve.Place ℚ̄ FF // 0 < P.ord (y - algebraMap ℚ̄ FF c)} ≤
      Nat.card {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c))} :=
    Nat.card_le_card_of_injective ι' hι'

  obtain ⟨W, hW, hD⟩ := exists_place_elliptic M K τ₀ Kst hKst
  have halg : algebraMap FF E (y - algebraMap ℚ̄ FF c) = xE - algebraMap ℂ E (LevelN.jAnalytic τ₀) := by
    rw [map_sub, hΦEy, ← hc]
    congr 1
    exact (IsScalarTower.algebraMap_apply ℚ̄ FF E c).symm.trans (IsScalarTower.algebraMap_apply ℚ̄ ℂ E c)
  have hiff : ∀ P : AlgebraicCurve.Place ℂ E,
      0 < P.ord (xE - algebraMap ℂ E (LevelN.jAnalytic τ₀)) ↔
        0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c)) := by
    intro P; rw [halg]
  let eqv : {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (xE - algebraMap ℂ E (LevelN.jAnalytic τ₀))} ≃
      {P : AlgebraicCurve.Place ℂ E // 0 < P.ord (algebraMap FF E (y - algebraMap ℚ̄ FF c))} :=
    Equiv.subtypeEquivRight hiff
  have h2 := natCard_place_le_natCard_doubleCoset (jK M K) L₀ rfl (σ' M K)
    (σ'_surjective M K) Γ Kst E hσE (LevelN.jAnalytic τ₀) W hW hD xE rfl
  rw [Nat.card_congr eqv] at h2
  exact h1.trans h2

end Main

end ModularCurve.FibresGamma
p2m_reactivate "P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve.FibresGamma"
p2m_reactivate "P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jGen laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq LevelN.exists_place_ord_sub_pos_forall_smul_eq exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN natCard_doubleCoset_le_card_fibres_of_finrank_eq_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC"
namespace EllipticPoints
p2m_open "ModularCurve"

private def rho : ℍ := ⟨⟨-1/2, Real.sqrt 3 / 2⟩, by
  show 0 < Real.sqrt 3 / 2
  positivity⟩

private theorem coe_rho : (rho : ℂ) = ⟨-1/2, Real.sqrt 3 / 2⟩ := rfl

private theorem rho_sq_add : (rho : ℂ) ^ 2 + rho + 1 = 0 := by
  rw [coe_rho]
  apply Complex.ext
  · simp [sq, Complex.mul_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith [h3]
  · simp [sq, Complex.mul_im]
    ring

private theorem im_rho : (rho : ℂ).im = Real.sqrt 3 / 2 := rfl

private theorem sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private theorem rho_add_one_ne_zero : (rho : ℂ) + 1 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  rw [Complex.add_im, im_rho, Complex.one_im, Complex.zero_im] at h1
  have := sqrt3_pos
  linarith

private theorem S_mul_T_smul_rho : (ModularGroup.S * ModularGroup.T) • rho = rho := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h00 : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 0 = 0 := by
    change ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0; rw [hST]; rfl
  have h01 : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 1 = -1 := by
    change ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -1; rw [hST]; rfl
  have h10 : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 = 1 := by
    change ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1; rw [hST]; rfl
  have h11 : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 1 = 1 := by
    change ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1; rw [hST]; rfl
  rw [h00, h01, h10, h11]
  simp only [map_zero, map_neg, map_one, Complex.ofReal_zero, Complex.ofReal_neg, Complex.ofReal_one, zero_mul,
    zero_add, one_mul]
  rw [div_eq_iff (rho_add_one_ne_zero), eq_comm, ← sub_eq_zero]
  have := rho_sq_add
  linear_combination this

private theorem rho_add_one_pow_four_ne_one : ((rho : ℂ) + 1) ^ 4 ≠ 1 := by
  have h2 : ((rho : ℂ) + 1) ^ 2 = rho := by linear_combination rho_sq_add
  have h4 : ((rho : ℂ) + 1) ^ 4 = -rho - 1 := by
    calc ((rho : ℂ) + 1) ^ 4 = (((rho : ℂ) + 1) ^ 2) ^ 2 := by ring
      _ = (rho : ℂ) ^ 2 := by rw [h2]
      _ = -rho - 1 := by linear_combination rho_sq_add
  rw [h4]
  intro h
  have h1 := congrArg Complex.im h
  rw [Complex.sub_im, Complex.neg_im, im_rho, Complex.one_im] at h1
  have := sqrt3_pos
  linarith

private theorem E₄_rho : ModularForm.E₄ rho = 0 := by
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    ⟨_, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) hmem rho
  have hsm : (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) • rho =
      (ModularGroup.S * ModularGroup.T) • rho := rfl
  rw [hsm, S_mul_T_smul_rho] at h
  have hval : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.cast : ℤ → ℝ) := rfl
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) rho =
      (rho : ℂ) + 1 := by
    show (((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (rho : ℂ) + (((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = (rho : ℂ) + 1
    rw [hval, Matrix.map_apply, Matrix.map_apply, hST]
    simp
  rw [hden] at h

  have : ((rho : ℂ) + 1) ^ (4 : ℤ) = ((rho : ℂ) + 1) ^ 4 := by norm_cast
  rw [this] at h
  by_contra hne
  apply rho_add_one_pow_four_ne_one
  have := mul_right_cancel₀ hne (h.symm.trans (one_mul _).symm)
  exact this

private theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  have h00 : (ModularGroup.S : SL(2, ℤ)) 0 0 = 0 := by
    change ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0; rw [ModularGroup.coe_S]; rfl
  have h01 : (ModularGroup.S : SL(2, ℤ)) 0 1 = -1 := by
    change ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -1; rw [ModularGroup.coe_S]; rfl
  have h10 : (ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by
    change ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1; rw [ModularGroup.coe_S]; rfl
  have h11 : (ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by
    change ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0; rw [ModularGroup.coe_S]; rfl
  rw [h00, h01, h10, h11]
  simp only [map_zero, map_neg, map_one, Complex.ofReal_zero, Complex.ofReal_neg, Complex.ofReal_one, zero_mul,
    zero_add, one_mul, add_zero, UpperHalfPlane.coe_I]
  rw [div_eq_iff Complex.I_ne_zero, Complex.I_mul_I]

private theorem E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨_, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' (ModularForm.E₆) hmem UpperHalfPlane.I
  have hsm : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) • UpperHalfPlane.I =
      ModularGroup.S • UpperHalfPlane.I := rfl
  rw [hsm, S_smul_I] at h
  have hval : ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) UpperHalfPlane.I =
      Complex.I := by
    show (((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) *
        (UpperHalfPlane.I : ℂ) +
      (((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = Complex.I
    rw [hval, Matrix.map_apply, Matrix.map_apply, ModularGroup.coe_S]
    simp
  rw [hden] at h
  have hI6 : (Complex.I) ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    calc Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [hI6, neg_one_mul] at h

  linear_combination h / 2

private theorem jAnalytic_rho : ModularCurve.LevelN.jAnalytic rho = 0 := by
  rw [ModularCurve.LevelN.jAnalytic, E₄_rho]; simp

private theorem jAnalytic_I : ModularCurve.LevelN.jAnalytic UpperHalfPlane.I = 1728 := by
  rw [ModularCurve.LevelN.jAnalytic]
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  have hΔ0 := ModularForm.discriminant_ne_zero UpperHalfPlane.I
  rw [E₆_I] at hΔ
  rw [div_eq_iff hΔ0, hΔ]
  ring

end ModularCurve.EllipticPoints
p2m_reactivate "P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve.FibresGamma"
p2m_reactivate "P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve.FibresGamma"

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC jGen laurentBaseChange jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq LevelN.exists_place_ord_sub_pos_forall_smul_eq exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN natCard_doubleCoset_le_card_fibres_of_finrank_eq_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC" namespace FibresGamma end ModularCurve.FibresGamma
p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve ModularCurve.FibresGamma ModularCurve.EllipticPoints CongruenceSubgroup AlgebraicCurve in
private theorem ModularCurve.FibresGamma.fibre_zero_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord y} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by
  haveI := isDomain_ring M
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom
  have hKst : ∀ k ∈ Subgroup.zpowers (ModularGroup.S * ModularGroup.T), k • rho = rho := fun k hk =>
    (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr S_mul_T_smul_rho) hk :)
  have h := natCard_place_ord_sub_pos_le M (FractionRing (LevelN.ring M)) Γ hΓ ι y hy rho
    (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) hKst 0 (by rw [map_zero, jAnalytic_rho])
  simpa only [map_zero, sub_zero] using h

p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve ModularCurve.FibresGamma ModularCurve.EllipticPoints CongruenceSubgroup AlgebraicCurve in
private theorem ModularCurve.FibresGamma.fibre_1728_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord (y - 1728)} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by
  haveI := isDomain_ring M
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom
  have hKst : ∀ k ∈ Subgroup.zpowers ModularGroup.S, k • UpperHalfPlane.I = UpperHalfPlane.I := fun k hk =>
    (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr S_smul_I) hk :)
  have h := natCard_place_ord_sub_pos_le M (FractionRing (LevelN.ring M)) Γ hΓ ι y hy UpperHalfPlane.I
    (Subgroup.zpowers ModularGroup.S) hKst 1728 (by rw [map_ofNat, jAnalytic_I])
  have h1728 : (algebraMap (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) 1728) = 1728 :=
    map_ofNat _ 1728
  rw [h1728] at h
  exact h

p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve ModularCurve.FibresGamma CongruenceSubgroup AlgebraicCurve in
private theorem ModularCurve.FibresGamma.fibre_pole_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // P.ord y < 0} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by
  haveI := isDomain_ring M
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom
  exact natCard_place_ord_lt_zero_le M (FractionRing (LevelN.ring M)) Γ hΓ ι y hy

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve ModularCurve.FibresGamma CongruenceSubgroup AlgebraicCurve in

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) =
        (Γ ⊔ Subgroup.zpowers (-1)).index) :
    Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord y} =
        Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord (y - 1728)} =
        Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) // P.ord y < 0} =
        Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by
  obtain ⟨h1, h2, h3⟩ :=
    ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index M Γ hΓ y hy hfull
  exact ⟨le_antisymm (ModularCurve.FibresGamma.fibre_zero_le M Γ hΓ y hy) h1,
    le_antisymm (ModularCurve.FibresGamma.fibre_1728_le M Γ hΓ y hy) h2,
    le_antisymm (ModularCurve.FibresGamma.fibre_pole_le M Γ hΓ y hy) h3⟩

end
p2m_reactivate "P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index.ModularCurve.FibresGamma"

end S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
end P2MW
export P2MW.S_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index (solution)

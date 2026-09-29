-- Prove2me | solution 1 for ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b97b09c2-cf85-5b96-abb4-cc1150c41196

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure.ModularCurve"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jGen coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff jqModC map_jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_jGen_le_two_three_level JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728"
namespace UBAux
p2m_open "ModularCurve"

section CoeffLift

variable {L : Type*} [Field L] {Ω : Type*} [Field Ω] [Algebra ℚ L] [Algebra ℚ Ω] (τ : L →ₐ[ℚ] Ω)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_coeffEmb' (x : LaurentSeries ℚ) : coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x := by
  change coeffMap _ (coeffMap _ x) = coeffMap _ x
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem coeffMap_algebraMap' (c : L) :
    coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange Ω F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange Ω F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Ω hz
  | one => simp
  | add _ _ _ _ hx hy => simpa using add_mem hx hy
  | neg _ _ hx => simpa using neg_mem hx
  | inv _ _ hx => simpa using inv_mem hx
  | mul _ _ _ _ hx hy => simpa using mul_mem hx hy

@[reducible] def algebraOfLift : Algebra L ↥(laurentBaseChange Ω F₀) :=
  ((algebraMap Ω ↥(laurentBaseChange Ω F₀)).comp τ.toRingHom).toAlgebra

def liftRingHom : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange Ω F₀) :=
  ((coeffMap τ.toRingHom).comp (laurentBaseChange L F₀).toSubring.subtype).codRestrict
    (laurentBaseChange Ω F₀).toSubring (fun x => coeffMap_mem_laurentBaseChange' τ F₀ x.2)

theorem coe_liftRingHom (x : ↥(laurentBaseChange L F₀)) :
    ((liftRingHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

def liftHom : letI := algebraOfLift τ F₀; ↥(laurentBaseChange L F₀) →ₐ[L] ↥(laurentBaseChange Ω F₀) :=
  letI := algebraOfLift τ F₀
  { liftRingHom τ F₀ with
    commutes' := fun c => Subtype.ext (by
      change coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c)
      exact coeffMap_algebraMap' τ c) }

theorem coe_liftHom (x : ↥(laurentBaseChange L F₀)) :
    letI := algebraOfLift τ F₀; ((liftHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

theorem liftHom_toRingHom : letI := algebraOfLift τ F₀; (liftHom τ F₀).toRingHom = liftRingHom τ F₀ := rfl

set_option synthInstance.maxHeartbeats 1600000 in

theorem adjoin_range_liftRingHom_eq_top :
    IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  let T : IntermediateField Ω ↥(laurentBaseChange Ω F₀) := IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀))
  let T' : Subfield (LaurentSeries Ω) := T.toSubfield.map (laurentBaseChange Ω F₀).val.toRingHom
  have hgens : Set.range (algebraMap Ω (LaurentSeries Ω)) ∪ (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ))) ⊆ T' := by
    rintro w (⟨a, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨algebraMap Ω ↥(laurentBaseChange Ω F₀) a, T.algebraMap_mem a, rfl⟩
    · refine ⟨liftRingHom τ F₀ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩,
        IntermediateField.subset_adjoin Ω _ ⟨_, rfl⟩, ?_⟩
      change coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x
      exact coeffMap_coeffEmb' τ x
  have hle : Subfield.closure (Set.range (algebraMap Ω (LaurentSeries Ω)) ∪
      (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ)))) ≤ T' := Subfield.closure_le.mpr hgens
  obtain ⟨w, hw, hwz⟩ := hle (mem_laurentBaseChange_iff.mp z.2)
  have : w = z := Subtype.ext hwz
  rw [← this]
  exact hw

end CoeffLift

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

section Generic

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem ord_sub_algebraMap_le_one_algebraicClosure (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a : AlgebraicClosure ℚ) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1 := by
  classical
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQFC : Algebra (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) := algebraOfLift ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let Ψ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+* ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) := liftRingHom ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  letI algFF : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) := Ψ.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((liftHom ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)).commutes c).symm
  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) := isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd
  obtain ⟨x₁, hx₁tr, hx₁fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ Γ hT
  have hgenC : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)))) = ⊤ :=
    adjoin_range_liftRingHom_eq_top ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  obtain ⟨P'', -, hP''ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) ⟨x₀, hx₀tr, hx₀fd⟩ ⟨x₁, hx₁tr, hx₁fd⟩ hgenC P

  have hyC : ((Ψ y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := by
    rw [coe_liftRingHom, hy]
    exact map_jqModC ι
  have hιa0 : ι a ≠ 0 := fun h => ha0 (ι.injective (by rw [h, map_zero]))
  have hιa1728 : ι a ≠ 1728 := fun h => ha1728 (ι.injective (by rw [h, map_ofNat]))
  have hle1 := ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
    M Γ hΓ (Ψ y) hyC (ι a) hιa0 hιa1728 P''
  have htrans : P''.ord (Ψ y - algebraMap ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) (ι a)) =
      P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) := by
    rw [← hP''ord, map_sub, ← IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) a,
      IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) a]
    rfl
  rw [htrans] at hle1
  exact hle1

end Generic

end ModularCurve.UBAux

open ModularCurve.UBAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    P.ord y ≤ 3 ∧
    P.ord (y - 1728) ≤ 2 ∧
    (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 →
      P.ord (y - algebraMap (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1) := by
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
    convert hp using 2
    rfl
  let ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom

  have hΓM : CongruenceSubgroup.Gamma M ≤ Γ := by
    refine le_trans (fun γ hγ => ?_) hΓ
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩
  have hT : ModularGroup.T ∈ Γ := hΓ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])

  obtain ⟨Φ, hΦc, hΦy, -⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN M Γ hΓM hT ι K

  obtain ⟨hst, σ, hσ, hker, hfix, htr, hfd, hdeg, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin M K

  obtain ⟨⟨W1728, hW1728pos, hW1728⟩, ⟨W0, hW0pos, hW0⟩, -⟩ :=
    ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level M K

  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  let t : K := algebraMap ↥(ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)
  have hΦy' : Φ y = t := hΦy y hy
  let E : IntermediateField ℂ K := IntermediateField.adjoin ℂ (Set.range Φ)
  have hΦmem : ∀ f, Φ f ∈ E := fun f => IntermediateField.subset_adjoin ℂ _ ⟨f, rfl⟩
  let ΦE : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+* ↥E := Φ.codRestrict E hΦmem
  have hΦE : ∀ f, ((ΦE f : ↥E) : K) = Φ f := fun f => RingHom.codRestrict_apply Φ E hΦmem f
  have hcoeC : ∀ z : ℂ, ((algebraMap ℂ ↥E z : ↥E) : K) = algebraMap ℂ K z := fun _ => rfl
  letI algFE : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E := ΦE.toAlgebra
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQE : Algebra (AlgebraicClosure ℚ) ↥E := ((algebraMap ℂ ↥E).comp ι).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (by
      change ((algebraMap ℂ ↥E (ι c) : ↥E) : K) = ((ΦE (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) : ↥E) : K)
      rw [hcoeC, hΦE, hΦc])
  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) := isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd

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
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E)) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have : Subtype.val '' Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E) = Set.range Φ := by
      ext w
      constructor
      · rintro ⟨_, ⟨f, rfl⟩, rfl⟩; exact ⟨f, (hΦE f).symm⟩
      · rintro ⟨f, rfl⟩; exact ⟨ΦE f, ⟨f, rfl⟩, hΦE f⟩
    rw [this]
  obtain ⟨P', -, hP'ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ℂ ↥E ⟨x₀, hx₀tr, hx₀fd⟩ ⟨ΦE y, htr', hEfd⟩ hgen P

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
  have keyUB : ∀ (j₀ : ℂ) (W₀ : Place ℂ K), 0 < W₀.ord (t - algebraMap ℂ K j₀) →
      ∀ w : Place ℂ ↥E, 0 < w.ord (ΦE y - algebraMap ℂ ↥E j₀) →
        w.ord (ΦE y - algebraMap ℂ ↥E j₀) ≤ W₀.ord (t - algebraMap ℂ K j₀) := by
    intro j₀ W₀ hW₀ w hw
    obtain ⟨h1, -, h3, h4, h5⟩ := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ (ΦE y) t j₀ E.val hvaly
      hfd hgal hint W₀ hW₀
    obtain ⟨ψ, hψ, rfl⟩ := h3 w hw
    rw [h5 ψ hψ, h1]

    haveI : Finite {σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
        SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀} := Subtype.finite
    have htmem : t ∈ IntermediateField.adjoin ℂ ({t} : Set K) := IntermediateField.mem_adjoin_simple_self ℂ t
    have hσt : ∀ σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K, σ t = t := fun σ =>
      σ.commutes (⟨t, htmem⟩ : ↥(IntermediateField.adjoin ℂ ({t} : Set K)))
    let g : {σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
          SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀} →
        {ψ' : {ψ' : ↥E →ₐ[ℂ] K // ψ' (ΦE y) = t} //
          W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := fun σ =>
      have hψσ : (((σ.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ) (ΦE y) = t := by
        rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hψ]; exact hσt σ.1
      ⟨⟨((σ.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ, hψσ⟩,
        ((h4 ψ _ hψ hψσ).mpr ⟨σ.1, σ.2, rfl⟩).symm⟩
    have hg : Function.Surjective g := by
      rintro ⟨⟨ψ', hψ'⟩, heq⟩
      obtain ⟨σ, hσ, rfl⟩ := (h4 ψ ψ' hψ hψ').mp heq.symm
      exact ⟨⟨σ, hσ⟩, rfl⟩
    exact_mod_cast Nat.card_le_card_of_surjective g hg

  have h0E : P'.ord (ΦE y) = P.ord y := by rw [← hP'ord y]; rfl
  have h1728E : P'.ord (ΦE y - 1728) = P.ord (y - 1728) := by rw [← hP'ord (y - 1728), map_sub, map_ofNat]; rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    by_cases hpos : 0 < P.ord y
    · have hk := keyUB 0 W0 (by rw [map_zero, sub_zero]; exact hW0pos) P'
      simp only [map_zero, sub_zero] at hk
      rw [h0E] at hk
      exact (hk hpos).trans hW0
    · linarith
  ·
    by_cases hpos : 0 < P.ord (y - 1728)
    · have hk := keyUB 1728 W1728 (by rw [map_ofNat]; exact hW1728pos) P'
      simp only [map_ofNat] at hk
      rw [h1728E] at hk
      exact (hk hpos).trans hW1728
    · linarith
  ·
    intro a ha0 ha1728
    exact ord_sub_algebraMap_le_one_algebraicClosure M Γ hΓ hT ιa y hy P a ha0 ha1728

end
end S_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
end P2MW
export P2MW.S_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure (solution)

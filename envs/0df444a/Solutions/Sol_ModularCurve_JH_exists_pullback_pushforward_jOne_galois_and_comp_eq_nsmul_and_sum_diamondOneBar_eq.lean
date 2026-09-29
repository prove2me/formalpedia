-- Prove2me | solution 1 for ModularCurve.JH.exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2700091c-6d1c-56ea-9211-02ca7492aa35

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ShimuraCovering
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff
import Theorems.Thm_ModularCurve_laurentBaseChange_deck_galois_package
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_Pic0_pushforwardAlongHom_smul
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_eq_finrankAlong_smul
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.AlgebraicCurve IntermediateField"
open scoped MatrixGroups

namespace K1Transfer

local notation "ℚbar" => AlgebraicClosure ℚ

section Reps

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (S : Finset ℕ) (hS : ∀ d ∈ S, Nat.Coprime d M)
  (hSH : ∀ (d : ℕ) (hd : d ∈ S), ZMod.unitOfCoprime d (hS d hd) ∈ H)
  (hHS : ∀ h ∈ H, ∃! d : ℕ, d ∈ S ∧ (d : ZMod M) = ((h : (ZMod M)ˣ) : ZMod M))

def rep (u : H) : ℕ := (hHS u u.2).exists.choose

theorem rep_mem (u : H) : rep S hHS u ∈ S := (hHS u u.2).exists.choose_spec.1

theorem natCast_rep (u : H) : ((rep S hHS u : ℕ) : ZMod M) = ((u : (ZMod M)ˣ) : ZMod M) :=
  (hHS u u.2).exists.choose_spec.2

theorem rep_injective : Function.Injective (rep S hHS) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  rw [← natCast_rep S hHS u, ← natCast_rep S hHS v, h]

include hSH in
theorem rep_unitOfCoprime {d : ℕ} (hd : d ∈ S) :
    rep S hHS ⟨ZMod.unitOfCoprime d (hS d hd), hSH d hd⟩ = d := by
  apply (hHS _ (hSH d hd)).unique
  · exact ⟨rep_mem S hHS _, natCast_rep S hHS _⟩
  · exact ⟨hd, (ZMod.coe_unitOfCoprime d (hS d hd)).symm⟩

include hSH in
theorem image_rep_eq [Fintype H] [DecidableEq ℕ] : Finset.univ.image (rep S hHS) = S := by
  ext d
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩; exact rep_mem S hHS u
  · intro hd; exact ⟨_, rep_unitOfCoprime S hS hSH hHS hd⟩

include hSH in
theorem sum_S_eq [Fintype H] {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ d ∈ S, f d = ∑ u : H, f (rep S hHS u) := by
  classical
  have h1 : ∑ d ∈ S, f d = ∑ d ∈ Finset.univ.image (rep S hHS), f d := by
    rw [image_rep_eq S hS hSH hHS]
  rw [h1, Finset.sum_image fun u _ v _ h => rep_injective S hHS h]

include hSH hHS in
theorem card_S_eq [Fintype H] : S.card = Fintype.card H := by
  classical
  have h1 : S.card = (Finset.univ.image (rep S hHS)).card := by rw [image_rep_eq S hS hSH hHS]
  rw [h1, Finset.card_image_of_injective _ (rep_injective S hHS), Finset.card_univ]

end Reps

section DiamondCongr

variable (M : ℕ)

theorem isDiamondAut_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    IsDiamondAut M d = IsDiamondAut M d' := by
  have hc : Nat.Coprime d M ↔ Nat.Coprime d' M := by
    rw [← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, h]
  funext σ
  simp only [IsDiamondAut, hc, h]

theorem diamondAut_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    diamondAut M d = diamondAut M d' := by
  let G : ((x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) → Prop) →
      (x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) := fun P =>
    haveI := Classical.dec (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, P σ)
    if h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, P σ then h.choose else AlgEquiv.refl
  have hG : ∀ e : ℕ, diamondAut M e = G (IsDiamondAut M e) := fun e => rfl
  rw [hG, hG, isDiamondAut_congr M h]

theorem diamondAutBar_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    diamondAutBar M d = diamondAutBar M d' := by
  rw [diamondAutBar, diamondAutBar, diamondAut_congr M h]

end DiamondCongr

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem isBaseChangeAutOf_unique {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {σ σ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ σ) (h' : IsBaseChangeAutOf L σ₀ σ') : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Subtype.ext
      exact (h ⟨z, hz⟩).trans (h' ⟨z, hz⟩).symm
  | algebraMap c =>
      have : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ :
          laurentBaseChange L F₀) = algebraMap L (laurentBaseChange L F₀) c := rfl
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

variable (L) [Algebra.IsAlgebraic ℚ L]

theorem baseChangeAut_eq_geomAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    baseChangeAut L σ₀ = geomAut L F₀ σ₀ := by
  have hgeom : IsBaseChangeAutOf L σ₀ (geomAut L F₀ σ₀) := fun y =>
    coe_geomAut_coeffEmb L F₀ σ₀ y
  exact isBaseChangeAutOf_unique (isBaseChangeAutOf_baseChangeAut ⟨_, hgeom⟩) hgeom

theorem diamondAutBar_eq_geomAut (M d : ℕ) :
    diamondAutBar M d = geomAut ℚbar (x1FunctionField M) (diamondAut M d) :=
  baseChangeAut_eq_geomAut ℚbar (diamondAut M d)

end BaseChange

section GaloisAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem sum_subgroup_smul_eq_pullbackAlong_pushforwardAlong
    (ι : F →ₐ[K] F') (H : Subgroup (F' ≃ₐ[K] F')) [Fintype H]
    (hrange : ι.fieldRange = IntermediateField.fixedField H) (hfin : FiniteAlong K ι)
    [HasPrincipalDivisors K F'] (hint : ι.toRingHom.IsIntegral) (D : Divisor K F') :
    ∑ h : H, SemilinearAut.ofAlgAut (h : F' ≃ₐ[K] F') • D
      = Divisor.pullbackAlong ι hint (Divisor.pushforwardAlong ι hint D) := by
  classical
  haveI : Finite H := inferInstance
  letI : Algebra F F' := algebraAlong ι
  haveI : IsScalarTower K F F' := isScalarTower_along ι
  haveI hfd : Module.Finite F F' := hfin

  haveI : IsGalois F F' := by
    haveI hG : IsGalois (IntermediateField.fixedField H) F' := IsGalois.of_fixed_field F' H
    let e₁ : F ≃ₐ[K] ι.fieldRange :=
      (AlgEquiv.ofInjectiveField ι).trans (Subalgebra.equivOfEq _ _ ι.fieldRange_toSubalgebra.symm)
    let e₂ : ι.fieldRange ≃ₐ[K] IntermediateField.fixedField H :=
      IntermediateField.equivOfEq hrange
    let f : IntermediateField.fixedField H ≃+* F := (e₁.trans e₂).symm.toRingEquiv
    refine IsGalois.of_equiv_equiv (F := IntermediateField.fixedField H) (E := F')
      (f := f) (g := RingEquiv.refl F') (RingHom.ext fun y => ?_)
    have lhs : ((algebraMap F F').comp (f : IntermediateField.fixedField H →+* F)) y
        = ι ((e₁.trans e₂).symm y) := rfl
    have rhs : ((RingEquiv.refl F' : F' →+* F').comp
        (algebraMap (IntermediateField.fixedField H) F')) y = (y : F') := rfl
    rw [lhs, rhs]
    have hy : (e₁.trans e₂) ((e₁.trans e₂).symm y) = y := AlgEquiv.apply_symm_apply _ y
    have key : ∀ b : F, ((e₁.trans e₂) b : F') = ι b := fun b => rfl
    rw [← key, hy]

  have hB3 := AlgebraicCurve.Divisor.sum_galois_smul_eq_pullback_pushforward
    (K := K) (F := F) (F' := F') D
  have hR : Divisor.pullback F' (Divisor.pushforward F D)
      = Divisor.pullbackAlong ι hint (Divisor.pushforwardAlong ι hint D) := rfl
  rw [hR] at hB3

  have hιfix : ∀ (h : H) (x : F), (h : F' ≃ₐ[K] F') (ι x) = ι x := by
    intro h x
    have hx : ι x ∈ IntermediateField.fixedField H := by
      rw [← hrange]; exact ⟨x, rfl⟩
    exact (IntermediateField.mem_fixedField_iff H _).mp hx h h.2
  have hσfix : ∀ (σ : F' ≃ₐ[F] F') (y : F'), y ∈ IntermediateField.fixedField H → σ y = y := by
    intro σ y hy
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact σ.commutes x
  have hmemH : ∀ σ : F' ≃ₐ[F] F', σ.restrictScalars K ∈ H := by
    intro σ
    let τ : F' ≃ₐ[FixedPoints.subfield H F'] F' :=
      { σ.toRingEquiv with commutes' := fun y => hσfix σ y y.2 }
    obtain ⟨h, hh⟩ := FixedPoints.toAlgAut_surjective H F' τ
    have hστ : σ.restrictScalars K = (h : F' ≃ₐ[K] F') := by
      apply AlgEquiv.ext
      intro x
      have := AlgEquiv.congr_fun hh x
      rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply] at this
      exact this.symm
    rw [hστ]; exact h.2
  let toH : (F' ≃ₐ[F] F') → H := fun σ => ⟨σ.restrictScalars K, hmemH σ⟩
  have htoH : Function.Bijective toH := by
    constructor
    · intro σ σ' hσ
      exact AlgEquiv.restrictScalars_injective K (congrArg Subtype.val hσ)
    · rintro ⟨h, hh⟩
      refine ⟨{ (h : F' ≃ₐ[K] F').toRingEquiv with commutes' := fun x => hιfix ⟨h, hh⟩ x }, ?_⟩
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      rfl
  have hsumH : ∑ σ : F' ≃ₐ[F] F', SemilinearAut.ofAlgAut (σ.restrictScalars K) • D
      = ∑ h : H, SemilinearAut.ofAlgAut (h : F' ≃ₐ[K] F') • D :=
    Fintype.sum_bijective toH htoH _ _ (fun σ => rfl)
  rw [← hsumH, hB3]

end GaloisAlong

section FixAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem algEquiv_comp_eq_of_mem (ι : F →ₐ[K] F') (H : Subgroup (F' ≃ₐ[K] F'))
    (hrange : ι.fieldRange = IntermediateField.fixedField H) {τ : F' ≃ₐ[K] F'} (hτ : τ ∈ H) (x : F) :
    τ (ι x) = ι x := by
  have hx : ι x ∈ IntermediateField.fixedField H := by
    rw [← hrange]; exact ⟨x, rfl⟩
  exact (IntermediateField.mem_fixedField_iff H _).mp hx τ hτ

end FixAlong

section Fibres

variable {G G' A : Type*} [Group G] [Fintype G] [Group G'] [DecidableEq G'] [AddCommMonoid A]

theorem sum_comp_monoidHom_eq_card_ker_smul (φ : G →* G') (f : G' → A) :
    ∑ u : G, f (φ u)
      = (Finset.univ.filter (fun u : G => φ u = 1)).card • ∑ h ∈ Finset.univ.image φ, f h := by
  rw [Finset.sum_comp f φ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  congr 1
  apply MonoidHom.card_fiber_eq_of_mem_range φ
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨u, rfl⟩
  · exact ⟨1, map_one φ⟩

theorem sum_image_eq_sum_range (φ : G →* G') [Fintype φ.range] (f : G' → A) :
    ∑ h ∈ Finset.univ.image φ, f h = ∑ h : φ.range, f (h : G') := by
  apply Finset.sum_subtype
  intro h
  simp only [Finset.mem_image, Finset.mem_univ, true_and, MonoidHom.mem_range]

end Fibres

section KerCount

variable {G G' : Type*} [Group G] [Fintype G] [Group G'] [DecidableEq G']

theorem card_filter_eq_one_eq_card_ker (φ : G →* G') :
    (Finset.univ.filter (fun u : G => φ u = 1)).card = Nat.card φ.ker := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [MonoidHom.mem_ker]

theorem sum_comp_eq_card_ker_smul_sum_range {A : Type*} [AddCommMonoid A] (φ : G →* G')
    [Fintype φ.range] (f : G' → A) :
    ∑ u : G, f (φ u) = Nat.card φ.ker • ∑ h : φ.range, f (h : G') := by
  classical
  rw [sum_comp_monoidHom_eq_card_ker_smul, card_filter_eq_one_eq_card_ker, sum_image_eq_sum_range]

theorem card_ker_mul_card_range (φ : G →* G') :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

end KerCount

section Descent

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def mkHom : Divisor.degZero (K := K) (F := F) →+ Pic0 K F where
  toFun := Pic0.mk
  map_zero' := Pic0.mk_zero
  map_add' := Pic0.mk_add

@[scoped simp] theorem mkHom_apply (D : Divisor.degZero (K := K) (F := F)) : mkHom D = Pic0.mk D := rfl

theorem mk_sum {ι : Type*} (s : Finset ι) (D : ι → Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (∑ i ∈ s, D i) = ∑ i ∈ s, Pic0.mk (D i) := by
  rw [← mkHom_apply, map_sum]; rfl

theorem mk_nsmul (n : ℕ) (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (n • D) = n • Pic0.mk D := by
  rw [← mkHom_apply, map_nsmul]; rfl

variable [HasPrincipalDivisors K F']
  (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
  (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)

theorem pushforwardAlongHom_pullbackAlongHom
    (hdiv : ∀ D : Divisor K F, Divisor.pushforwardAlong φ hφ (Divisor.pullbackAlong φ hφ D)
      = (finrankAlong K φ : ℤ) • D) (x : Pic0 K F) :
    Pic0.pushforwardAlongHom φ hφ hfin hN (Pic0.pullbackAlongHom φ hφ hFI x) = finrankAlong K φ • x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, Pic0.pushforwardAlongHom_mk, ← mk_nsmul]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pullbackAlongDegZeroHom, hdiv, AddSubmonoidClass.coe_nsmul,
    natCast_zsmul]

theorem ofAlgAut_smul_pullbackAlongHom (τ : F' ≃ₐ[K] F') (hτ : ∀ x : F, τ (φ x) = φ x)
    (x : Pic0 K F) :
    SemilinearAut.ofAlgAut τ • Pic0.pullbackAlongHom φ hφ hFI x = Pic0.pullbackAlongHom φ hφ hFI x := by
  have hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom (1 : SemilinearAut K F) (SemilinearAut.ofAlgAut τ) :=
    fun y => by rw [one_smul, SemilinearAut.ofAlgAut_smul]; exact hτ y
  have := SemilinearAut.pullbackAlong_smul φ hφ hgg'
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pullbackAlongDegZeroHom, ← this D, one_smul]

theorem sum_ofAlgAut_smul_eq_pullbackAlongHom_pushforwardAlongHom {ι' : Type*} (s : Finset ι')
    (τ : ι' → (F' ≃ₐ[K] F'))
    (hdiv : ∀ D : Divisor K F', ∑ i ∈ s, SemilinearAut.ofAlgAut (τ i) • D
      = Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong φ hφ D)) (y : Pic0 K F') :
    ∑ i ∈ s, SemilinearAut.ofAlgAut (τ i) • y
      = Pic0.pullbackAlongHom φ hφ hFI (Pic0.pushforwardAlongHom φ hφ hfin hN y) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pullbackAlongHom_mk]
  simp_rw [SemilinearAut.pic0_smul_mk]
  rw [← mk_sum]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [AddSubmonoidClass.coe_finsetSum, Pic0.coe_pullbackAlongDegZeroHom, Pic0.coe_pushforwardAlongDegZero,
    ← hdiv D]
  exact Finset.sum_congr rfl fun i _ => SemilinearAut.coe_degZeroSMulHom _ _

end Descent

end K1Transfer
p2m_reactivate "P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.K1Transfer"

open AlgebraicCurve.SemilinearAut

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk Place Divisor Divisor.degZero HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.mk_add Pic0.mk_zero algebraAlong isScalarTower_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong finrankAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence_apply Place.mem_fiberAlong SeparableAlong SemilinearAut.IntertwinesAlong Divisor.pushforward Divisor.pullback Pic0.coe_pullbackAlongDegZeroHom Pic0.pullbackAlongHom Pic0.pullbackAlongHom_mk Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Divisor.sum_galois_smul_eq_pullback_pushforward SemilinearAut.pullbackAlong_smul fundamentalIdentityAlong normFormulaAlong Pic0.pushforwardAlongHom_smul Divisor.correspondence_single_eq_finrankAlong_smul" namespace Pic0 p2m_export "AlgebraicCurve.Pic0" "mk mk_surjective mk_add mk_zero coe_degZeroSMulHom coe_pullbackAlongDegZeroHom pullbackAlongHom pullbackAlongHom_mk coe_pushforwardAlongDegZero pushforwardAlongHom pushforwardAlongHom_mk pushforwardAlongHom_smul" end AlgebraicCurve.Pic0
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Pic0" in
theorem AlgebraicCurve.Pic0.pullbackAlongHom_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F] [AlgebraicCurve.HasPrincipalDivisors K F']
    {g : AlgebraicCurve.SemilinearAut K F} {g' : AlgebraicCurve.SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ)
    (hgg' : AlgebraicCurve.SemilinearAut.IntertwinesAlong φ.toRingHom g g') (x : AlgebraicCurve.Pic0 K F) :
    AlgebraicCurve.Pic0.pullbackAlongHom φ hφ hFI (g • x) = g' • AlgebraicCurve.Pic0.pullbackAlongHom φ hφ hFI x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [pic0_smul_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pullbackAlongDegZeroHom, SemilinearAut.coe_degZeroSMulHom, SemilinearAut.coe_degZeroSMulHom,
    Pic0.coe_pullbackAlongDegZeroHom]
  exact SemilinearAut.pullbackAlong_smul φ hφ hgg' (D : Divisor K F)

namespace ModularCurve p2m_export "ModularCurve" "xHFunctionField xHFunctionFieldC_le_x1 xHFunctionFieldBar JH x1FunctionField x1FunctionFieldBar JOne arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def coeffMap coeffEmb laurentBaseChange HeckeDiamondInputsAll IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut IsDiamondAut diamondAut diamondAutBar diamondOneBar diamondOneBar_apply geomAut coe_geomAut_coeffEmb inclusionBar coe_inclusionBar exists_monoidHom_diamondAut_mem_xHFunctionField_iff laurentBaseChange_deck_galois_package hasPrincipalDivisors_xHFunctionFieldBar inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC" end ModularCurve
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.intertwines_arith (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (ι : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁))
    (hι : ∀ x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀),
      ((ι x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    SemilinearAut.IntertwinesAlong ι.toRingHom (arithmeticGalois F₀ τ) (arithmeticGalois F₁ τ) := by
  intro x
  apply Subtype.ext
  have h1 : ((arithmeticGalois F₁ τ • ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) ((ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    coe_arithmeticGalois_smul F₁ τ _
  have h2 : ((ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) := hι x
  have h3 : ((ι.toRingHom (arithmeticGalois F₀ τ • x) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((arithmeticGalois F₀ τ • x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) := hι _
  rw [h1, h2, h3, coe_arithmeticGalois_smul]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.pullbackAlongHom_galois_smul (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)]
    (ι : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁))
    (hι : ∀ x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀),
      ((ι x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral) (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • x) = σ • AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def]
  exact AlgebraicCurve.Pic0.pullbackAlongHom_smul ι hint hFI (ModularCurve.intertwines_arith F₀ F₁ ι hι σ) x

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.pushforwardAlongHom_galois_smul (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (ι : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁))
    (hι : ∀ x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀),
      ((ι x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
    (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (y : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) :
    AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN (σ • y) = σ • AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def]
  exact AlgebraicCurve.Pic0.pushforwardAlongHom_smul ι hint hfin hN (ModularCurve.intertwines_arith F₀ F₁ ι hι σ) y

p2m_open_scoped "ModularCurve" in
theorem ModularCurve.T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

p2m_open_scoped "ModularCurve" in
theorem ModularCurve.pushforwardAlong_pullbackAlong_eq_finrankAlong_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)]
    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hint : ι.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι) (hsep : AlgebraicCurve.SeparableAlong (AlgebraicClosure ℚ) ι)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Divisor.pushforwardAlong ι hint (Divisor.pullbackAlong ι hint D) = (finrankAlong (AlgebraicClosure ℚ) ι : ℤ) • D := by

  have hf : ∀ w : Place (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M), w.inertiaDegAlong ι hint = 1 := fun w =>
    ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (L := AlgebraicClosure ℚ)
      (CongruenceSubgroup.Gamma1 M) (ModularCurve.T_mem_Gamma1 M) (x1FunctionField M) rfl ι hint w

  have hsingle : ∀ (v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (n : ℤ),
      Divisor.pushforwardAlong ι hint (Divisor.pullbackAlong ι hint (Finsupp.single v n)) =
        (finrankAlong (AlgebraicClosure ℚ) ι : ℤ) • Finsupp.single v n := fun v n => by
    have h := AlgebraicCurve.Divisor.correspondence_single_eq_finrankAlong_smul ι ι hint hint hfin hsep v
      (fun w hw => Place.mem_fiberAlong.mp hw) (fun w _ => hf w) (fun w _ => hf w) n
    rwa [Divisor.correspondence_apply] at h

  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]
  | single v n => exact hsingle v n

namespace K1Transfer

local notation "ℚbar" => AlgebraicClosure ℚ

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem xH_le_x1 : xHFunctionField M H ≤ x1FunctionField M := xHFunctionFieldC_le_x1 ℚ M H

abbrev ιbar : ↥(xHFunctionFieldBar M H) →ₐ[ℚbar] ↥(x1FunctionFieldBar M) :=
  inclusionBar ℚbar (xH_le_x1 M H)

theorem coe_ιbar (x : ↥(xHFunctionFieldBar M H)) :
    ((ιbar M H x : ↥(x1FunctionFieldBar M)) : LaurentSeries ℚbar) = (x : LaurentSeries ℚbar) :=
  coe_inclusionBar ℚbar (xH_le_x1 M H) x

set_option maxHeartbeats 3200000 in

theorem main (hin : HeckeDiamondInputsAll M)
    [HasPrincipalDivisors ℚbar ↥(x1FunctionFieldBar M)]
    (S : Finset ℕ) (hS : ∀ d ∈ S, Nat.Coprime d M)
    (hSH : ∀ (d : ℕ) (hd : d ∈ S), ZMod.unitOfCoprime d (hS d hd) ∈ H)
    (hHS : ∀ h ∈ H, ∃! d : ℕ, d ∈ S ∧ (d : ZMod M) = ((h : (ZMod M)ˣ) : ZMod M)) :
    ∃ (pull : JH M H →+ JOne M) (push : JOne M →+ JH M H) (c m : ℕ),
      0 < c ∧ 0 < m ∧ c * m = S.card ∧
      (∀ (hint : (ιbar M H).toRingHom.IsIntegral)
          (hFI : FundamentalIdentityAlong ℚbar (ιbar M H) hint) (x : JH M H),
        pull x = Pic0.pullbackAlongHom (ιbar M H) hint hFI x) ∧
      (∀ (hint : (ιbar M H).toRingHom.IsIntegral) (hfin : FiniteAlong ℚbar (ιbar M H))
          (hN : NormFormulaAlong ℚbar (ιbar M H) hfin) (y : JOne M),
        push y = Pic0.pushforwardAlongHom (ιbar M H) hint hfin hN y) ∧
      (∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (x : JH M H), pull (σ • x) = σ • pull x) ∧
      (∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (y : JOne M), push (σ • y) = σ • push y) ∧
      (∀ x : JH M H, push (pull x) = c • x) ∧
      (∀ d ∈ S, ∀ x : JH M H, diamondOneBar M d (pull x) = pull x) ∧
      (∀ y : JOne M, ∑ d ∈ S, diamondOneBar M d y = m • pull (push y)) := by
  classical
  haveI : HasPrincipalDivisors ℚbar ↥(xHFunctionFieldBar M H) := hasPrincipalDivisors_xHFunctionFieldBar M H
  haveI : Fintype H := Fintype.ofFinite _

  have hdia : ∀ d : ℕ, Nat.Coprime d M →
      ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ := fun d hd => (hin.2 d hd).1
  obtain ⟨δ, hδ, hgalois⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff M H hdia
  have hfix : ∀ (u : H) (x : x1FunctionField M),
      (x : LaurentSeries ℚ) ∈ xHFunctionField M H → δ u x = x := fun u x hx => (hgalois x).mp hx u
  have hgal : ∀ x : x1FunctionField M, (∀ u : H, δ u x = x) →
      (x : LaurentSeries ℚ) ∈ xHFunctionField M H := fun x hx => (hgalois x).mpr hx

  obtain ⟨hrange, hfin, hdeg⟩ := laurentBaseChange_deck_galois_package ℚbar (xH_le_x1 M H) δ hfix hgal
  have hbar : ∀ u : H, diamondAutBar M (rep S hHS u) = ((geomAut ℚbar (x1FunctionField M)).comp δ) u := by
    intro u
    rw [diamondAutBar_congr M ((natCast_rep S hHS u).trans (ZMod.natCast_zmod_val _).symm),
      diamondAutBar_eq_geomAut, ← hδ u, MonoidHom.comp_apply]
  generalize (geomAut ℚbar (x1FunctionField M)).comp δ = δbar at hrange hdeg hbar
  haveI : Fintype δbar.range := Fintype.ofFinite _

  have hint : (ιbar M H).toRingHom.IsIntegral := by
    letI := algebraAlong (ιbar M H)
    haveI : Module.Finite ↥(xHFunctionFieldBar M H) ↥(x1FunctionFieldBar M) := hfin
    intro x
    exact Algebra.IsIntegral.isIntegral x
  have hsep : SeparableAlong ℚbar (ιbar M H) := by
    letI := algebraAlong (ιbar M H)
    haveI : Module.Finite ↥(xHFunctionFieldBar M H) ↥(x1FunctionFieldBar M) := hfin
    show Algebra.IsSeparable _ _
    infer_instance
  have hFI : FundamentalIdentityAlong ℚbar (ιbar M H) hint :=
    AlgebraicCurve.fundamentalIdentityAlong (ιbar M H) hint hfin hsep
  have hN : NormFormulaAlong ℚbar (ιbar M H) hfin := AlgebraicCurve.normFormulaAlong (ιbar M H) hfin hsep

  refine ⟨Pic0.pullbackAlongHom (ιbar M H) hint hFI, Pic0.pushforwardAlongHom (ιbar M H) hint hfin hN,
    finrankAlong ℚbar (ιbar M H), Nat.card δbar.ker, ?_, ?_, ?_, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeg]; exact Nat.card_pos
  · exact Nat.card_pos
  · rw [card_S_eq S hS hSH hHS, hdeg, mul_comm, ← Nat.card_eq_fintype_card]
    exact card_ker_mul_card_range δbar
  · intro σ x
    exact ModularCurve.pullbackAlongHom_galois_smul (xHFunctionField M H) (x1FunctionField M) (ιbar M H)
      (coe_ιbar M H) hint hFI σ x
  · intro σ y
    exact ModularCurve.pushforwardAlongHom_galois_smul (xHFunctionField M H) (x1FunctionField M) (ιbar M H)
      (coe_ιbar M H) hint hfin hN σ y
  · intro x
    exact pushforwardAlongHom_pullbackAlongHom (ιbar M H) hint hFI hfin hN
      (ModularCurve.pushforwardAlong_pullbackAlong_eq_finrankAlong_smul M H (ιbar M H) hint hfin hsep) x
  · intro d hd x
    rw [diamondOneBar_apply]
    have hu : diamondAutBar M d = δbar ⟨ZMod.unitOfCoprime d (hS d hd), hSH d hd⟩ := by
      rw [← hbar, rep_unitOfCoprime S hS hSH hHS hd]
    rw [hu]
    exact ofAlgAut_smul_pullbackAlongHom (ιbar M H) hint hFI _
      (fun y => algEquiv_comp_eq_of_mem (ιbar M H) δbar.range hrange ⟨_, rfl⟩ y) x
  · intro y
    calc ∑ d ∈ S, diamondOneBar M d y
        = ∑ d ∈ S, SemilinearAut.ofAlgAut (diamondAutBar M d) • y :=
          Finset.sum_congr rfl fun d _ => diamondOneBar_apply M d y
      _ = ∑ u : H, SemilinearAut.ofAlgAut (diamondAutBar M (rep S hHS u)) • y :=
          sum_S_eq S hS hSH hHS fun d => SemilinearAut.ofAlgAut (diamondAutBar M d) • y
      _ = ∑ u : H, SemilinearAut.ofAlgAut (δbar u) • y :=
          Finset.sum_congr rfl fun u _ => by rw [hbar u]
      _ = Nat.card δbar.ker • ∑ h : δbar.range,
            SemilinearAut.ofAlgAut (h : ↥(x1FunctionFieldBar M) ≃ₐ[ℚbar] ↥(x1FunctionFieldBar M)) • y :=
          sum_comp_eq_card_ker_smul_sum_range δbar fun g => SemilinearAut.ofAlgAut g • y
      _ = Nat.card δbar.ker • Pic0.pullbackAlongHom (ιbar M H) hint hFI
            (Pic0.pushforwardAlongHom (ιbar M H) hint hfin hN y) := by
          congr 1
          exact sum_ofAlgAut_smul_eq_pullbackAlongHom_pushforwardAlongHom (ιbar M H) hint hFI hfin hN
            Finset.univ
            (fun h : δbar.range => (h : ↥(x1FunctionFieldBar M) ≃ₐ[ℚbar] ↥(x1FunctionFieldBar M)))
            (fun D => sum_subgroup_smul_eq_pullbackAlong_pushforwardAlong (ιbar M H) δbar.range hrange
              hfin hint D) y

end Main
p2m_reactivate "P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.K1Transfer"

end K1Transfer
p2m_reactivate "P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.K1Transfer"

end
p2m_reactivate "P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.K1Transfer"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.AlgebraicCurve in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))

    (S : Finset ℕ) (hS : ∀ d ∈ S, Nat.Coprime d M)
    (hSH : ∀ (d : ℕ) (hd : d ∈ S), ZMod.unitOfCoprime d (hS d hd) ∈ H)
    (hHS : ∀ h ∈ H, ∃! d : ℕ, d ∈ S ∧ (d : ZMod M) = ((h : (ZMod M)ˣ) : ZMod M)) :
    ∃ (pull : ModularCurve.JH M H →+ ModularCurve.JOne M)
      (push : ModularCurve.JOne M →+ ModularCurve.JH M H) (c m : ℕ),
      0 < c ∧ 0 < m ∧ c * m = S.card ∧

      (∀ (hint : ι.toRingHom.IsIntegral)
          (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
          (x : ModularCurve.JH M H),
        pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x) ∧
      (∀ (hint : ι.toRingHom.IsIntegral)
          (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
          (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
          (y : ModularCurve.JOne M),
        push y = AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JH M H),
        pull (σ • x) = σ • pull x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ModularCurve.JOne M),
        push (σ • y) = σ • push y) ∧

      (∀ x : ModularCurve.JH M H, push (pull x) = c • x) ∧

      (∀ d ∈ S, ∀ x : ModularCurve.JH M H,
        ModularCurve.diamondOneBar M d (pull x) = pull x) ∧

      (∀ y : ModularCurve.JOne M,
        ∑ d ∈ S, ModularCurve.diamondOneBar M d y = m • pull (push y)) := by

  obtain rfl : ι = K1Transfer.ιbar M H := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rw [hι x, K1Transfer.coe_ιbar]
  exact K1Transfer.main M H hin S hS hSH hHS

end S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
end P2MW
export P2MW.S_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq (solution)

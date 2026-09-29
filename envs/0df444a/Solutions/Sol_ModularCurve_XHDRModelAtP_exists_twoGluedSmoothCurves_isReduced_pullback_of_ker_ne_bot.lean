-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/245f6a19-c59f-52f2-ac8a-2fbabc81d5d4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen
import Theorems.Thm_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup

open scoped MatrixGroups

namespace TwoGluedH

universe u

theorem coe_preimage_opens {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) :
    ((f ⁻¹ᵁ W : X.Opens) : Set ↥X) = f.base ⁻¹' (W : Set ↥Y) := rfl

scoped instance subsingleton_spec_field (K : Type u) [Field K] : Subsingleton ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

scoped instance nonempty_spec_field (K : Type u) [Field K] : Nonempty ↥(Spec (CommRingCat.of K)) :=
  ⟨IsLocalRing.closedPoint K⟩

def coverOfIso {X Y : Scheme.{u}} (e : X ≅ Y) (𝒱 : Y.TwoAffineOpenCover) : X.TwoAffineOpenCover where
  U0 := e.hom ⁻¹ᵁ 𝒱.U0
  U1 := e.hom ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage_of_isIso e.hom
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage_of_isIso e.hom
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage_of_isIso e.hom

theorem charP_of_ker_ne_bot (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] (f : R p →+* k)
    (hf : RingHom.ker f ≠ ⊥) : CharP k p := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hf
  rw [RingHom.mem_ker] at hx

  have hxq : (x : ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hden : ((x : ℚ).den : ℚ) ∈ GaloisRep.ratLocalizedAt p := by
    show ((x : ℚ).den : ℚ).den.Coprime p
    simp
  have hnum : ((x : ℚ).num : ℚ) ∈ GaloisRep.ratLocalizedAt p := by
    show ((x : ℚ).num : ℚ).den.Coprime p
    simp
  have hmul : x * ⟨_, hden⟩ = ⟨_, hnum⟩ := Subtype.ext (Rat.mul_den_eq_num (x : ℚ))
  have hcast : (⟨_, hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) := Subtype.ext (by push_cast; rfl)
  have hfnum : ((x : ℚ).num : k) = 0 := by
    have := congrArg f hmul
    rw [map_mul, hx, zero_mul, hcast, map_intCast] at this
    exact this.symm
  have hnum0 : (x : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr hxq

  obtain ⟨ℓ, hℓ⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k ℓ with hprime | hzero
  · by_cases hℓp : ℓ = p
    · exact hℓp ▸ hℓ
    · exfalso
      have hcop : (ℓ : ℚ) ∈ GaloisRep.ratLocalizedAt p := by show (ℓ : ℚ).den.Coprime p; simp
      have hinv : ((ℓ : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt p := by
        show ((ℓ : ℚ)⁻¹).den.Coprime p
        rw [Rat.inv_natCast_den, if_neg hprime.ne_zero]
        exact (Nat.coprime_primes hprime hp.out).mpr hℓp
      have h1 : (⟨_, hcop⟩ : R p) * ⟨_, hinv⟩ = 1 :=
        Subtype.ext (by show (ℓ : ℚ) * (ℓ : ℚ)⁻¹ = 1; exact mul_inv_cancel₀ (by exact_mod_cast hprime.ne_zero))
      have := congrArg f h1
      rw [map_mul, map_one, show f ⟨(ℓ : ℚ), hcop⟩ = (ℓ : k) from map_natCast f ℓ, CharP.cast_eq_zero,
        zero_mul] at this
      exact zero_ne_one this
  · exfalso
    subst hzero
    haveI := CharP.charP_to_charZero k
    exact hnum0 (by exact_mod_cast hfnum)

end TwoGluedH
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot.TwoGluedH"

open TwoGluedH in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (k : Type) [Field k] [IsAlgClosed k] (f : R p →+* k) (hf : RingHom.ker f ≠ ⊥) :
    ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
      (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
      (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
      (i₁ : SchemeHomOver c₁ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))))
      (i₂ : SchemeHomOver c₂ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))))
      (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
      (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
      IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))) ∧
      (∀ z : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
      IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n := by
  haveI : CharP k p := charP_of_ker_ne_bot p f hf
  obtain ⟨A, hA, hcp, hac, ρ, hρ, φ, hφ⟩ :=
    ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq p k f
  subst hφ

  set toκ : R p →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp ρ with htoκ
  set s₀ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (R p)) :=
    Spec.map (CommRingCat.ofHom toκ) with hs₀
  set π : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := Spec.map (CommRingCat.ofHom φ) with hπ
  have hs : Spec.map (CommRingCat.ofHom (φ.comp toκ)) = π ≫ s₀ := by
    rw [hπ, hs₀, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hs]
  set cM := toBase p (ΓM M H) hj with hcM
  set cN := toBase p (ΓN p M H hpM) hj with hcN

  let e : pullback cM (π ≫ s₀) ⟶ pullback cM s₀ :=
    pullback.lift (pullback.fst cM (π ≫ s₀)) (pullback.snd cM (π ≫ s₀) ≫ π) (by rw [Category.assoc]; exact pullback.condition)
  have he_fst : e ≫ pullback.fst cM s₀ = pullback.fst cM (π ≫ s₀) := pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd cM s₀ = pullback.snd cM (π ≫ s₀) ≫ π := pullback.lift_snd _ _ _
  have hE : IsPullback e (pullback.snd cM (π ≫ s₀)) (pullback.snd cM s₀) π :=
    IsPullback.of_right (by rw [he_fst]; exact IsPullback.of_hasPullback cM (π ≫ s₀)) he_snd
      (IsPullback.of_hasPullback cM s₀)
  let e' : pullback cN (π ≫ s₀) ⟶ pullback cN s₀ :=
    pullback.lift (pullback.fst cN (π ≫ s₀)) (pullback.snd cN (π ≫ s₀) ≫ π) (by rw [Category.assoc]; exact pullback.condition)
  have he'_fst : e' ≫ pullback.fst cN s₀ = pullback.fst cN (π ≫ s₀) := pullback.lift_fst _ _ _
  have he'_snd : e' ≫ pullback.snd cN s₀ = pullback.snd cN (π ≫ s₀) ≫ π := pullback.lift_snd _ _ _
  have hE' : IsPullback e' (pullback.snd cN (π ≫ s₀)) (pullback.snd cN s₀) π :=
    IsPullback.of_right (by rw [he'_fst]; exact IsPullback.of_hasPullback cN (π ≫ s₀)) he'_snd
      (IsPullback.of_hasPullback cN s₀)
  have hπsurj : Surjective π := ⟨Function.surjective_to_subsingleton _⟩
  have hesurj : Surjective e := MorphismProperty.of_isPullback hE.flip hπsurj

  let j₁ : pullback cN s₀ ⟶ pullback cM s₀ := 𝔛.comp A hA ρ hρ 0
  let j₂ : pullback cN s₀ ⟶ pullback cM s₀ := 𝔛.comp A hA ρ hρ 1
  have hj₁ : j₁ ≫ pullback.snd cM s₀ = pullback.snd cN s₀ := 𝔛.comp_over A hA ρ hρ 0
  have hj₂ : j₂ ≫ pullback.snd cM s₀ = pullback.snd cN s₀ := 𝔛.comp_over A hA ρ hρ 1
  haveI hcj₁ : IsClosedImmersion j₁ := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI hcj₂ : IsClosedImmersion j₂ := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  let i₁' : pullback j₁ e ⟶ pullback cM (π ≫ s₀) := pullback.snd j₁ e
  let i₂' : pullback j₂ e ⟶ pullback cM (π ≫ s₀) := pullback.snd j₂ e
  let c₁' : pullback j₁ e ⟶ Spec (CommRingCat.of k) := i₁' ≫ pullback.snd cM (π ≫ s₀)
  let c₂' : pullback j₂ e ⟶ Spec (CommRingCat.of k) := i₂' ≫ pullback.snd cM (π ≫ s₀)
  have sq₁ : IsPullback (pullback.fst j₁ e) c₁' (pullback.snd cN s₀) π := by
    have := (IsPullback.of_hasPullback j₁ e).paste_vert hE
    rwa [hj₁] at this
  have sq₂ : IsPullback (pullback.fst j₂ e) c₂' (pullback.snd cN s₀) π := by
    have := (IsPullback.of_hasPullback j₂ e).paste_vert hE
    rwa [hj₂] at this

  have hp₀ : IsProper (pullback.snd cN s₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback cN s₀) 𝔛.isProper0
  have hsm₀ : SmoothOfRelativeDimension 1 (pullback.snd cN s₀) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback cN s₀) 𝔛.smooth0
  haveI : IsIntegral (pullback cN s₀) := IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)
  have hgi₀ : GeometricallyIntegral (pullback.snd cN s₀) := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  have hp₁' : IsProper c₁' := MorphismProperty.of_isPullback sq₁ hp₀
  have hp₂' : IsProper c₂' := MorphismProperty.of_isPullback sq₂ hp₀
  have hsm₁' : SmoothOfRelativeDimension 1 c₁' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq₁ hsm₀
  have hsm₂' : SmoothOfRelativeDimension 1 c₂' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq₂ hsm₀
  have hgi₁' : GeometricallyIntegral c₁' := MorphismProperty.of_isPullback sq₁ hgi₀
  have hgi₂' : GeometricallyIntegral c₂' := MorphismProperty.of_isPullback sq₂ hgi₀
  have hci₁' : IsClosedImmersion i₁' := inferInstance
  have hci₂' : IsClosedImmersion i₂' := inferInstance

  have hr₁ : Set.range i₁'.base = e.base ⁻¹' Set.range j₁.base := Scheme.Pullback.range_snd j₁ e
  have hr₂ : Set.range i₂'.base = e.base ⁻¹' Set.range j₂.base := Scheme.Pullback.range_snd j₂ e
  have hjs : ∀ y : ↥(pullback cM s₀), y ∈ Set.range j₁.base ∨ y ∈ Set.range j₂.base :=
    𝔛.comp_jointly_surjective A hA ρ hρ

  let q : pullback i₁' i₂' ⟶ pullback j₁ j₂ :=
    pullback.map i₁' i₂' j₁ j₂ (pullback.fst j₁ e) (pullback.fst j₂ e) e
      pullback.condition.symm pullback.condition.symm
  have hq_fst : q ≫ pullback.fst j₁ j₂ = pullback.fst i₁' i₂' ≫ pullback.fst j₁ e := pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd j₁ j₂ = pullback.snd i₁' i₂' ≫ pullback.fst j₂ e := pullback.lift_snd _ _ _
  have S3 : IsPullback (pullback.snd i₁' i₂' ≫ pullback.fst j₂ e) (pullback.fst i₁' i₂') j₂
      (pullback.fst j₁ e ≫ j₁) := by
    have := (IsPullback.of_hasPullback i₁' i₂').flip.paste_horiz (IsPullback.of_hasPullback j₂ e)
    rwa [show i₁' ≫ e = pullback.fst j₁ e ≫ j₁ from pullback.condition.symm] at this
  have S4 : IsPullback (pullback.fst i₁' i₂') q (pullback.fst j₁ e) (pullback.fst j₁ j₂) :=
    IsPullback.of_bot (by rw [hq_snd]; exact S3.flip) hq_fst.symm (IsPullback.of_hasPullback j₁ j₂)
  let z : pullback j₁ j₂ ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := pullback.fst j₁ j₂ ≫ pullback.snd cN s₀
  have SP : IsPullback q (pullback.fst i₁' i₂' ≫ c₁') z π := S4.flip.paste_vert sq₁
  let m : pullback i₁' i₂' ≅ pullback z π := SP.isoPullback
  haveI : IsReduced (pullback j₁ j₂) := 𝔛.crossing_reduced A hA ρ hρ
  haveI : Finite ↥(pullback j₁ j₂) := by
    haveI : NeZero (M / p) := ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩
    haveI : (ΓN p M H hpM).FiniteIndex := CuspForm.GammaH_finiteIndex (M / p) (infSubgroup p M H hpM)
    haveI := (ModularCurve.finite_ssPlacesQExp (ResidueField ↥A) p (ΓN p M H hpM)
      (ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM))).to_subtype
    exact Finite.of_equiv _ (𝔛.nodeEquiv A hA ρ hρ).symm
  haveI : Smooth (pullback.snd cN s₀) := SmoothOfRelativeDimension.smooth 1 _
  haveI : LocallyOfFiniteType z := inferInstance
  obtain ⟨hred', hcard'⟩ := AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed z φ

  have hn0 : 0 < Nat.card ↥(pullback j₁ j₂) := by
    rw [Nat.card_pos_iff]
    refine ⟨?_, inferInstance⟩
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    letI : Algebra (R p) (ResidueField ↥A) := toκ.toAlgebra
    have hconn : ConnectedSpace ↥(pullback cM s₀) :=
      ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed p M H hpM hj 𝔛 (ResidueField ↥A)
    have hc₁ : IsClosed (Set.range j₁.base) := j₁.isClosedEmbedding.isClosed_range
    have hc₂ : IsClosed (Set.range j₂.base) := j₂.isClosedEmbedding.isClosed_range
    have hdisj : Disjoint (Set.range j₁.base) (Set.range j₂.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
      obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hb.symm
      exact hempty.elim w
    have hcompl : (Set.range j₁.base)ᶜ = Set.range j₂.base := by
      ext y
      constructor
      · intro hy; exact (hjs y).resolve_left hy
      · intro hy h1; exact Set.disjoint_left.mp hdisj h1 hy
    have hclopen : IsClopen (Set.range j₁.base) :=
      ⟨hc₁, by rw [← compl_compl (Set.range j₁.base), hcompl]; exact hc₂.isOpen_compl⟩
    have hne : Nonempty ↥(pullback cN s₀) := ⟨(𝔛.efib A hA ρ hρ).base (Classical.arbitrary _)⟩
    obtain ⟨x₀⟩ := hne
    rcases isClopen_iff.mp hclopen with h | h
    · exact (Set.eq_empty_iff_forall_notMem.mp h) (j₁.base x₀) ⟨x₀, rfl⟩
    · have : j₂.base x₀ ∈ Set.range j₂.base := ⟨x₀, rfl⟩
      rw [← hcompl, h, Set.compl_univ] at this
      exact this

  obtain ⟨𝒱, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_twoAffineOpenCover_U0_eq_chartFinOpen
    (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
  letI : Algebra (R p) k := (φ.comp toκ).toAlgebra
  have hsk : π ≫ s₀ = Scheme.TwoAffineOpenCover.specMap (R p) k := hs.symm
  let 𝒱k : (pullback cN (π ≫ s₀)).TwoAffineOpenCover := coverOfIso (pullback.congrHom rfl hsk) (𝒱.pullback cN k)
  let cov₁ : (pullback j₁ e).TwoAffineOpenCover := coverOfIso (sq₁.isoPullback ≪≫ hE'.isoPullback.symm) 𝒱k
  let cov₂ : (pullback j₂ e).TwoAffineOpenCover := coverOfIso (sq₂.isoPullback ≪≫ hE'.isoPullback.symm) 𝒱k

  have hredF : IsReduced (pullback cM (π ≫ s₀)) :=
    ModularCurve.XHDRModelAtP.isReduced_pullback_toBase_of_isAlgClosed p M H hpM hj 𝔛 k (π ≫ s₀)

  refine ⟨pullback j₁ e, pullback j₂ e, c₁', c₂', hp₁', hsm₁', hgi₁', hp₂', hsm₂', hgi₂', ⟨i₁', rfl⟩, ⟨i₂', rfl⟩,
    hci₁', hci₂', Nat.card ↥(pullback j₁ j₂), cov₁, cov₂, hredF, ?_, ?_, ?_, hn0⟩
  · intro x
    rcases hjs (e.base x) with h | h
    · left; show x ∈ Set.range i₁'.base; rw [hr₁]; exact h
    · right; show x ∈ Set.range i₂'.base; rw [hr₂]; exact h
  · show IsReduced (pullback i₁' i₂')
    exact isReduced_of_isOpenImmersion m.hom
  · show Nat.card ↥(pullback i₁' i₂') = Nat.card ↥(pullback j₁ j₂)
    rw [← hcard']
    exact Nat.card_congr (Scheme.homeoOfIso m).toEquiv

#print axioms solution

end
end S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot (solution)

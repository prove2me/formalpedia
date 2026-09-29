-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ff9a1d4d-31bc-54cc-bc13-af66389284bf

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO
import Theorems.Thm_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Theorems.Thm_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve~DRModelPackageLevel AlgebraicCurve TopologicalSpace IsLocalRing ModularCurve.XHDRLevel"
open scoped MatrixGroups

noncomputable section

namespace ECL_FUnion

section Local
variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

def fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) : fibre (Γ := Γ) (hj := hj) τB ⟶ fibre (Γ := Γ) (hj := hj) τA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

@[reassoc]
theorem fibreMapOfComp_fst {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [fibreMapOfComp, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem fibreMapOfComp_snd {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem bcMap_eq_fibreMapOfComp {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ hto = fibreMapOfComp Γ hj ρO toκ' toκ hto := by
  apply pullback.hom_ext
  · rw [fibreMapOfComp_fst, bcMap_fst]
  · rw [fibreMapOfComp_snd, bcMap_snd]

theorem fibreMapOfComp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (τA : R p →+* A) (τB : R p →+* B) (τC : R p →+* C)
    (φ : A →+* B) (hφ : φ.comp τA = τB) (ψ : B →+* C) (hψ : ψ.comp τB = τC)
    (χ : A →+* C) (hχ : χ.comp τA = τC) (e : ψ.comp φ = χ) :
    fibreMapOfComp Γ hj τB τC ψ hψ ≫ fibreMapOfComp Γ hj τA τB φ hφ =
      fibreMapOfComp Γ hj τA τC χ hχ := by
  subst e
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMapOfComp_fst]
  · simp only [Category.assoc, fibreMapOfComp_snd, fibreMapOfComp_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isPullback_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    IsPullback (fibreMapOfComp Γ hj τA τB φ h)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB)))
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA) = Spec.map (CommRingCat.ofHom τB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  have key : IsPullback (fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst (toBase p Γ hj) _)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB))) (toBase p Γ hj)
      (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA)) := by
    rw [fibreMapOfComp_fst, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key (fibreMapOfComp_snd Γ hj τA τB φ h) (IsPullback.of_hasPullback _ _)

theorem isClosedImmersion_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) (hφ : Function.Surjective φ) :
    IsClosedImmersion (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφ
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem flat_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Flat (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.toAlgebra
    show RingHom.Flat (algebraMap A B)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat A B)
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem surjective_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Surjective (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ) {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ')

include hϖ in

theorem toκ_maximalIdeal [Fact p.Prime] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def ι [Fact p.Prime] : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal hϖ toκ)

include hto in
theorem ι_comp [Fact p.Prime] : (ι hϖ toκ).comp ((IsLocalRing.residue O).comp ρO) = toκ' := by
  subst hto; exact RingHom.ext fun _ => rfl

theorem bcMap_eq_comp [Fact p.Prime] :
    bcMap Γ hj ρO toκ hto =
      fibreMapOfComp Γ hj ((IsLocalRing.residue O).comp ρO) toκ' (ι hϖ toκ) (ι_comp ρO hϖ toκ hto) ≫
        bcMap Γ hj ρO (IsLocalRing.residue O) rfl := by
  subst hto
  rw [bcMap_eq_fibreMapOfComp, bcMap_eq_fibreMapOfComp,
    fibreMapOfComp_comp (χ := toκ) (hχ := rfl) (e := RingHom.ext fun _ => rfl)]

include hϖ in

theorem exists_bcMap_residue_eq (y : ↥(XO Γ hj ρO))
    (hy : y ∉ (XO.toBase Γ hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (bcMap Γ hj ρO (IsLocalRing.residue O) rfl).base y₀ = y := by
  set s := (XO.toBase Γ hj ρO).base y with hs
  have hps : ((p : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  rw [bcMap_eq_fibreMapOfComp]
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_fibreMapOfComp Γ hj ρO ((IsLocalRing.residue O).comp ρO) (IsLocalRing.residue O) rfl) y
    (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

end Local

variable {p : ℕ} [hq : Fact p.Prime]

section MapLemmas
universe v u
variable {C : Type u} [Category.{v} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂)

@[reassoc]
private theorem map_fst' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem map_snd' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

end MapLemmas

section SpecialFibre

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O) (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

private theorem isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [Surjective f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨y, rfl⟩ := f.surjective x
    have hfl : (f.stalkMap y).hom.Flat := Flat.stalkMap f y
    letI := (f.stalkMap y).hom.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfl
    haveI : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (f.base y)) (B := Y.presheaf.stalk y)
    exact isReduced_of_injective (algebraMap _ (Y.presheaf.stalk y)) (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk X

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

include 𝔛 in

private theorem isReduced_fibre_mk (I : Ideal O) [I.IsMaximal] :
    IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((Ideal.Quotient.mk I).comp ρO)) := by
  have hk : IsField (O ⧸ I) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance
  let φ : (O ⧸ I) →+* AlgebraicClosure (FractionRing (O ⧸ I)) :=
    (algebraMap (FractionRing (O ⧸ I)) (AlgebraicClosure (FractionRing (O ⧸ I)))).comp
      (algebraMap (O ⧸ I) (FractionRing (O ⧸ I)))
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) (φ.comp ((Ideal.Quotient.mk I).comp ρO))) :=
    ModularCurve.XHDRModelAtP.isReduced_pullback_toBase_of_isAlgClosed p M H hpM hj 𝔛 _
      (Spec.map (CommRingCat.ofHom (φ.comp ((Ideal.Quotient.mk I).comp ρO))))

  haveI hf1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap (O ⧸ I) (FractionRing (O ⧸ I))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap (O ⧸ I) (FractionRing (O ⧸ I))).Flat
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing (O ⧸ I)) (nonZeroDivisors (O ⧸ I)))
  haveI hf2 : Flat (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (O ⧸ I)) (AlgebraicClosure (FractionRing (O ⧸ I)))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap (FractionRing (O ⧸ I)) (AlgebraicClosure (FractionRing (O ⧸ I)))).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [show CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap (O ⧸ I) (FractionRing (O ⧸ I))) ≫
        CommRingCat.ofHom (algebraMap (FractionRing (O ⧸ I)) (AlgebraicClosure (FractionRing (O ⧸ I)))) from rfl,
      Spec.map_comp]
    infer_instance

  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨fun x => ⟨⟨⊥, Ideal.bot_prime⟩, PrimeSpectrum.ext ?_⟩⟩
    have hbot : ∀ J : Ideal (O ⧸ I), J ≠ ⊤ → J = ⊥ := fun J hJ => by
      by_contra hne
      obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨b, hb⟩ := hk.mul_inv_cancel ha0
      exact hJ (Ideal.eq_top_of_isUnit_mem _ haJ (isUnit_iff_exists_inv.mpr ⟨b, hb⟩))
    have hx : x.asIdeal = ⊥ := hbot _ x.isPrime.ne_top
    rw [hx]
    change Ideal.comap φ ⊥ = ⊥
    exact hbot _ (Ideal.comap_ne_top φ (Ideal.bot_prime (α := AlgebraicClosure (FractionRing (O ⧸ I)))).ne_top)

  let g : fibre (Γ := ΓM M H) (hj := hj) (φ.comp ((Ideal.Quotient.mk I).comp ρO)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((Ideal.Quotient.mk I).comp ρO) :=
    fibreMapOfComp (ΓM M H) hj ((Ideal.Quotient.mk I).comp ρO) (φ.comp ((Ideal.Quotient.mk I).comp ρO)) φ rfl
  have hg := isPullback_fibreMapOfComp (ΓM M H) hj ((Ideal.Quotient.mk I).comp ρO) (φ.comp ((Ideal.Quotient.mk I).comp ρO)) φ rfl
  haveI : Flat g := MorphismProperty.of_isPullback hg.flip inferInstance
  haveI : Surjective g := MorphismProperty.of_isPullback hg.flip inferInstance
  exact isReduced_of_flat_of_surjective g

include 𝔛 in

private theorem isReduced_pullback_toBase_specMap_mk (I : Ideal O) [I.IsMaximal] :
    IsReduced (pullback (XO.toBase (ΓM M H) hj ρO) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  have h : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI := isReduced_fibre_mk (ρO := ρO) (𝔛 := 𝔛) I
  exact isReduced_of_isOpenImmersion ((pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom ρO)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).hom ≫
      (pullback.congrHom rfl h).hom)

private theorem ker_Spec_map_mk :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))).ker =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))}) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ofIdealTop_ideal]
  have htop : (homOfLE le_top : ((⊤ : (Spec (CommRingCat.of O)).Opens) ⟶ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  simp only [htop, op_id, CategoryTheory.Functor.map_id]
  rw [show CommRingCat.Hom.hom (𝟙 ((Spec (CommRingCat.of O)).presheaf.obj (Opposite.op ⊤))) =
      RingHom.id _ from rfl, Ideal.map_id]

  have hnat := AlgebraicGeometry.Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))

  have happ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))).app ⊤ =
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [happ]
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv.hom := by
    intro a b h
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).hom.hom h
    simpa only [CategoryTheory.Iso.inv_hom_id_apply] using this
  ext a
  rw [RingHom.mem_ker]
  change (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv.hom
      (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) ((Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom a)) = 0 ↔ _
  rw [map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

  let e : Γ(Spec (CommRingCat.of O), ⊤) ≃+* O := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  change e a ∈ Ideal.span {((p : ℕ) : O)} ↔ a ∈ Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))}
  rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_natCast, RingEquiv.apply_symm_apply, hc]
  · rintro ⟨c, rfl⟩
    exact ⟨e c, by rw [map_mul, map_natCast]⟩

end SpecialFibre

section Radical

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj) {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O) (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

include 𝔛 hϖ in

private theorem comap_radical_eq :
    ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (XO.toBase (ΓM M H) hj ρO)).radical =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (XO.toBase (ΓM M H) hj ρO) := by
  let πO := XO.toBase (ΓM M H) hj ρO
  let I : (Spec (CommRingCat.of O)).IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})
  show (I.comap πO).radical = I.comap πO
  let fZ := pullback.fst πO I.subschemeι
  have hJ : I.comap πO = fZ.ker := rfl

  haveI : IsReduced (pullback πO I.subschemeι) := by
    haveI hmax : (Ideal.span {((p : ℕ) : O)}).IsMaximal := by rw [← hϖ]; exact maximalIdeal.isMaximal O
    let i₂ : Spec (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)})) ⟶ Spec (CommRingCat.of O) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))
    haveI : IsClosedImmersion i₂ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    haveI hP₂ : IsReduced (pullback πO i₂) :=
      isReduced_pullback_toBase_specMap_mk (ρO := ρO) (𝔛 := 𝔛) (Ideal.span {((p : ℕ) : O)})
    have hker : I.subschemeι.ker = i₂.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (ker_Spec_map_mk (p := p) (O := O)).symm
    let e := IsClosedImmersion.lift I.subschemeι i₂ hker.le
    haveI : IsIso e := IsClosedImmersion.isIso_lift I.subschemeι i₂ hker
    have he : e ≫ I.subschemeι = i₂ := IsClosedImmersion.lift_fac _ _ _
    exact isReduced_of_isOpenImmersion (inv (pullback.map πO i₂ πO I.subschemeι (𝟙 _) e (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, he])))

  apply le_antisymm _ (Scheme.IdealSheafData.le_radical _)
  rw [hJ, ← Scheme.IdealSheafData.map_bot, ← (Scheme.IdealSheafData.map_gc fZ).le_iff_le, le_bot_iff,
    ← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_radical]
  ext z
  simp only [Closeds.coe_top, Set.mem_univ, iff_true]
  rw [Scheme.IdealSheafData.map_bot]
  show fZ.base z ∈ (fZ.ker.support : Set _)
  rw [Scheme.Hom.support_ker]
  exact subset_closure ⟨z, rfl⟩

private theorem comap_eq_ofIdealTop :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (XO.toBase (ΓM M H) hj ρO) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {((p : ℕ) : Γ(XO (ΓM M H) hj ρO, ⊤))}) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton, map_natCast]

include 𝔛 hϖ in

private theorem radical_span_natCast_sections (U : (XO (ΓM M H) hj ρO).affineOpens) :
    (Ideal.span {((p : ℕ) : Γ(XO (ΓM M H) hj ρO, U))}).radical =
      Ideal.span {((p : ℕ) : Γ(XO (ΓM M H) hj ρO, U))} := by
  have h := congrArg (fun J : (XO (ΓM M H) hj ρO).IdealSheafData => J.ideal U)
    (comap_radical_eq 𝔛 ρO hϖ)
  simp only [Scheme.IdealSheafData.radical_ideal] at h
  rw [comap_eq_ofIdealTop, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast] at h
  exact h

end Radical

section Stalk

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj) {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O) (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

include 𝔛 hϖ in

private theorem radical_span_natCast_stalk (x : ↥(XO (ΓM M H) hj ρO)) :
    (Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)}).radical =
      Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)} := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (XO (ΓM M H) hj ρO).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  letI := (XO (ΓM M H) hj ρO).presheaf.algebra_section_stalk ⟨x, hxU⟩
  haveI hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have hrad := radical_span_natCast_sections 𝔛 ρO hϖ ⟨U, hU⟩
  have hmap : (Ideal.span {((p : ℕ) : Γ(XO (ΓM M H) hj ρO, U))}).map
      (algebraMap _ ((XO (ΓM M H) hj ρO).presheaf.stalk x)) =
      Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h := congrArg (Ideal.map (algebraMap _ ((XO (ΓM M H) hj ρO).presheaf.stalk x))) hrad
  simp only at h
  rw [IsLocalization.map_radical (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    ((XO (ΓM M H) hj ρO).presheaf.stalk x), hmap] at h
  exact h

end Stalk

end ECL_FUnion

end

open ECL_FUnion in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    Scheme.branchIdeal hinf ⊓ Scheme.branchIdeal hzero = Ideal.span {baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O)} := by
  set X := XO (ΓM M H) hj ρO with hX
  set x := 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n with hx
  haveI : IsIntegral X := ModularCurve.XHDRModelAtP.isIntegral_xO p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O hϖ ρO
  haveI := 𝔛.lfp
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (XO.toBase (ΓM M H) hj ρO)
  have hgen : baseGerm ρO x ((p : ℕ) : O) = ((p : ℕ) : X.presheaf.stalk x) := by
    simp only [baseGerm, map_natCast]
  rw [hgen]
  obtain ⟨-, hpP, -, hpQ, hmin, -⟩ :=
    ModularCurve.XHDRModelAtP.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ x hinf hzero
  apply le_antisymm
  · intro a ha
    rw [← ECL_FUnion.radical_span_natCast_stalk 𝔛 ρO hϖ x, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro 𝔮 h𝔮
    rcases hmin 𝔮 h𝔮 with rfl | rfl
    · exact ha.1
    · exact ha.2
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨hpP, hpQ⟩

end S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm (solution)

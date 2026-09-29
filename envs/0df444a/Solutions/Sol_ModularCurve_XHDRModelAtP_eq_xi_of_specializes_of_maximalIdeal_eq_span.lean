-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.eq_xi_of_specializes_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/11e28aa4-ef0f-5886-8b02-6aa49b4e25a1

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XHDRModelAtP_finite_crossings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_eq_xi_of_specializes_of_maximalIdeal_eq_span
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

namespace ECL_FibN
open ModularCurve ModularCurve.XHDRLevel

theorem isIntegral_fibreN {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)

theorem efib_genericPoint_eq {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) =
      genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  refine IsGenericPoint.eq (S := ⊤) ?_ (genericPoint_spec _)
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact 𝔛.efib_genericPoint_specializes A hA ρ hρ y

end ECL_FibN

namespace ECL_EqGen

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

private theorem not_surjective_of_crossing
    (f : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) → ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    ¬ Function.Surjective f := by
  intro hf
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ 𝔛.smooth0
  haveI : Infinite ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    exact Set.infinite_univ_iff.mp (h.mono (Set.subset_univ _))
  haveI : Infinite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Infinite.of_surjective f hf
  haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := 𝔛.finite_crossings A hA ρ hρ
  exact not_finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))

private theorem comp0_genericPoint_notMem_range_comp1 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 1).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_fst_of_mem_range _ _ h)

private theorem comp1_genericPoint_notMem_range_comp0 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 0).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_snd_of_mem_range _ _ h)

theorem eq_of_specializes_comp0_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp0_genericPoint_notMem_range_comp1 𝔛 A hA ρ hρ)

theorem eq_of_specializes_comp1_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp1_genericPoint_notMem_range_comp0 𝔛 A hA ρ hρ)
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

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

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  {ϖ : O} (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
  {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ) (hϖκ : toκ ϖ = 0) {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ')

include hϖ hϖκ in

theorem toκ_maximalIdeal [Fact p.Prime] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, hϖκ, zero_mul]

def ι [Fact p.Prime] : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal hϖ toκ hϖκ)

include hto in
theorem ι_comp [Fact p.Prime] : (ι hϖ toκ hϖκ).comp ((IsLocalRing.residue O).comp ρO) = toκ' := by
  subst hto; exact RingHom.ext fun _ => rfl

theorem bcMap_eq_comp [Fact p.Prime] :
    bcMap Γ hj ρO toκ hto =
      fibreMapOfComp Γ hj ((IsLocalRing.residue O).comp ρO) toκ' (ι hϖ toκ hϖκ) (ι_comp ρO hϖ toκ hϖκ hto) ≫
        bcMap Γ hj ρO (IsLocalRing.residue O) rfl := by
  subst hto
  rw [bcMap_eq_fibreMapOfComp, bcMap_eq_fibreMapOfComp,
    fibreMapOfComp_comp (χ := toκ) (hχ := rfl) (e := RingHom.ext fun _ => rfl)]

include hϖ in

theorem exists_bcMap_residue_eq (y : ↥(XO Γ hj ρO))
    (hy : y ∉ (XO.toBase Γ hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (bcMap Γ hj ρO (IsLocalRing.residue O) rfl).base y₀ = y := by
  set s := (XO.toBase Γ hj ρO).base y with hs
  have hps : ϖ ∈ s.asIdeal := by
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

section Main
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
  {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  {ϖ : O} (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
  (toκ : O →+* IsLocalRing.ResidueField ↥A) (hϖκ : toκ ϖ = 0) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

include hϖ hϖκ in

theorem eq_of_specializes_aux [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (i : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hi : ∀ z, z ⤳ i.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) → z = i.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))))
    (y : ↥(XO (ΓM M H) hj ρO))
    (hy : y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    y = (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  set η := genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  set g := fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ)
    (ι hϖ toκ hϖκ) (ι_comp ρO hϖ toκ hϖκ htoκ) with hg
  set j := bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl with hjj
  haveI : IsClosedImmersion j := by
    rw [hjj, bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ _ _ rfl Ideal.Quotient.mk_surjective
  haveI : Flat g := flat_fibreMapOfComp _ _ _ _ _ _
  have hξ : (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base η = j.base (g.base (i.base η)) := by
    rw [bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ hϖκ htoκ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [hξ] at h ⊢
  obtain ⟨y₀, rfl⟩ := exists_bcMap_residue_eq (ΓM M H) hj ρO hϖ y hy
  have h₀ : y₀ ⤳ g.base (i.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hi z hz]

end Main

end ECL_EqGen

end

open ECL_EqGen in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ) (hϖκ : toκ ϖ = 0) :
    (∀ y : ↥(XO (ΓM M H) hj ρO), y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξinf A hA ρ hρ ρO toκ htoκ → y = 𝔛.ξinf A hA ρ hρ ρO toκ htoκ) ∧
    (∀ y : ↥(XO (ΓM M H) hj ρO), y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξzero A hA ρ hρ ρO toκ htoκ → y = 𝔛.ξzero A hA ρ hρ ρO toκ htoκ) := by
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ

  have hξ : ∀ i : Fin 2, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) =
      (𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    intro i
    rw [Scheme.Hom.comp_apply, ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]
  refine ⟨fun y hy h => ?_, fun y hy h => ?_⟩
  · change y ⤳ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _ at h
    change y = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _
    rw [hξ 0] at h ⊢
    exact ECL_EqGen.eq_of_specializes_aux (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (hϖκ := hϖκ) (htoκ := htoκ) (i := 𝔛.comp A hA ρ hρ 0)
      (hi := ECL_EqGen.eq_of_specializes_comp0_genericPoint 𝔛 A hA ρ hρ) y hy h
  · change y ⤳ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _ at h
    change y = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _
    rw [hξ 1] at h ⊢
    exact ECL_EqGen.eq_of_specializes_aux (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (hϖκ := hϖκ) (htoκ := htoκ) (i := 𝔛.comp A hA ρ hρ 1)
      (hi := ECL_EqGen.eq_of_specializes_comp1_genericPoint 𝔛 A hA ρ hρ) y hy h

end S_ModularCurve_XHDRModelAtP_eq_xi_of_specializes_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_eq_xi_of_specializes_of_maximalIdeal_eq_span (solution)

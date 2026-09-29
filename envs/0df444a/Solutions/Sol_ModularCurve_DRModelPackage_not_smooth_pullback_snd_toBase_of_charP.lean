-- Prove2me | solution 1 for ModularCurve.DRModelPackage.not_smooth_pullback_snd_toBase_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1f832e31-00ac-5076-ba37-9b4e00f3e232

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

open NeronModelInfra AlgebraicCurve IsLocalRing Topology

namespace NSDR

theorem primeSpectrum_pigeonhole {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (q₁ q₂ q₃ : PrimeSpectrum R) : q₁ = q₂ ∨ q₁ = q₃ ∨ q₂ = q₃ := by
  have key : ∀ q : PrimeSpectrum R, q.asIdeal = ⊥ ∨ q.asIdeal = IsLocalRing.maximalIdeal R := by
    intro q
    by_cases h : q.asIdeal = ⊥
    · exact Or.inl h
    · exact Or.inr (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal h))
  rcases key q₁ with h₁ | h₁ <;> rcases key q₂ with h₂ | h₂ <;> rcases key q₃ with h₃ | h₃
  all_goals first
    | exact Or.inl (PrimeSpectrum.ext (h₁.trans h₂.symm))
    | exact Or.inr (Or.inl (PrimeSpectrum.ext (h₁.trans h₃.symm)))
    | exact Or.inr (Or.inr (PrimeSpectrum.ext (h₂.trans h₃.symm)))

theorem isClosed_singleton_or_eq_genericPoint {P : Scheme} [IsIntegral P] [JacobsonSpace P]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (c : P) : IsClosed ({c} : Set P) ∨ c = genericPoint P := by
  by_contra h
  push Not at h
  obtain ⟨hc, hcξ⟩ := h

  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints (X := P) (Z := closure {c})
    ⟨c, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hx
  have hcx : c ⤳ x := specializes_iff_mem_closure.mpr hxZ
  have hξx : genericPoint P ⤳ x := (genericPoint_spec P).specializes (Set.mem_univ x)
  have hxc : x ≠ c := by rintro rfl; exact hc hx
  have hξc : genericPoint P ≠ c := fun e => hcξ e.symm
  have hξx' : genericPoint P ≠ x := by
    rintro e
    apply hcξ

    have h1 : closure ({genericPoint P} : Set P) = Set.univ := genericPoint_closure P
    rw [e, hx.closure_eq] at h1
    have : c ∈ ({x} : Set P) := by rw [h1]; exact Set.mem_univ c
    rw [Set.mem_singleton_iff] at this
    rw [this, e]

  haveI := hdvr x hx
  have hr : ∀ y : P, y ⤳ x → ∃ q : Spec (P.presheaf.stalk x), (P.fromSpecStalk x).base q = y := by
    intro y hy
    have : y ∈ Set.range (P.fromSpecStalk x).base := by rw [Scheme.range_fromSpecStalk]; exact hy
    exact this
  obtain ⟨q₁, hq₁⟩ := hr _ hcx
  obtain ⟨q₂, hq₂⟩ := hr _ hξx
  obtain ⟨q₃, hq₃⟩ := hr _ (le_refl x : x ⤳ x)
  rcases primeSpectrum_pigeonhole q₁ q₂ q₃ with e | e | e
  · exact hξc (hq₂.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e.symm).trans hq₁))
  · exact hxc (hq₃.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e.symm).trans hq₁))
  · exact hξx' (hq₂.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e).trans hq₃))

theorem false_of_range_eq_univ {P X : Scheme} [IsIntegral P] [JacobsonSpace P]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (i j : P ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : Set.range i.base = Set.univ) (hij : Set.range j.base ≠ Set.range i.base) : False := by
  have hie := i.isClosedEmbedding
  have hje := j.isClosedEmbedding
  set ξ := genericPoint P with hξ

  have hrange : ∀ (k : P ⟶ X), IsClosedEmbedding k.base → Set.range k.base = closure {k.base ξ} := by
    intro k hk
    rw [← Set.image_singleton, hk.closure_image_eq, genericPoint_closure, Set.image_univ]

  obtain ⟨c, hc⟩ : j.base ξ ∈ Set.range i.base := by rw [hi]; exact Set.mem_univ _
  have hcξ : c ≠ ξ := by
    intro e
    apply hij
    rw [hrange j hje, hrange i hie, ← hc, e]
  rcases isClosed_singleton_or_eq_genericPoint hdvr c with hcl | hcl
  ·
    have hj : Set.range j.base = {j.base ξ} := by
      rw [hrange j hje, ← hc, ← Set.image_singleton, hie.closure_image_eq, hcl.closure_eq, Set.image_singleton]
    have : j.base c ∈ ({j.base ξ} : Set X) := hj ▸ Set.mem_range_self c
    exact hcξ (hje.injective (Set.mem_singleton_iff.mp this))
  · exact hcξ hcl

theorem false_of_jointly_surjective {P X : Scheme} [IsIntegral P] [JacobsonSpace P] [IrreducibleSpace X]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (i j : P ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hcov : ∀ x : X, x ∈ Set.range i.base ∨ x ∈ Set.range j.base)
    (hne : Set.range i.base ≠ Set.range j.base) : False := by
  have hA : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hB : IsClosed (Set.range j.base) := j.isClosedEmbedding.isClosed_range
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
      _ _ hA hB (fun x _ => hcov x)) with h | h
  · exact false_of_range_eq_univ hdvr i j (Set.eq_univ_of_univ_subset h) hne.symm
  · exact false_of_range_eq_univ hdvr j i (Set.eq_univ_of_univ_subset h) hne

end NSDR

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    ¬ Smooth (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := by
  intro hsm
  haveI := hsm
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
  haveI : ConnectedSpace ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))
  haveI : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))

  haveI : Smooth (𝔛.ratModel K).toBase := SmoothOfRelativeDimension.smooth 1 _
  haveI : JacobsonSpace ↥(𝔛.ratModel K).C := LocallyOfFiniteType.jacobsonSpace (𝔛.ratModel K).toBase
  have hdvr : ∀ x : ↥(𝔛.ratModel K).C, IsClosed ({x} : Set ↥(𝔛.ratModel K).C) →
      IsDiscreteValuationRing ((𝔛.ratModel K).C.presheaf.stalk x) := fun x hx =>
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed (𝔛.ratModel K).toBase x hx
  haveI := 𝔛.compInf_isClosedImmersion K
  haveI := 𝔛.compZero_isClosedImmersion K
  exact NSDR.false_of_jointly_surjective hdvr (𝔛.compInf K) (𝔛.compZero K)
    (𝔛.comp_jointly_surjective K) (𝔛.range_compInf_ne K)

end S_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP (solution)

-- Prove2me | solution 1 for ModularCurve.UniformizedHeckeCurve.exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e23203f4-5c7a-53af-a798-25990feb27f7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteAlong_of_isIntegral
import Theorems.Thm_AlgebraicCurve_Place_subfieldClosure_range_union_eq_top_of_restrictAlong_injOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

namespace P2mWs2B2

theorem isBoundedUnder_congr {α : Type*} {l : Filter α} {u v : α → ℝ} (h : ∀ᶠ x in l, u x = v x) :
    Filter.IsBoundedUnder (· ≤ ·) l u ↔ Filter.IsBoundedUnder (· ≤ ·) l v :=
  ⟨fun hu => hu.mono_le (h.mono fun _ hx => hx.symm.le), fun hv => hv.mono_le (h.mono fun _ hx => hx.le)⟩

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem isIntegral_algHom_of_isCurveOver
    {Fc : Type} [Field Fc] [Algebra ℂ Fc] [IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    {Fc₀ : Type} [Field Fc₀] [Algebra ℂ Fc₀] [IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (e : Fc →ₐ[ℂ] Fc₀) : e.toRingHom.IsIntegral := by
  classical
  have hinj : Function.Injective e := e.toRingHom.injective
  obtain ⟨t, ht, -⟩ := (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := ℂ) (F := Fc)).mp inferInstance
  obtain ⟨x₀, -, hfd₀, -⟩ := (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := ℂ) (F := Fc₀)).mp inferInstance
  have het : Transcendental ℂ (e t) := by
    rintro ⟨p, hp0, hp⟩
    exact ht ⟨p, hp0, hinj (by rw [map_zero, ← Polynomial.aeval_algHom_apply, hp])⟩
  haveI := hfd₀
  haveI hfd : FiniteDimensional (IntermediateField.adjoin ℂ ({e t} : Set Fc₀)) Fc₀ :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x₀ het
  have hL : IntermediateField.adjoin ℂ ({e t} : Set Fc₀) ≤ e.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨t, rfl⟩
  intro y
  obtain ⟨p, hpm, hpy⟩ : IsIntegral (IntermediateField.adjoin ℂ ({e t} : Set Fc₀)) y := IsIntegral.of_finite _ y
  have hlifts : p.map (algebraMap (IntermediateField.adjoin ℂ ({e t} : Set Fc₀)) Fc₀) ∈ Polynomial.lifts e.toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp (hL (p.coeff n).2)
    exact ⟨x, hx⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hpm.map _)
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_map]
  exact hpy

end P2mWs2B2

open P2mWs2B2 in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve Γ Fc₀)
    (hsurj : Function.Surjective U₀.pt)
    (hadd₀ : ∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x + y) z = U₀.realize x z + U₀.realize y z)
    (hmul₀ : ∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x * y) z = U₀.realize x z * U₀.realize y z)
    (hconst₀ : ∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (algebraMap ℂ Fc₀ c) z = c)
    (hinj₀ : ∀ x y : Fc₀, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = U₀.realize y z) → x = y)
    (hcomplete₀ : ∀ f : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
      (∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
      ∃ x : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = f z)

    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (V : Fc → UpperHalfPlane → ℂ)
    (hmero : ∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => V x (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ x : Fc, ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, V x (γ • z) = V x z)
    (hadd : ∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x + y) z = V x z + V y z)
    (hmul : ∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x * y) z = V x z * V y z)
    (hconst : ∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (algebraMap ℂ Fc c) z = c)
    (hsep : ∀ τ τ' : UpperHalfPlane,
      (∀ x : Fc, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖V x z‖) ↔
        Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ') (fun z : UpperHalfPlane => ‖V x z‖)) →
      ∃ γ ∈ Γ, γ • τ = τ')

    (P : Type) (per : P → UpperHalfPlane) (bc : P → AlgebraicCurve.Place ℂ Fc)
    (hbc : ∀ (p : P) (x : Fc), x ∈ (bc p).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] (per p)) (fun z : UpperHalfPlane => ‖V x z‖)) :
    ∃ e : Fc ≃ₐ[ℂ] Fc₀,
      (∀ (x : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (e x) z = V x z) ∧
      (∀ (p : P) (x : Fc), e x ∈ (U₀.pt (per p)).toValuationSubring ↔ x ∈ (bc p).toValuationSubring) := by
  classical

  have hex : ∀ x : Fc, ∃ y : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize y z = V x z :=
    fun x => hcomplete₀ (V x) (hmero x) (hinv x)
  choose e₀ he₀ using hex
  have huniq : ∀ (x : Fc) (y : Fc₀),
      (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize y z = V x z) → y = e₀ x :=
    fun x y hy => hinj₀ y (e₀ x) fun τ => ((hy τ).and (he₀ x τ)).mono fun _ hz => hz.1.trans hz.2.symm

  have hadd' : ∀ x y : Fc, e₀ (x + y) = e₀ x + e₀ y := fun x y => (huniq (x + y) (e₀ x + e₀ y) fun τ => by
    filter_upwards [hadd₀ (e₀ x) (e₀ y) τ, he₀ x τ, he₀ y τ, hadd x y τ] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4]).symm
  have hmul' : ∀ x y : Fc, e₀ (x * y) = e₀ x * e₀ y := fun x y => (huniq (x * y) (e₀ x * e₀ y) fun τ => by
    filter_upwards [hmul₀ (e₀ x) (e₀ y) τ, he₀ x τ, he₀ y τ, hmul x y τ] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4]).symm
  have hcomm' : ∀ c : ℂ, e₀ (algebraMap ℂ Fc c) = algebraMap ℂ Fc₀ c := fun c =>
    (huniq (algebraMap ℂ Fc c) (algebraMap ℂ Fc₀ c) fun τ => by
      filter_upwards [hconst₀ c τ, hconst c τ] with z h1 h2
      rw [h1, h2]).symm
  let eA : Fc →ₐ[ℂ] Fc₀ :=
    { toFun := e₀
      map_one' := by have h := hcomm' 1; rwa [map_one, map_one] at h
      map_mul' := hmul'
      map_zero' := by have h := hcomm' 0; rwa [map_zero, map_zero] at h
      map_add' := hadd'
      commutes' := hcomm' }
  have heA : ∀ x, eA x = e₀ x := fun _ => rfl

  have hinjE : Function.Injective eA := eA.toRingHom.injective

  have hreg : ∀ (τ : UpperHalfPlane) (x : Fc), eA x ∈ (U₀.pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖V x z‖) := fun τ x => by
    rw [U₀.mem_pt_iff, heA]
    exact isBoundedUnder_congr ((he₀ x τ).mono fun z hz => by rw [hz])

  have hInt : eA.toRingHom.IsIntegral := isIntegral_algHom_of_isCurveOver eA
  have hres : ∀ P P' : AlgebraicCurve.Place ℂ Fc₀, P.restrictAlong eA hInt = P'.restrictAlong eA hInt → P = P' := by
    intro P P' hPP
    obtain ⟨τ, rfl⟩ := hsurj P
    obtain ⟨τ', rfl⟩ := hsurj P'
    obtain ⟨γ, hγ, hγτ⟩ := hsep τ τ' fun x => by
      rw [← hreg τ x, ← hreg τ' x, ← mem_restrictAlong_iff eA hInt (U₀.pt τ) x,
        ← mem_restrictAlong_iff eA hInt (U₀.pt τ') x, hPP]
    exact (U₀.pt_eq_pt_iff τ τ').2 ⟨γ, hγ, hγτ⟩
  have hsurjE : Function.Surjective eA := by
    have hfin : FiniteAlong ℂ eA := AlgebraicCurve.finiteAlong_of_isIntegral eA hInt
    have htop := AlgebraicCurve.Place.subfieldClosure_range_union_eq_top_of_restrictAlong_injOn ℂ eA eA hInt hInt
      hfin hfin ∅ Set.finite_empty (fun P P' _ _ h _ => hres P P' h)
    have hr : Set.range eA = (eA.toRingHom.fieldRange : Set Fc₀) := (RingHom.coe_fieldRange eA.toRingHom).symm
    rw [Set.union_self, hr, Subfield.closure_eq] at htop
    intro y
    have hy : y ∈ eA.toRingHom.fieldRange := by rw [htop]; exact Subfield.mem_top y
    exact RingHom.mem_fieldRange.mp hy

  refine ⟨AlgEquiv.ofBijective eA ⟨hinjE, hsurjE⟩, fun x τ => ?_, fun p x => ?_⟩
  · rw [AlgEquiv.ofBijective_apply, heA]
    exact he₀ x τ
  · rw [AlgEquiv.ofBijective_apply]
    exact (hreg (per p) x).trans (hbc p x).symm

end S_ModularCurve_UniformizedHeckeCurve_exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
end P2MW
export P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits (solution)

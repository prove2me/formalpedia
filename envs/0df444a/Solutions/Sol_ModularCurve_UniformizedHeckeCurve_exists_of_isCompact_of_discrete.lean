-- Prove2me | solution 1 for ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/97f849c0-61ae-5d67-beeb-b22501047cd4

import Definitions.Def_ModularCurve_UniformizedHeckeCurve
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_AutomorphicField
import Theorems.Thm_ModularCurve_automorphicField_realize_laws
import Theorems.Thm_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology
import Theorems.Thm_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology
import Theorems.Thm_ModularCurve_isCurveOver_automorphicField_of_isCompact
import Theorems.Thm_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology
import Theorems.Thm_ModularCurve_exists_pt_eq_of_isCompact
import Theorems.Thm_ModularCurve_exists_realize_eventuallyEq_of_isCompact
import Theorems.Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem
import Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_of_isCompact_of_discrete
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (H : ∀ ℓ : ℕ, ℓ.Prime → Multiset (GL (Fin 2) ℝ))
    (hH : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∀ γ ∈ Γ, ∀ τ : ℍ,
      ((H ℓ hℓ).map fun δ => MulAction.orbit ↥Γ (δ • γ • τ)) =
        ((H ℓ hℓ).map fun δ => MulAction.orbit ↥Γ (δ • τ))) :
    ∃ (Fc : Type) (_ : Field Fc) (_ : Algebra ℂ Fc) (_ : AlgebraicCurve.IsCurveOver ℂ Fc)
      (_ : Algebra.EssFiniteType ℂ Fc) (U : ModularCurve.UniformizedHeckeCurve Γ Fc),
      Function.Surjective U.pt ∧ U.heckePoints = H ∧

      (∀ (x : Fc) (τ : ℍ), MeromorphicAt (fun z : ℂ => U.realize x (ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ, U.realize (x + y) z = U.realize x z + U.realize y z) ∧
      (∀ (x y : Fc) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ, U.realize (x * y) z = U.realize x z * U.realize y z) ∧
      (∀ (c : ℂ) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ, U.realize (algebraMap ℂ Fc c) z = c) ∧
      (∀ x y : Fc, (∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = U.realize y z) → x = y) ∧

      (∀ x : Fc, ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, U.realize x (γ • z) = U.realize x z) ∧

      (∀ f : ℍ → ℂ, (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = f z) := by
  classical
  haveI hΓ : Γ.HasDetOne := ⟨fun hγ => hdet _ hγ⟩
  obtain ⟨hsep, hloc⟩ :=
    ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology Γ hdet hneg hcusp
  obtain ⟨hcompute, hmer, hadd, hmul, hconst, hinj, hinvr⟩ := ModularCurve.automorphicField_realize_laws Γ
  obtain ⟨pt, hmem, hord, hpteq⟩ :=
    ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology Γ hneg hsep hloc

  have he_two : ∀ τ : ℍ, 2 * (Nat.card (MulAction.stabilizer Γ τ) / 2) = Nat.card (MulAction.stabilizer Γ τ) :=
    fun τ => Nat.mul_div_cancel' (UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ hdet hneg τ)
  have he_pos : ∀ τ : ℍ, 0 < Nat.card (MulAction.stabilizer Γ τ) / 2 := by
    intro τ
    haveI := (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ).1
    have hc : 0 < Nat.card (MulAction.stabilizer Γ τ) := Nat.card_pos
    have h2 := he_two τ
    omega
  have hx : ∃ x : ↥(ModularCurve.automorphicField Γ),
      x ∉ Set.range (algebraMap ℂ ↥(ModularCurve.automorphicField Γ)) := by
    obtain ⟨k, -, -, g, h, hh0, hordgh⟩ := hloc UpperHalfPlane.I
    have hhne : (h : ℍ → ℂ) ≠ 0 := fun h0 => hh0 (by rw [h0]; rfl)
    have hs : h.toHolRing ≠ 0 := by rwa [Ne, ModularForm.toHolRing_eq_zero_iff]
    set ι := algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) with hι
    refine ⟨⟨ι g.toHolRing / ι h.toHolRing, ⟨k, g, h, hhne, rfl⟩⟩, ?_⟩
    rintro ⟨c, hc⟩
    have h1 := hconst c UpperHalfPlane.I
    rw [hc] at h1
    have h2 := hcompute g.toHolRing h.toHolRing hs UpperHalfPlane.I
    have h3 : ∀ᶠ z in 𝓝[≠] UpperHalfPlane.I, (g : ℍ → ℂ) z / (h : ℍ → ℂ) z = c := by
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [ModularForm.coe_toHolRing] at hz2
      rw [← hz2]
      exact hz1

    have h4 : ∀ᶠ w in 𝓝[≠] ((UpperHalfPlane.I : ℍ) : ℂ),
        (fun w : ℂ => (g : ℍ → ℂ) (ofComplex w) / (h : ℍ → ℂ) (ofComplex w)) w = (fun _ : ℂ => c) w := by
      rw [eventually_nhdsWithin_iff] at h3
      rw [eventually_nhdsWithin_iff, ← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.eventually_map]
      filter_upwards [h3] with z hz hne
      have hne' : z ∈ ({UpperHalfPlane.I} : Set ℍ)ᶜ := fun e =>
        hne (by rw [Set.mem_singleton_iff.mp e]; exact Set.mem_singleton _)
      simpa only [ofComplex_apply] using hz hne'
    have h5 := meromorphicOrderAt_congr h4
    rw [hordgh, meromorphicOrderAt_const] at h5
    have hpos := he_pos UpperHalfPlane.I
    split_ifs at h5
    · exact WithTop.coe_ne_top h5
    · have : ((Nat.card (MulAction.stabilizer Γ UpperHalfPlane.I) / 2 : ℕ) : ℤ) = 0 := by exact_mod_cast h5
      omega
  obtain ⟨hcurve, hfin, -⟩ := ModularCurve.isCurveOver_automorphicField_of_isCompact Γ hcpt hx
  have hsurj : ∀ P : AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ), ∃ τ : ℍ, pt τ = P :=
    fun P => ModularCurve.exists_pt_eq_of_isCompact Γ hcpt pt hmem P
  have hample := ModularCurve.exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology Γ hdet hcusp
  have hcomplete := ModularCurve.exists_realize_eventuallyEq_of_isCompact Γ hcpt hcusp hample

  let sec : AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ) → ℍ := fun P => (hsurj P).choose
  have hsec : ∀ P, pt (sec P) = P := fun P => (hsurj P).choose_spec
  let corr : ∀ ℓ : ℕ, ℓ.Prime →
      (AlgebraicCurve.Divisor ℂ ↥(ModularCurve.automorphicField Γ) →+
        AlgebraicCurve.Divisor ℂ ↥(ModularCurve.automorphicField Γ)) :=
    fun ℓ hℓ => Finsupp.liftAddHom fun P =>
      zmultiplesHom (AlgebraicCurve.Divisor ℂ ↥(ModularCurve.automorphicField Γ))
        (((H ℓ hℓ).map fun δ => Finsupp.single (pt (δ • sec P)) (1 : ℤ)).sum)
  refine ⟨↥(ModularCurve.automorphicField Γ), inferInstance, inferInstance, hcurve, hfin,
    { pt := pt
      realize := ModularCurve.automorphicField.realize
      ramification := fun τ => Nat.card (MulAction.stabilizer Γ τ) / 2
      ramification_pos := he_pos
      mem_pt_iff := hmem
      meromorphicOrderAt_realize := hord
      pt_eq_pt_iff := hpteq
      distinguished := 1
      exists_pt_eq := fun P _ => hsurj P
      two_mul_ramification := he_two
      heckePoints := H
      corr := corr
      corr_single_pt := ?_ }, ?_, rfl, hmer, hadd, hmul, hconst, hinj, hinvr, hcomplete⟩
  ·
    intro ℓ hℓ τ

    have hpt_orbit : ∀ x y : ℍ, MulAction.orbit (↥Γ) x = MulAction.orbit (↥Γ) y → pt x = pt y := by
      intro x y hxy
      have hy : y ∈ MulAction.orbit (↥Γ) x := hxy ▸ MulAction.mem_orbit_self y
      obtain ⟨γ, hγ⟩ := hy
      exact (hpteq x y).2 ⟨γ, γ.2, hγ⟩
    let φ : Set ℍ → AlgebraicCurve.Divisor ℂ ↥(ModularCurve.automorphicField Γ) := fun s =>
      if h : ∃ x : ℍ, MulAction.orbit (↥Γ) x = s then Finsupp.single (pt h.choose) (1 : ℤ) else 0
    have hφ : ∀ x : ℍ, φ (MulAction.orbit (↥Γ) x) = Finsupp.single (pt x) (1 : ℤ) := by
      intro x
      have h : ∃ y : ℍ, MulAction.orbit (↥Γ) y = MulAction.orbit (↥Γ) x := ⟨x, rfl⟩
      simp only [φ, dif_pos h]
      rw [hpt_orbit h.choose x h.choose_spec]

    obtain ⟨γ, hγ, hγτ⟩ := (hpteq τ (sec (pt τ))).1 (hsec (pt τ)).symm
    simp only [corr, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_smul]
    have e1 : ((H ℓ hℓ).map fun δ => Finsupp.single (pt (δ • sec (pt τ))) (1 : ℤ)) =
        ((H ℓ hℓ).map fun δ => MulAction.orbit (↥Γ) (δ • γ • τ)).map φ := by
      rw [Multiset.map_map, ← hγτ]
      exact Multiset.map_congr rfl (fun δ _ => (hφ _).symm)
    have e2 : ((H ℓ hℓ).map fun δ => Finsupp.single (pt (δ • τ)) (1 : ℤ)) =
        ((H ℓ hℓ).map fun δ => MulAction.orbit (↥Γ) (δ • τ)).map φ := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl (fun δ _ => (hφ _).symm)
    rw [e1, e2, hH ℓ hℓ γ hγ τ]
  ·
    exact fun P => hsurj P

end S_ModularCurve_UniformizedHeckeCurve_exists_of_isCompact_of_discrete
end P2MW
export P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_of_isCompact_of_discrete (solution)

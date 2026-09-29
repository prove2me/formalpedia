-- Prove2me | solution 1 for ModularCurve.exists_pt_eq_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/766afde0-c5e3-5f9c-916b-2354985659a2

import Mathlib
import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_automorphicField_realize_laws
import Theorems.Thm_ModularCurve_isCurveOver_automorphicField_of_isCompact
import Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_range_and_forall_ne_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_pt_eq_of_isCompact
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped MatrixGroups Topology Manifold ModularForm
open UpperHalfPlane

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "automorphicField automorphicField.realize automorphicField_realize_laws isCurveOver_automorphicField_of_isCompact"
namespace T6Aux
p2m_open "ModularCurve"

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := UpperHalfPlane.isOpenEmbedding_coe.map_nhdsWithin_preimage_eq {(τ : ℂ)}ᶜ τ
  have : ((↑) : ℍ → ℂ) ⁻¹' {(τ : ℂ)}ᶜ = {τ}ᶜ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, UpperHalfPlane.ext_iff]
  rw [this] at h
  exact h

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map this

theorem eventually_coe_iff {τ : ℍ} {p : ℂ → Prop} :
    (∀ᶠ (w : ℍ) in 𝓝[≠] τ, p (UpperHalfPlane.coe w)) ↔ ∀ᶠ z in 𝓝[≠] (τ : ℂ), p z := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]

theorem eventually_ofComplex_iff {τ : ℍ} {p : ℍ → Prop} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ z in 𝓝[≠] τ, p z := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem tendsto_smul_nhdsNE (g : GL (Fin 2) ℝ) (τ : ℍ) :
    Filter.Tendsto (fun z : ℍ => g • z) (𝓝[≠] τ) (𝓝[≠] (g • τ)) := by
  refine ((continuous_const_smul g).continuousWithinAt).tendsto_nhdsWithin ?_
  intro z hz h
  exact hz (MulAction.injective g h)

theorem mem_range_algebraMap_of_forall_isBoundedUnder
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (x : ↥(ModularCurve.automorphicField Γ))
    (hb : ∀ τ : ℍ, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖)) :
    x ∈ Set.range (algebraMap ℂ ↥(ModularCurve.automorphicField Γ)) := by
  classical
  obtain ⟨h0, hmer, hadd, hmul, hconst, hinj, hinv⟩ := ModularCurve.automorphicField_realize_laws Γ
  obtain ⟨K, hK, hKcov⟩ := hcpt

  have hord : ∀ τ : ℍ, 0 ≤ meromorphicOrderAt
      (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ) := by
    intro τ
    by_contra hneg
    have hlt := lt_of_not_ge hneg
    have ht := tendsto_cobounded_of_meromorphicOrderAt_neg hlt
    rw [← tendsto_norm_atTop_iff_cobounded] at ht
    obtain ⟨M, hM⟩ := hb τ
    have hM' : ∀ᶠ z in 𝓝[≠] τ, ‖ModularCurve.automorphicField.realize x z‖ ≤ M :=
      Filter.eventually_map.mp hM
    have hMC : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖ModularCurve.automorphicField.realize x (ofComplex z)‖ ≤ M :=
      (eventually_ofComplex_iff (p := fun w : ℍ => ‖ModularCurve.automorphicField.realize x w‖ ≤ M)).mpr hM'
    have hbig := ht.eventually (Filter.eventually_ge_atTop (M + 1))
    obtain ⟨z, hz1, hz2⟩ := (hMC.and hbig).exists
    linarith

  have hhmer : MeromorphicOn (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z))
      {z : ℂ | 0 < z.im} := fun z hz => hmer x ⟨z, hz⟩
  obtain ⟨g, hgmd, hgev⟩ : ∃ g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧
      ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, g z = ModularCurve.automorphicField.realize x z := by
    let G : ℂ → ℂ :=
      toMeromorphicNFOn (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) {z : ℂ | 0 < z.im}
    have hGev : ∀ τ : ℍ, G =ᶠ[𝓝[≠] (τ : ℂ)]
        (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) :=
      fun τ => hhmer.toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos
    have hGan : ∀ τ : ℍ, AnalyticAt ℂ G (τ : ℂ) := by
      intro τ
      have hNF : MeromorphicNFAt G (τ : ℂ) :=
        meromorphicNFOn_toMeromorphicNFOn
          (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) _ τ.im_pos
      refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
      rw [meromorphicOrderAt_congr (hGev τ)]
      exact hord τ
    refine ⟨fun τ => G τ, ?_, ?_⟩
    · rw [UpperHalfPlane.mdifferentiable_iff]
      have hGd : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} :=
        fun z hz => (hGan ⟨z, hz⟩).differentiableAt.differentiableWithinAt
      refine hGd.congr fun z hz => ?_
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
    · intro τ
      refine ((eventually_coe_iff
        (p := fun z : ℂ => G z = ModularCurve.automorphicField.realize x (ofComplex z))).mpr
        (hGev τ)).mono fun w hw => ?_
      simpa only [ofComplex_apply] using hw

  have hginv : ∀ γ ∈ Γ, ∀ τ : ℍ, g (γ • τ) = g τ := by
    intro γ hγ τ₀
    have e1 : ∀ᶠ z in 𝓝[≠] τ₀, g (γ • z) = ModularCurve.automorphicField.realize x (γ • z) :=
      (tendsto_smul_nhdsNE γ τ₀).eventually (hgev (γ • τ₀))
    have ev : ∀ᶠ z in 𝓝[≠] τ₀, g (γ • z) = g z := by
      filter_upwards [e1, hinv x γ hγ τ₀, hgev τ₀] with z h1 h2 h3
      rw [h1, h2, h3]
    have c1 : ContinuousAt (fun z : ℍ => g (γ • z)) τ₀ :=
      (hgmd.continuous.comp (continuous_const_smul γ)).continuousAt
    have c2 : ContinuousAt g τ₀ := hgmd.continuous.continuousAt
    exact tendsto_nhds_unique_of_eventuallyEq (c1.tendsto.mono_left nhdsWithin_le_nhds)
      (c2.tendsto.mono_left nhdsWithin_le_nhds) ev

  have hKne : K.Nonempty := by
    obtain ⟨γ, -, hγ⟩ := hKcov UpperHalfPlane.I
    exact ⟨_, hγ⟩
  obtain ⟨τ₀, hτ₀K, hmax⟩ := hK.exists_isMaxOn hKne (hgmd.continuous.norm.continuousOn)
  have hle : ∀ τ : ℍ, ‖g τ‖ ≤ ‖g τ₀‖ := by
    intro τ
    obtain ⟨γ, hγ, hγK⟩ := hKcov τ
    rw [← hginv γ hγ τ]
    exact hmax hγK
  have hGd : DifferentiableOn ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hgmd
  have hmaxU : IsMaxOn (norm ∘ (g ∘ ofComplex)) {z : ℂ | 0 < z.im} (τ₀ : ℂ) := by
    intro z hz
    have hz' : 0 < z.im := hz
    simp only [Set.mem_setOf_eq, Function.comp_apply, ofComplex_apply_of_im_pos hz', ofComplex_apply]
    exact hle ⟨z, hz'⟩
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (Complex.isConnected_of_upperHalfPlane subset_rfl (fun z hz => by
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact le_of_lt hz)).isPreconnected
  have hconstU := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn isOpen_upperHalfPlaneSet hGd
    τ₀.im_pos hmaxU
  have hgc : ∀ τ : ℍ, g τ = g τ₀ := by
    intro τ
    have := hconstU τ.im_pos
    simpa only [Function.comp_apply, ofComplex_apply, Function.const_apply] using this

  refine ⟨g τ₀, hinj _ _ fun τ => ?_⟩
  filter_upwards [hconst (g τ₀) τ, hgev τ] with z h1 h2
  rw [h1, ← hgc z, h2]

end ModularCurve.T6Aux
p2m_reactivate "P2MW.S_ModularCurve_exists_pt_eq_of_isCompact.ModularCurve P2MW.S_ModularCurve_exists_pt_eq_of_isCompact.ModularCurve.T6Aux"
p2m_reactivate "P2MW.S_ModularCurve_exists_pt_eq_of_isCompact.ModularCurve"

namespace T6A9A

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_toValuationSubring_of_ord_nonneg (v : Place K F) {y : F} (hy : 0 ≤ v.ord y) :
    y ∈ v.toValuationSubring := by
  by_contra hmem
  have hy0 : y ≠ 0 := by
    rintro rfl; exact hmem (zero_mem _)
  have hinv : y⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem y).resolve_left hmem

  have hnu : ¬ IsUnit (⟨y⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hmem
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * (u : v.toValuationSubring) = 1 := u.inv_mul
    have h2 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * y⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) h1
      simpa [hu] using this
    have h3 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = y := by
      rw [mul_inv_eq_one₀ hy0] at h2
      exact h2
    rw [← h3]
    exact ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2

  have hle : v.adicValuation y⁻¹ ≤ 1 := v.adicValuation_le_one_of_mem hinv
  have hne : v.adicValuation y⁻¹ ≠ 1 := by
    intro h
    exact hnu ((v.adicValuation_coe_eq_one_iff ⟨y⁻¹, hinv⟩).mp h)
  have hlt : v.adicValuation y⁻¹ < 1 := lt_of_le_of_ne hle hne
  rw [v.adicValuation_eq_exp_neg_ord (inv_ne_zero hy0), ← WithZero.exp_zero, WithZero.exp_lt_exp,
    v.ord_inv] at hlt
  omega

theorem exists_nonconst_regular_away [IsAlgClosed K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (P : Place K F) :
    ∃ x : F, x ∉ Set.range (algebraMap K F) ∧ ∀ Q : Place K F, Q ≠ P → x ∈ Q.toValuationSubring := by
  obtain ⟨y, hy, hord⟩ := Place.exists_not_mem_range_and_forall_ne_ord_nonneg K F P
  exact ⟨y, hy, fun Q hQ => mem_toValuationSubring_of_ord_nonneg Q (hord Q hQ)⟩

end T6A9A
p2m_reactivate "P2MW.S_ModularCurve_exists_pt_eq_of_isCompact.ModularCurve P2MW.S_ModularCurve_exists_pt_eq_of_isCompact.ModularCurve.T6Aux"

open ModularCurve.T6Aux in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    [AlgebraicCurve.IsCurveOver ℂ ↥(ModularCurve.automorphicField Γ)]
    (pt : ℍ → AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ))
    (hpt : ∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖))
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ)) :
    ∃ τ : ℍ, pt τ = P := by
  classical
  by_contra hP
  have hP' : ∀ τ : ℍ, pt τ ≠ P := fun τ h => hP ⟨τ, h⟩

  have hx : ∃ x : ↥(ModularCurve.automorphicField Γ),
      x ∉ Set.range (algebraMap ℂ ↥(ModularCurve.automorphicField Γ)) := by
    obtain ⟨y, -, hy⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr P.ne_top')
    refine ⟨y, ?_⟩
    rintro ⟨c, rfl⟩
    exact hy (P.algebraMap_mem' c)
  obtain ⟨_, hEFT, _⟩ := ModularCurve.isCurveOver_automorphicField_of_isCompact Γ hcpt hx
  obtain ⟨y, hync, hyreg⟩ :=
    T6A9A.exists_nonconst_regular_away (K := ℂ) (F := ↥(ModularCurve.automorphicField Γ)) P
  apply hync
  apply mem_range_algebraMap_of_forall_isBoundedUnder Γ hcpt y
  intro τ
  exact (hpt τ y).mp (hyreg (pt τ) (hP' τ))

end
end S_ModularCurve_exists_pt_eq_of_isCompact
end P2MW
export P2MW.S_ModularCurve_exists_pt_eq_of_isCompact (solution)

-- Prove2me | solution 1 for ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b31bddfa-8b5d-57d5-a8d3-bb3d71a66900

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_isAlgClosed_of_charZero
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

open AlgebraicCurve ModularCurve
open scoped Pointwise

namespace A2JOneLevel

universe u

variable {L : Type u} [Field L] [Algebra ℚ L]

def Good (s : Set (L ≃ₐ[ℚ] L)) : Prop :=
  ∃ E : IntermediateField ℚ L, FiniteDimensional ℚ E ∧
    (E.fixingSubgroup : Set (L ≃ₐ[ℚ] L)) ⊆ s

theorem Good.mono {s t : Set (L ≃ₐ[ℚ] L)} (hs : Good s) (hst : s ⊆ t) : Good t := by
  obtain ⟨E, hE, hEs⟩ := hs
  exact ⟨E, hE, hEs.trans hst⟩

theorem Good.of_forall {s : Set (L ≃ₐ[ℚ] L)} (h : ∀ σ, σ ∈ s) : Good s :=
  ⟨⊥, inferInstance, fun σ _ => h σ⟩

theorem Good.inter {s t : Set (L ≃ₐ[ℚ] L)} (hs : Good s) (ht : Good t) : Good (s ∩ t) := by
  obtain ⟨E, hE, hEs⟩ := hs
  obtain ⟨E', hE', hEt⟩ := ht
  haveI := hE
  haveI := hE'
  refine ⟨E ⊔ E', IntermediateField.finiteDimensional_sup E E', fun σ hσ => ⟨hEs ?_, hEt ?_⟩⟩
  · exact IntermediateField.fixingSubgroup_antitone le_sup_left hσ
  · exact IntermediateField.fixingSubgroup_antitone le_sup_right hσ

theorem Good.biInter_finset {ι : Type*} (S : Finset ι) (s : ι → Set (L ≃ₐ[ℚ] L))
    (h : ∀ i ∈ S, Good (s i)) : Good (⋂ i ∈ S, s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Good.of_forall fun σ => by simp
  | insert a S ha ih =>
      have h1 : Good (s a) := h a (Finset.mem_insert_self a S)
      have h2 : Good (⋂ i ∈ S, s i) := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine (h1.inter h2).mono ?_
      intro σ hσ
      have h2' : ∀ i ∈ S, σ ∈ s i := by simpa only [Set.mem_iInter] using hσ.2
      simp only [Finset.mem_insert, Set.mem_iInter, forall_eq_or_imp]
      exact ⟨hσ.1, h2'⟩

theorem Good.exists_subgroup {s : Set (L ≃ₐ[ℚ] L)} (hs : Good s) :
    ∃ E : IntermediateField ℚ L, FiniteDimensional ℚ E ∧
      ∀ σ ∈ E.fixingSubgroup, σ ∈ s ∧ σ⁻¹ ∈ s := by
  obtain ⟨E, hE, hEs⟩ := hs
  exact ⟨E, hE, fun σ hσ => ⟨hEs hσ, hEs (E.fixingSubgroup.inv_mem hσ)⟩⟩

section Elements

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem good_fix_coeffMap [Algebra.IsAlgebraic ℚ L] {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    Good {σ : L ≃ₐ[ℚ] L | coeffMap (σ : L →+* L) x = x} := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, _, rfl⟩
      ·
        refine ⟨IntermediateField.adjoin ℚ {a},
          IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic a).isIntegral,
          fun σ hσ => ?_⟩
        have hσa : σ a = a := by
          rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
          exact hσ a (IntermediateField.mem_adjoin_simple_self ℚ a)
        show coeffMap (σ : L →+* L) (algebraMap L (LaurentSeries L) a) = _
        rw [coeffMap_algebraMap]
        exact congrArg (algebraMap L (LaurentSeries L)) hσa
      ·
        exact Good.of_forall fun σ => coeffMap_coeffEmb σ z
  | one => exact Good.of_forall fun σ => map_one _
  | add y z _ _ hy hz =>
      refine (hy.inter hz).mono ?_
      rintro σ ⟨h1, h2⟩
      show coeffMap (σ : L →+* L) (y + z) = y + z
      rw [map_add, h1, h2]
  | neg y _ hy =>
      refine hy.mono fun σ h1 => ?_
      show coeffMap (σ : L →+* L) (-y) = -y
      rw [map_neg, h1]
  | inv y _ hy =>
      refine hy.mono fun σ h1 => ?_
      show coeffMap (σ : L →+* L) y⁻¹ = y⁻¹
      rw [map_inv₀, h1]
  | mul y z _ _ hy hz =>
      refine (hy.inter hz).mono ?_
      rintro σ ⟨h1, h2⟩
      show coeffMap (σ : L →+* L) (y * z) = y * z
      rw [map_mul, h1, h2]

theorem good_fix_elem [Algebra.IsAlgebraic ℚ L] (x : laurentBaseChange L F₀) :
    Good {σ : L ≃ₐ[ℚ] L | arithmeticGalois F₀ σ • x = x} := by
  refine (good_fix_coeffMap F₀ x.2).mono fun σ hσ => ?_
  exact Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact hσ)

end Elements

section Places

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (ρ : (L ≃ₐ[ℚ] L) →* SemilinearAut K F)

theorem exists_not_iff_of_ne {v w : Place K F} (h : w ≠ v) :
    ∃ x : F, ¬ (x ∈ v.toValuationSubring ↔ x ∈ w.toValuationSubring) := by
  by_contra hcon
  push Not at hcon
  exact h (Place.ext (SetLike.ext fun x => (hcon x).symm))

theorem good_fix_place [HasPrincipalDivisors K F]
    (hfix : ∀ x : F, Good {σ : L ≃ₐ[ℚ] L | ρ σ • x = x}) (v : Place K F) :
    Good {σ : L ≃ₐ[ℚ] L | ρ σ • v = v} := by
  classical

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hordπ : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (π : F) hπ0

  have hZ : ∀ g : SemilinearAut K F, g • (π : F) = (π : F) → g • v ∈ D.support := by
    intro g hg
    have h1 : (g • v).ord (π : F) = 1 := by
      have := SemilinearAut.ord_smul g v (π : F)
      rwa [hg, hordπ] at this
    rw [Finsupp.mem_support_iff, hD, h1]
    exact one_ne_zero

  have hx : ∀ w : Place K F, ∃ x : F,
      w ≠ v → ¬ (x ∈ v.toValuationSubring ↔ x ∈ w.toValuationSubring) := by
    intro w
    by_cases h : w = v
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨x, hx⟩ := exists_not_iff_of_ne h
      exact ⟨x, fun _ => hx⟩
  choose x hx using hx

  have hgood : Good ({σ : L ≃ₐ[ℚ] L | ρ σ • (π : F) = (π : F)} ∩
      ⋂ w ∈ D.support, {σ : L ≃ₐ[ℚ] L | ρ σ • x w = x w}) :=
    (hfix (π : F)).inter (Good.biInter_finset D.support _ fun w _ => hfix (x w))
  obtain ⟨E, hE, hEs⟩ := hgood.exists_subgroup
  refine ⟨E, hE, fun σ hσ => ?_⟩
  obtain ⟨⟨hσπ, -⟩, ⟨-, hσx'⟩⟩ := hEs σ hσ
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσπ hσx'
  show ρ σ • v = v
  by_contra hne
  have hmem : ρ σ • v ∈ D.support := hZ (ρ σ) hσπ
  have hfix' : (ρ σ)⁻¹ • x (ρ σ • v) = x (ρ σ • v) := by
    have := hσx' (ρ σ • v) hmem
    rwa [map_inv] at this
  apply hx (ρ σ • v) hne
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hfix']

theorem good_fix_pic0 [HasPrincipalDivisors K F]
    (hfix : ∀ x : F, Good {σ : L ≃ₐ[ℚ] L | ρ σ • x = x}) (y : Pic0 K F) :
    Good {σ : L ≃ₐ[ℚ] L | ρ σ • y = y} := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  have hgood : Good (⋂ v ∈ (D : Divisor K F).support, {σ : L ≃ₐ[ℚ] L | ρ σ • v = v}) :=
    Good.biInter_finset _ _ fun v _ => good_fix_place ρ hfix v
  refine hgood.mono fun σ hσ => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσ
  have hD : ρ σ • (D : Divisor K F) = (D : Divisor K F) := by
    rw [SemilinearAut.divisor_smul_def]
    conv_rhs => rw [← Finsupp.mapDomain_id (v := (D : Divisor K F))]
    exact Finsupp.mapDomain_congr fun v hv => hσ v hv
  simp only [Set.mem_setOf_eq]
  rw [SemilinearAut.pic0_smul_mk]
  congr 1
  exact Subtype.ext (by rw [SemilinearAut.coe_degZeroSMulHom]; exact hD)

end Places

theorem exists_fixingSubgroup_le_stabilizer [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors L (laurentBaseChange L F₀)]
    (y : Pic0 L (laurentBaseChange L F₀)) :
    ∃ E : IntermediateField ℚ L, FiniteDimensional ℚ E ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ ∈ E.fixingSubgroup → σ • y = y := by
  obtain ⟨E, hE, hEs⟩ := good_fix_pic0 (arithmeticGalois F₀) (good_fix_elem F₀) y
  refine ⟨E, hE, fun σ hσ => ?_⟩
  rw [galois_smul_pic0_def]
  exact hEs hσ

open scoped MatrixGroups in

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem exists_transcendental_finiteDimensional_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    ∃ x : x1FunctionFieldBar M, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (x1FunctionFieldBar M)))
        (x1FunctionFieldBar M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (T_mem_Gamma1 M)

theorem isCurveOver_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    IsCurveOver (AlgebraicClosure ℚ) (x1FunctionFieldBar M) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_x1FunctionFieldBar M
  haveI := hfin
  haveI : PerfectField
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (x1FunctionFieldBar M))) :=
    PerfectField.ofCharZero
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin
    Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem finite_torsion_JOne (M : ℕ) [NeZero M] (n : ℕ) (hn : n ≠ 0) :
    Finite {c : JOne M // n • c = 0} := by
  haveI := isCurveOver_x1FunctionFieldBar M
  exact AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero (AlgebraicClosure ℚ)
    (x1FunctionFieldBar M) (exists_transcendental_finiteDimensional_x1FunctionFieldBar M) n hn

end A2JOneLevel

theorem solution (M : ℕ) [NeZero M]
    (n : ℕ) (hn : 0 < n) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ P : ModularCurve.JOne M, (n : ℤ) • P = 0 → σ • P = P := by

  haveI hfin : Finite {c : JOne M // n • c = 0} := A2JOneLevel.finite_torsion_JOne M n hn.ne'

  haveI := A2JOneLevel.isCurveOver_x1FunctionFieldBar M
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hE : ∀ P : {c : JOne M // n • c = 0},
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ E.fixingSubgroup →
          σ • (P : JOne M) = P := fun P =>
    A2JOneLevel.exists_fixingSubgroup_le_stabilizer (x1FunctionField M) (P : JOne M)
  choose E hEfin hEfix using hE

  haveI : ∀ P, FiniteDimensional ℚ (E P) := hEfin
  refine ⟨⨆ P, E P, IntermediateField.finiteDimensional_iSup_of_finite, fun σ hσ P hP => ?_⟩
  have hP' : n • P = 0 := by rwa [natCast_zsmul] at hP
  refine hEfix ⟨P, hP'⟩ σ ?_
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => hσ x (le_iSup E ⟨P, hP'⟩ hx)

end S_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion
end P2MW
export P2MW.S_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion (solution)

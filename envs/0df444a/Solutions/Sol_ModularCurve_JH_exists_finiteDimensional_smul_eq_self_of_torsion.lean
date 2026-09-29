-- Prove2me | solution 1 for ModularCurve.JH.exists_finiteDimensional_smul_eq_self_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cc175243-c09d-5c71-838f-1205671c0d9b

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_Pic0_abelJacobiCard_genus
import Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

open Submodule
open AlgebraicCurve ModularCurve
open scoped Pointwise

namespace JHStab

universe u

variable {L : Type u} [Field L] [Algebra ℚ L]

def Good (s : Set (L ≃ₐ[ℚ] L)) : Prop :=
  ∃ E : IntermediateField ℚ L, FiniteDimensional ℚ E ∧
    (E.fixingSubgroup : Set (L ≃ₐ[ℚ] L)) ⊆ s

theorem Good.mono {s t : Set (L ≃ₐ[ℚ] L)} (hs : Good s) (hst : s ⊆ t) : Good t := by
  obtain ⟨E, hE, hEs⟩ := hs
  exact ⟨E, hE, hEs.trans hst⟩

theorem Good.univ : Good (Set.univ : Set (L ≃ₐ[ℚ] L)) := by
  refine ⟨IntermediateField.adjoin ℚ {(1 : L)}, ?_, Set.subset_univ _⟩
  exact IntermediateField.adjoin.finiteDimensional isIntegral_one

theorem Good.of_forall {s : Set (L ≃ₐ[ℚ] L)} (h : ∀ σ, σ ∈ s) : Good s :=
  Good.univ.mono fun σ _ => h σ

theorem Good.inter {s t : Set (L ≃ₐ[ℚ] L)} (hs : Good s) (ht : Good t) : Good (s ∩ t) := by
  obtain ⟨E, hE, hEs⟩ := hs
  obtain ⟨E', hE', hEt⟩ := ht
  haveI := hE
  haveI := hE'
  refine ⟨E ⊔ E', IntermediateField.finiteDimensional_sup E E', ?_⟩
  intro σ hσ
  refine ⟨hEs ?_, hEt ?_⟩
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
      have h2' : ∀ i ∈ S, σ ∈ s i := by
        have := hσ.2
        simpa only [Set.mem_iInter] using this
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
        refine ⟨IntermediateField.adjoin ℚ {a}, ?_, ?_⟩
        · exact IntermediateField.adjoin.finiteDimensional
            (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
        · intro σ hσ
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
      rw [map_add]
      exact congrArg₂ (· + ·) h1 h2
  | neg y _ hy =>
      refine hy.mono ?_
      intro σ h1
      show coeffMap (σ : L →+* L) (-y) = -y
      rw [map_neg]
      exact congrArg (fun t => -t) h1
  | inv y _ hy =>
      refine hy.mono ?_
      intro σ h1
      show coeffMap (σ : L →+* L) y⁻¹ = y⁻¹
      rw [map_inv₀]
      exact congrArg (fun t => t⁻¹) h1
  | mul y z _ _ hy hz =>
      refine (hy.inter hz).mono ?_
      rintro σ ⟨h1, h2⟩
      show coeffMap (σ : L →+* L) (y * z) = y * z
      rw [map_mul]
      exact congrArg₂ (· * ·) h1 h2

theorem good_fix_elem [Algebra.IsAlgebraic ℚ L] (x : laurentBaseChange L F₀) :
    Good {σ : L ≃ₐ[ℚ] L | arithmeticGalois F₀ σ • x = x} := by
  refine (good_fix_coeffMap F₀ x.2).mono ?_
  intro σ hσ
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
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
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
  refine ⟨E, hE, ?_⟩
  intro σ hσ
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
  have hgood : Good (⋂ v ∈ (D : Divisor K F).support,
      {σ : L ≃ₐ[ℚ] L | ρ σ • v = v}) :=
    Good.biInter_finset _ _ fun v _ => good_fix_place ρ hfix v
  refine hgood.mono ?_
  intro σ hσ
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

theorem isOpen_stabilizer_pic0 [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    [HasPrincipalDivisors L (laurentBaseChange L F₀)]
    (y : Pic0 L (laurentBaseChange L F₀)) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[ℚ] L) y : Set (L ≃ₐ[ℚ] L)) := by
  obtain ⟨E, hE, hEs⟩ := good_fix_pic0 (arithmeticGalois F₀) (good_fix_elem F₀) y
  haveI := hE
  refine Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff, galois_smul_pic0_def]
  exact hEs hσ

end JHStab

namespace JHPort

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem finiteIndex_GammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem exists_transcendental_finiteDimensional_xHFunctionFieldBar :
    ∃ x : xHFunctionFieldBar M H, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
        (xHFunctionFieldBar M H) := by
  haveI := finiteIndex_GammaH M H
  exact ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)

theorem essFiniteType_of_presentation {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  classical
  haveI := hfin
  let K₀ := IntermediateField.adjoin K ({x} : Set F)
  haveI : Module.Free K₀ F := Module.Free.of_divisionRing _ _
  let b := Module.finBasis K₀ F
  rw [← IntermediateField.fg_top_iff, IntermediateField.fg_def]
  refine ⟨insert x (Set.range b), (Set.finite_range b).insert x, ?_⟩
  refine le_antisymm le_top ?_
  intro y _
  have hy := b.sum_repr y
  rw [← hy]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
  refine mul_mem ?_ (IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
  exact IntermediateField.adjoin.mono K _ _
    (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) (b.repr y j).2

theorem isCurveOver_xHFunctionFieldBar :
    IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
  haveI := hfin
  haveI : PerfectField
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H))) :=
    PerfectField.ofCharZero
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
      (xHFunctionFieldBar M H) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin inferInstance

theorem hasCanonicalDivisor_xHFunctionFieldBar :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
  haveI := isCurveOver_xHFunctionFieldBar M H
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) :=
    essFiniteType_of_presentation hfin
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem finite_torsion_JH (n : ℕ) (hn : 0 < n) :
    Finite (Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) := by
  haveI := isCurveOver_xHFunctionFieldBar M H
  haveI := hasCanonicalDivisor_xHFunctionFieldBar M H
  refine AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow (fun p _ k => ?_) n hn
  have h := AlgebraicCurve.Pic0.abelJacobiCard_genus (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)
    (exists_transcendental_finiteDimensional_xHFunctionFieldBar M H) p k
  exact Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end JHPort

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ P : ModularCurve.JH M H, (n : ℤ) • P = 0 → σ • P = P := by

  haveI hfin : Finite (Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :=
    JHPort.finite_torsion_JH M H n hn

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI := JHPort.isCurveOver_xHFunctionFieldBar M H
  have hopen : ∀ y : ModularCurve.JH M H,
      IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := fun y =>
    JHStab.isOpen_stabilizer_pic0 (xHFunctionField M H) y
  have hE : ∀ P : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n,
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
        (E.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ⊆
          MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (P : ModularCurve.JH M H) := fun P =>
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp
      ((hopen (P : ModularCurve.JH M H)).mem_nhds (SetLike.mem_coe.mpr (Subgroup.one_mem _)))
  choose E hEfin hEsub using hE

  haveI : ∀ P, FiniteDimensional ℚ (E P) := hEfin
  refine ⟨⨆ P, E P, IntermediateField.finiteDimensional_iSup_of_finite, fun σ hσ P hP => ?_⟩
  have hP' : P ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n :=
    Pic0.mem_torsion.mpr hP
  have hmem : σ ∈ (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ((⟨P, hP'⟩ : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :
        ModularCurve.JH M H) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    refine hEsub ⟨P, hP'⟩ ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => hσ x (le_iSup E ⟨P, hP'⟩ hx)
  exact MulAction.mem_stabilizer_iff.mp hmem

end S_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
end P2MW
export P2MW.S_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion (solution)

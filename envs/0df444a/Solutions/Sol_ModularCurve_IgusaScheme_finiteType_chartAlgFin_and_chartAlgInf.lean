-- Prove2me | solution 1 for ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0289ddc1-a9e3-5309-aff2-250bfc3bfbdb

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) ∧
      Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) := by
  classical
  set Zl := GaloisRep.ratLocalizedAt ℓ with hZl
  set F := modularFunctionFieldFull N with hF
  haveI hZlFR : IsFractionRing ↥Zl ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  haveI hZlPID : IsPrincipalIdealRing ↥Zl := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  have hZlFinj : Function.Injective (algebraMap ↥Zl ↥F) := by
    rw [IsScalarTower.algebraMap_eq ↥Zl ℚ ↥F]
    exact (algebraMap ℚ ↥F).injective.comp (IsFractionRing.injective ↥Zl ℚ)

  set K := IntermediateField.adjoin ℚ ({jFull N} : Set ↥F) with hK
  haveI hFD : FiniteDimensional ↥K ↥F :=
    finiteDimensional_adjoin_jFull_modularFunctionFieldFull N

  have htjℚ : Transcendental ℚ (jFull N : ↥F) := by
    intro halg
    obtain ⟨p, hp, hev⟩ := halg
    refine transcendental_jq ⟨p, hp, ?_⟩
    have h0 : (algebraMap ↥F (LaurentSeries ℚ)) ((Polynomial.aeval (jFull N : ↥F)) p) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥F (LaurentSeries ℚ)) (jFull N : ↥F) = jq from coe_jFull N] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ↥Zl (jFull N : ↥F) :=
    fun h => htjℚ ((IsFractionRing.isAlgebraic_iff ↥Zl ℚ ↥F).mp h)
  have htji : Transcendental ↥Zl ((jFull N)⁻¹ : ↥F) := fun halg => by
    have := halg.inv; rw [inv_inv] at this; exact htj this

  have hKinv : IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥F) = K := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr
        (K.inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (jFull N)))
    · rw [hK, IntermediateField.adjoin_le_iff]
      intro x hx; obtain rfl := hx
      have h1 := (IntermediateField.adjoin ℚ {(jFull N)⁻¹}).inv_mem
        (IntermediateField.mem_adjoin_simple_self ℚ (jFull N)⁻¹)
      rwa [inv_inv] at h1

  suffices h : ∀ (s : ↥F) (hs : Transcendental ↥Zl s)
      (hFD_s : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s} : Set ↥F)) ↥F),
      Algebra.FiniteType ↥Zl ↥(chartAlg N ℓ {s}) by
    exact ⟨h (jFull N) htj hFD, h (jFull N)⁻¹ htji (hKinv ▸ hFD)⟩
  intro s hs hFD_s
  set A := Algebra.adjoin ↥Zl ({s} : Set ↥F) with hA
  set K' := IntermediateField.adjoin ℚ ({s} : Set ↥F) with hK'def
  haveI hFD' : FiniteDimensional ↥K' ↥F := hFD_s
  haveI hK'sep : Algebra.IsSeparable ↥K' ↥F := inferInstance
  have hsℚ : Transcendental ℚ s :=
    fun h => hs ((IsFractionRing.isAlgebraic_iff ↥Zl ℚ ↥F).mpr h)

  letI algAC : Algebra ↥A ↥(chartAlg N ℓ {s}) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg N ℓ {s})).toRingHom.toAlgebra
  haveI stAC : IsScalarTower ↥Zl ↥A ↥(chartAlg N ℓ {s}) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have hAFT : Algebra.FiniteType ↥Zl ↥A :=
    (Subalgebra.fg_iff_finiteType A).mp ⟨{s}, by rw [Finset.coe_singleton]⟩

  haveI stACF : IsScalarTower ↥A ↥(chartAlg N ℓ {s}) ↥F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hIIC : IsIntegralClosure ↥(chartAlg N ℓ {s}) ↥A ↥F := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, (mem_chartAlg_iff N ℓ).mpr hx⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (mem_chartAlg_iff N ℓ).mp y.2⟩ }

  have haevInj : Function.Injective (Polynomial.aeval (R := ↥Zl) s) :=
    transcendental_iff_injective.mp hs
  have hmemA : ∀ p : Polynomial ↥Zl, (Polynomial.aeval (R := ↥Zl) s) p ∈ A := fun p => by
    rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let eA : Polynomial ↥Zl ≃ₐ[↥Zl] ↥A :=
    AlgEquiv.ofBijective ((Polynomial.aeval (R := ↥Zl) s).codRestrict A hmemA)
      ⟨fun p q h => haevInj (Subtype.ext_iff.mp h),
       fun a => by
         have ha : (a : ↥F) ∈ (Polynomial.aeval (R := ↥Zl) s).range := by
           rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA]; exact a.2
         obtain ⟨p, hp⟩ := ha; exact ⟨p, Subtype.ext hp⟩⟩
  haveI hANoeth : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial ↥Zl) eA.toRingEquiv
  haveI hADom : IsDomain ↥A := inferInstance
  haveI hAUfm : UniqueFactorizationMonoid ↥A :=
    MulEquiv.uniqueFactorizationMonoid eA.toRingEquiv.toMulEquiv inferInstance
  haveI hAIIC : IsIntegrallyClosed ↥A := UniqueFactorizationMonoid.instIsIntegrallyClosed

  have hAK' : ∀ a : ↥A, (a : ↥F) ∈ K' := fun a =>
    Algebra.adjoin_induction
      (fun y hy => Set.mem_singleton_iff.mp hy ▸ IntermediateField.mem_adjoin_simple_self ℚ s)
      (fun r => K'.algebraMap_mem (algebraMap ↥Zl ℚ r))
      (fun _ _ _ _ ha hb => add_mem ha hb)
      (fun _ _ _ _ ha hb => mul_mem ha hb)
      a.2
  let ιAK : ↥A →+* ↥K' := (Subalgebra.val A).toRingHom.codRestrict K'.toSubring (fun a => hAK' a)
  letI algAK : Algebra ↥A ↥K' := ιAK.toAlgebra
  haveI stAKF : IsScalarTower ↥A ↥K' ↥F := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI stZlAK : IsScalarTower ↥Zl ↥A ↥K' :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (Subtype.ext rfl)

  have hιAKinj : Function.Injective (algebraMap ↥A ↥K') := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : ↥K' → ↥F) h)
  have haevNorm : ∀ p : Polynomial ℚ, ∃ b ∈ nonZeroDivisors ↥Zl,
      (Polynomial.aeval (R := ↥Zl) s)
        (IsLocalization.integerNormalization (nonZeroDivisors ↥Zl) p) =
      (algebraMap ↥Zl ↥F b) * (Polynomial.aeval (R := ℚ) s) p := by
    intro p
    obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥Zl) p
    refine ⟨b, hb, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap ℚ s
        (IsLocalization.integerNormalization (nonZeroDivisors ↥Zl) p), hbp,
      Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ↥Zl ℚ (Polynomial ℚ) b,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply ↥Zl ℚ ↥F]
  haveI hAFR : IsFractionRing ↥A ↥K' := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨a, ha⟩
      exact isUnit_iff_ne_zero.mpr fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp ha)
        (hιAKinj (h0.trans (map_zero _).symm))
    · intro k
      obtain ⟨r, t, hrt⟩ :=
        (IntermediateField.mem_adjoin_simple_iff ℚ (α := s) (k : ↥F)).mp (hK'def ▸ k.2)
      obtain ⟨br, hbr, hbrr⟩ := haevNorm r
      obtain ⟨bt, hbt, hbtt⟩ := haevNorm t
      set r' := IsLocalization.integerNormalization (nonZeroDivisors ↥Zl) r
      set t' := IsLocalization.integerNormalization (nonZeroDivisors ↥Zl) t
      by_cases ht0 : (Polynomial.aeval (R := ℚ) s) t = 0
      · refine ⟨⟨0, 1⟩, ?_⟩
        have hk0 : k = 0 := Subtype.ext (by
          show (k : ↥F) = 0; rw [hrt, ht0, div_zero])
        simp [hk0]
      · set ar : ↥A := ⟨(Polynomial.aeval (R := ↥Zl) s) r', hmemA r'⟩
        set at' : ↥A := ⟨(Polynomial.aeval (R := ↥Zl) s) t', hmemA t'⟩
        set abr : ↥A := algebraMap ↥Zl ↥A br with habr
        set abt : ↥A := algebraMap ↥Zl ↥A bt with habt
        have hat'nz : at' ≠ 0 := fun h0 => by
          have h0F : (Polynomial.aeval (R := ↥Zl) s) t' = 0 :=
            congrArg (Subtype.val : ↥A → ↥F) h0
          rw [hbtt] at h0F
          rcases mul_eq_zero.mp h0F with hc | hc
          · exact (mem_nonZeroDivisors_iff_ne_zero.mp hbt) (hZlFinj (by rw [hc, map_zero]))
          · exact ht0 hc
        have hZlAinj : Function.Injective (algebraMap ↥Zl ↥A) := fun a b h =>
          hZlFinj (congrArg (Subtype.val : ↥A → ↥F) h)
        have habrnz : abr ≠ 0 := fun h0 =>
          (mem_nonZeroDivisors_iff_ne_zero.mp hbr) (hZlAinj (by rw [← habr, h0, map_zero]))
        refine ⟨⟨abt * ar, ⟨abr * at',
          mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero habrnz hat'nz)⟩⟩, ?_⟩
        apply Subtype.ext
        show (k : ↥F) * ((Subtype.val : ↥A → ↥F) (abr * at')) =
             (Subtype.val : ↥A → ↥F) (abt * ar)
        have hc1 : ((abr : ↥A) : ↥F) = algebraMap ↥Zl ↥F br :=
          (IsScalarTower.algebraMap_apply ↥Zl ↥A ↥F br).symm
        have hc2 : ((abt : ↥A) : ↥F) = algebraMap ↥Zl ↥F bt :=
          (IsScalarTower.algebraMap_apply ↥Zl ↥A ↥F bt).symm
        simp only [Subalgebra.coe_mul, hc1, hc2,
          show ((ar : ↥A) : ↥F) = (Polynomial.aeval (R := ↥Zl) s) r' from rfl,
          show ((at' : ↥A) : ↥F) = (Polynomial.aeval (R := ↥Zl) s) t' from rfl,
          hbrr, hbtt, hrt]
        rw [div_mul_eq_mul_div, div_eq_iff ht0]
        ring
    · intro a b hab
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact hιAKinj hab⟩

  haveI hMF : Module.Finite ↥A ↥(chartAlg N ℓ {s}) :=
    IsIntegralClosure.finite ↥A ↥K' ↥F ↥(chartAlg N ℓ {s})

  exact Algebra.FiniteType.trans hAFT (Module.Finite.finiteType ↥(chartAlg N ℓ {s}))

end
end S_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf (solution)

-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_specMap_iota
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/99a75e9f-1f6b-5c0a-b720-ed63903e0c97

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota.ModularCurve.IgusaScheme ModularCurve.DRLevel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme jq modularFunctionFieldFull transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull chartAlg mem_chartAlg_iff adjoin_le_chartAlg subset_chartAlg chartAlgFin chartAlgInf jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme ModularCurve"

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem moduleFinite_adjoin_chartAlg (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (s : ↥(modularFunctionFieldFull N)) (hs : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) s)
    (hFD_s : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)) :
    letI := (Subalgebra.inclusion (adjoin_le_chartAlg N ℓ ({s} : Set ↥(modularFunctionFieldFull N)))).toRingHom.toAlgebra
    Module.Finite ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s} : Set ↥(modularFunctionFieldFull N))) ↥(chartAlg N ℓ {s}) := by
  classical
  haveI hZlFR : IsFractionRing ↥(GaloisRep.ratLocalizedAt ℓ) ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  haveI hZlPID : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt ℓ) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  have hZlFinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) := by
    rw [IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N)]
    exact (algebraMap ℚ ↥(modularFunctionFieldFull N)).injective.comp (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
  set A := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s} : Set ↥(modularFunctionFieldFull N)) with hA
  set K' := IntermediateField.adjoin ℚ ({s} : Set ↥(modularFunctionFieldFull N)) with hK'def
  haveI hFD' : FiniteDimensional ↥K' ↥(modularFunctionFieldFull N) := hFD_s
  haveI hK'sep : Algebra.IsSeparable ↥K' ↥(modularFunctionFieldFull N) := inferInstance
  letI algAC : Algebra ↥A ↥(chartAlg N ℓ {s}) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg N ℓ {s})).toRingHom.toAlgebra
  haveI stAC : IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥(chartAlg N ℓ {s}) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  haveI stACF : IsScalarTower ↥A ↥(chartAlg N ℓ {s}) ↥(modularFunctionFieldFull N) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hIIC : IsIntegralClosure ↥(chartAlg N ℓ {s}) ↥A ↥(modularFunctionFieldFull N) := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, (mem_chartAlg_iff N ℓ).mpr hx⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (mem_chartAlg_iff N ℓ).mp y.2⟩ }
  have haevInj : Function.Injective (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) :=
    transcendental_iff_injective.mp hs
  have hmemA : ∀ p : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ), (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) p ∈ A := fun p => by
    rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let eA : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) ≃ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥A :=
    AlgEquiv.ofBijective ((Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s).codRestrict A hmemA)
      ⟨fun p q h => haevInj (Subtype.ext_iff.mp h),
       fun a => by
         have ha : (a : ↥(modularFunctionFieldFull N)) ∈ (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s).range := by
           rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA]; exact a.2
         obtain ⟨p, hp⟩ := ha; exact ⟨p, Subtype.ext hp⟩⟩
  haveI hANoeth : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial ↥(GaloisRep.ratLocalizedAt ℓ)) eA.toRingEquiv
  haveI hADom : IsDomain ↥A := inferInstance
  haveI hAUfm : UniqueFactorizationMonoid ↥A :=
    MulEquiv.uniqueFactorizationMonoid eA.toRingEquiv.toMulEquiv inferInstance
  haveI hAIIC : IsIntegrallyClosed ↥A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hAK' : ∀ a : ↥A, (a : ↥(modularFunctionFieldFull N)) ∈ K' := fun a =>
    Algebra.adjoin_induction
      (fun y hy => Set.mem_singleton_iff.mp hy ▸ IntermediateField.mem_adjoin_simple_self ℚ s)
      (fun r => K'.algebraMap_mem (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ r))
      (fun _ _ _ _ ha hb => add_mem ha hb)
      (fun _ _ _ _ ha hb => mul_mem ha hb)
      a.2
  let ιAK : ↥A →+* ↥K' := (Subalgebra.val A).toRingHom.codRestrict K'.toSubring (fun a => hAK' a)
  letI algAK : Algebra ↥A ↥K' := ιAK.toAlgebra
  haveI stAKF : IsScalarTower ↥A ↥K' ↥(modularFunctionFieldFull N) := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI stZlAK : IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥K' :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (Subtype.ext rfl)
  have hιAKinj : Function.Injective (algebraMap ↥A ↥K') := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : ↥K' → ↥(modularFunctionFieldFull N)) h)
  have haevNorm : ∀ p : Polynomial ℚ, ∃ b ∈ nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ),
      (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s)
        (IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p) =
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) b) * (Polynomial.aeval (R := ℚ) s) p := by
    intro p
    obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p
    refine ⟨b, hb, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap ℚ s
        (IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) p), hbp,
      Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (Polynomial ℚ) b,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N)]
  haveI hAFR : IsFractionRing ↥A ↥K' := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨a, ha⟩
      exact isUnit_iff_ne_zero.mpr fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp ha)
        (hιAKinj (h0.trans (map_zero _).symm))
    · intro k
      obtain ⟨r, t, hrt⟩ :=
        (IntermediateField.mem_adjoin_simple_iff ℚ (α := s) (k : ↥(modularFunctionFieldFull N))).mp (hK'def ▸ k.2)
      obtain ⟨br, hbr, hbrr⟩ := haevNorm r
      obtain ⟨bt, hbt, hbtt⟩ := haevNorm t
      set r' := IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) r
      set t' := IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt ℓ)) t
      by_cases ht0 : (Polynomial.aeval (R := ℚ) s) t = 0
      · refine ⟨⟨0, 1⟩, ?_⟩
        have hk0 : k = 0 := Subtype.ext (by
          show (k : ↥(modularFunctionFieldFull N)) = 0; rw [hrt, ht0, div_zero])
        simp [hk0]
      · set ar : ↥A := ⟨(Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) r', hmemA r'⟩
        set at' : ↥A := ⟨(Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t', hmemA t'⟩
        set abr : ↥A := algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A br with habr
        set abt : ↥A := algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A bt with habt
        have hat'nz : at' ≠ 0 := fun h0 => by
          have h0F : (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t' = 0 :=
            congrArg (Subtype.val : ↥A → ↥(modularFunctionFieldFull N)) h0
          rw [hbtt] at h0F
          rcases mul_eq_zero.mp h0F with hc | hc
          · exact (mem_nonZeroDivisors_iff_ne_zero.mp hbt) (hZlFinj (by rw [hc, map_zero]))
          · exact ht0 hc
        have hZlAinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A) := fun a b h =>
          hZlFinj (congrArg (Subtype.val : ↥A → ↥(modularFunctionFieldFull N)) h)
        have habrnz : abr ≠ 0 := fun h0 =>
          (mem_nonZeroDivisors_iff_ne_zero.mp hbr) (hZlAinj (by rw [← habr, h0, map_zero]))
        refine ⟨⟨abt * ar, ⟨abr * at',
          mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero habrnz hat'nz)⟩⟩, ?_⟩
        apply Subtype.ext
        show (k : ↥(modularFunctionFieldFull N)) * ((Subtype.val : ↥A → ↥(modularFunctionFieldFull N)) (abr * at')) =
             (Subtype.val : ↥A → ↥(modularFunctionFieldFull N)) (abt * ar)
        have hc1 : ((abr : ↥A) : ↥(modularFunctionFieldFull N)) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) br :=
          (IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥(modularFunctionFieldFull N) br).symm
        have hc2 : ((abt : ↥A) : ↥(modularFunctionFieldFull N)) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) bt :=
          (IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ↥A ↥(modularFunctionFieldFull N) bt).symm
        simp only [Subalgebra.coe_mul, hc1, hc2,
          show ((ar : ↥A) : ↥(modularFunctionFieldFull N)) = (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) r' from rfl,
          show ((at' : ↥A) : ↥(modularFunctionFieldFull N)) = (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s) t' from rfl,
          hbrr, hbtt, hrt]
        rw [div_mul_eq_mul_div, div_eq_iff ht0]
        ring
    · intro a b hab
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact hιAKinj hab⟩
  exact IsIntegralClosure.finite ↥A ↥K' ↥(modularFunctionFieldFull N) ↥(chartAlg N ℓ {s})

set_option synthInstance.maxHeartbeats 1600000 in
theorem transcendental_jFull (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) (jFull N : ↥(modularFunctionFieldFull N)) ∧
    Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) ((jFull N)⁻¹ : ↥(modularFunctionFieldFull N)) := by
  haveI hZlFR : IsFractionRing ↥(GaloisRep.ratLocalizedAt ℓ) ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  have htjℚ : Transcendental ℚ (jFull N : ↥(modularFunctionFieldFull N)) := by
    intro halg
    obtain ⟨p, hp, hev⟩ := halg
    refine transcendental_jq ⟨p, hp, ?_⟩
    have h0 : (algebraMap ↥(modularFunctionFieldFull N) (LaurentSeries ℚ))
        ((Polynomial.aeval (jFull N : ↥(modularFunctionFieldFull N))) p) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull N) (LaurentSeries ℚ)) (jFull N : ↥(modularFunctionFieldFull N)) = jq
          from coe_jFull N] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) (jFull N : ↥(modularFunctionFieldFull N)) :=
    fun h => htjℚ ((IsFractionRing.isAlgebraic_iff ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N)).mp h)
  refine ⟨htj, fun halg => ?_⟩
  have := halg.inv; rw [inv_inv] at this; exact htj this

theorem finiteDimensional_adjoin_jFull_inv (N : ℕ) [NeZero N] :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N) := by
  have hK : IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)) =
      IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr
        ((IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))).inv_mem
          (IntermediateField.mem_adjoin_simple_self ℚ (jFull N)))
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx; obtain rfl := hx
      have h1 := (IntermediateField.adjoin ℚ {(jFull N)⁻¹}).inv_mem
        (IntermediateField.mem_adjoin_simple_self ℚ ((jFull N)⁻¹ : ↥(modularFunctionFieldFull N)))
      rwa [inv_inv] at h1
  rw [hK]
  exact finiteDimensional_adjoin_jFull_modularFunctionFieldFull N

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem finite_and_finitePresentation_of_apply_eq {N N' : ℕ} [NeZero N] [NeZero N'] (ℓ : ℕ) [Fact ℓ.Prime]
    (s : ↥(modularFunctionFieldFull N)) (s' : ↥(modularFunctionFieldFull N'))
    (hs' : Transcendental ↥(GaloisRep.ratLocalizedAt ℓ) s')
    (hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({s'} : Set ↥(modularFunctionFieldFull N'))) ↥(modularFunctionFieldFull N'))
    (hNoeth : IsNoetherianRing ↥(chartAlg N ℓ {s}))
    (φ : ↥(chartAlg N ℓ {s}) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N' ℓ {s'}))
    (hφ : φ ⟨s, subset_chartAlg N ℓ _ rfl⟩ = ⟨s', subset_chartAlg N' ℓ _ rfl⟩) :
    φ.toRingHom.Finite ∧ φ.toRingHom.FinitePresentation := by
  classical

  let fA : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ {s}) :=
    Polynomial.aeval (⟨s, subset_chartAlg N ℓ _ rfl⟩ : ↥(chartAlg N ℓ {s}))
  let fM : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N' ℓ {s'}) :=
    Polynomial.aeval (⟨s', subset_chartAlg N' ℓ _ rfl⟩ : ↥(chartAlg N' ℓ {s'}))

  have hcomp : φ.comp fA = fM := by
    apply Polynomial.algHom_ext
    simp only [fA, fM, AlgHom.comp_apply, Polynomial.aeval_X, hφ]

  set A' := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({s'} : Set ↥(modularFunctionFieldFull N')) with hA'
  have hmemA' : ∀ p : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ),
      (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s') p ∈ A' := fun p => by
    rw [hA', Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let incl : ↥A' →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N' ℓ {s'}) :=
    Subalgebra.inclusion (adjoin_le_chartAlg N' ℓ ({s'} : Set ↥(modularFunctionFieldFull N')))
  let cr : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥A' :=
    (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s').codRestrict A' hmemA'
  have htow : fM = incl.comp cr := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply]
    apply Subtype.ext
    simp only [fM, incl, cr, Polynomial.aeval_X, Subalgebra.coe_inclusion, AlgHom.coe_codRestrict]
  have hincl : incl.toRingHom.Finite := moduleFinite_adjoin_chartAlg N' ℓ s' hs' hFD'
  have hcr : cr.toRingHom.Finite := by
    refine RingHom.Finite.of_surjective _ fun a => ?_
    have ha : (a : ↥(modularFunctionFieldFull N')) ∈
        (Polynomial.aeval (R := ↥(GaloisRep.ratLocalizedAt ℓ)) s').range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA']; exact a.2
    obtain ⟨p, hp⟩ := ha
    exact ⟨p, Subtype.ext hp⟩
  have hfM : fM.toRingHom.Finite := by
    have e : fM.toRingHom = incl.toRingHom.comp cr.toRingHom := by rw [htow]; rfl
    rw [e]
    exact hincl.comp hcr
  have hfin : φ.toRingHom.Finite := by
    refine RingHom.Finite.of_comp_finite (f := fA.toRingHom) ?_
    have e : φ.toRingHom.comp fA.toRingHom = fM.toRingHom := by rw [← hcomp]; rfl
    rw [e]
    exact hfM
  refine ⟨hfin, ?_⟩
  haveI := hNoeth
  exact RingHom.FinitePresentation.of_finiteType.mp hfin.finiteType

end ModularCurve.IgusaScheme

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

open ModularCurve.DRModelPackageLevel in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) :
    (IsFinite (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom))) ∧
    (IsFinite (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom))) := by
  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  obtain ⟨htj, htji⟩ := transcendental_jFull (N₀ * q) q
  obtain ⟨hFT0, hFTinf⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ q
  have hNoeth0 : IsNoetherianRing ↥(chartAlgFin N₀ q) :=
    Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt q) _
  have hNoethInf : IsNoetherianRing ↥(chartAlgInf N₀ q) :=
    Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt q) _

  have hj : 𝔓.iota0 (jChartFin N₀ q) = jChartFin (N₀ * q) q := by
    apply Subtype.ext; apply Subtype.ext
    rw [𝔓.iota0_spec (jChartFin N₀ q), coe_jChartFin, coe_jChartFin, coe_jFull, coe_jFull]
  have hjinv : 𝔓.iotaInf (jInvChartInf N₀ q) = jInvChartInf (N₀ * q) q := by
    apply Subtype.ext; apply Subtype.ext
    rw [𝔓.iotaInf_spec (jInvChartInf N₀ q), coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv,
      IntermediateField.coe_inv, coe_jFull, coe_jFull]
  obtain ⟨hf0, hfp0⟩ := finite_and_finitePresentation_of_apply_eq q (jFull N₀) (jFull (N₀ * q)) htj
    (finiteDimensional_adjoin_jFull_modularFunctionFieldFull (N₀ * q)) hNoeth0 𝔓.iota0 hj
  obtain ⟨hfi, hfpi⟩ := finite_and_finitePresentation_of_apply_eq q ((jFull N₀)⁻¹) ((jFull (N₀ * q))⁻¹) htji
    (finiteDimensional_adjoin_jFull_inv (N₀ * q)) hNoethInf 𝔓.iotaInf hjinv
  exact ⟨⟨(IsFinite.SpecMap_iff _).mpr hf0, HasRingHomProperty.Spec_iff.mpr hfp0⟩,
    ⟨(IsFinite.SpecMap_iff _).mpr hfi, HasRingHomProperty.Spec_iff.mpr hfpi⟩⟩

end

end S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota (solution)

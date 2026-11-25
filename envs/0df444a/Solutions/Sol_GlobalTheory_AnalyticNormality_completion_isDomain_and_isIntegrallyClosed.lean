-- Prove2me | solution 1 for GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:11.694988+00:00
-- url     : https://prove2.me/submissions/15880a35-a57f-4f14-9ad1-06ae5b418961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobsonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsConductorAdicCompletionEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosed
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat
import Theorems.Thm_GlobalTheory_T_adic_completion_reduced_of_jacobson
import Theorems.Thm_GlobalTheory_T_associated_prime_localization_dvr
import Theorems.Thm_GlobalTheory_T_exists_conductor_adicCompletion_essFiniteType
import Theorems.Thm_GlobalTheory_T_isDomain_of_isIntegrallyClosed_of_isReduced_local
import Theorems.Thm_GlobalTheory_T_isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
import Theorems.Thm_GlobalTheory_T_isNoetherianRing_adicCompletion_of_noetherian
import Theorems.Thm_GlobalTheory_T_nonempty_adicCompletion_quotient_ringEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticNormality
open IsLocalRing
namespace GlobalTheory.AnalyticNormality
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
  have hquot := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
  have hengine := GlobalTheory.T.associated_prime_localization_dvr
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
  have hred := GlobalTheory.T.adic_completion_reduced_of_jacobson
  have hcond := GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩
end GlobalTheory.AnalyticNormality

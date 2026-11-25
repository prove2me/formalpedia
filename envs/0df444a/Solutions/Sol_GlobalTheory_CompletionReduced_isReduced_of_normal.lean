-- Prove2me | solution 1 for GlobalTheory.CompletionReduced.isReduced_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:10.811449+00:00
-- url     : https://prove2.me/submissions/95589408-4eb0-40f1-a4f3-e65127663846

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
import Theorems.Thm_GlobalTheory_CompletionReduced_map_le_jacobson_of_comap_isMaximal
import Theorems.Thm_GlobalTheory_CompletionReduced_exists_lt_of_add_one_le
import Theorems.Thm_GlobalTheory_T_associated_prime_localization_dvr
import Theorems.Thm_GlobalTheory_T_isNoetherianRing_adicCompletion_of_noetherian
import Theorems.Thm_GlobalTheory_T_isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes
import Theorems.Thm_GlobalTheory_T_nonempty_adicCompletion_quotient_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionReduced
namespace GlobalTheory.CompletionReduced
theorem _root_.solution (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP
  exact h1
end GlobalTheory.CompletionReduced

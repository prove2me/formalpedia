-- Prove2me | solution 1 for GlobalTheory.nonempty_algHom_of_smooth_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:37.554234+00:00
-- url     : https://prove2.me/submissions/5d8e0ce4-5b24-4d22-b454-0cde4e9774f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_nonempty_algHom_of_etale_of_isSepClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]
namespace GlobalTheory
theorem _root_.solution [IsSepClosed K] [Algebra.Smooth R A] (p : Ideal A)
    [p.IsPrime] (hp : p.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  have : Infinite K := by
    by_contra hK
    rw [not_infinite_iff_finite] at hK
    have := IsSepClosed.isAlgClosed_of_perfectField K
    exact not_finite K
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := p)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let p' : PrimeSpectrum S := ⟨p.map (algebraMap A S),
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› hdisj⟩
  have hp' : p'.asIdeal.comap (algebraMap R S) = RingHom.ker (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R A S, ← Ideal.comap_comap, ← hp]
    exact congrArg _ (IsLocalization.comap_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj)
  have hopen := (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := P) (S := S)).isOpen_range
  obtain ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hh, hsub⟩ := PrimeSpectrum.isBasis_basic_opens
    |>.exists_subset_of_mem_open (Set.mem_range_self p') hopen
  obtain ⟨b, hb⟩ : ∃ b : Fin n → K, MvPolynomial.aeval b h ≠ 0 := by
    by_contra hc
    push Not at hc
    have h₀ : h.map (algebraMap R K) = 0 :=
      MvPolynomial.funext fun b => by rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, hc, map_zero]
    apply hh
    rw [h.as_sum]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [MvPolynomial.monomial_eq]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap P S (algebraMap R P _) ∈ p'.asIdeal
    rw [← IsScalarTower.algebraMap_apply, ← Ideal.mem_comap, hp', RingHom.mem_ker,
      ← MvPolynomial.coeff_map, h₀, MvPolynomial.coeff_zero]
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  have : IsScalarTower R P K :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  obtain ⟨q, hq⟩ := hsub (a := ⟨RingHom.ker (algebraMap P K), RingHom.ker_isPrime _⟩) hb
  obtain ⟨ψ⟩ := nonempty_algHom_of_etale_of_isSepClosed (R := P) (K := K) q.asIdeal
    congr($(hq).asIdeal)
  exact ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩
end GlobalTheory

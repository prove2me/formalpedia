-- Prove2me | solution 1 for GlobalTheory.Chow.isPrincipal_of_forall_C_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:52.772806+00:00
-- url     : https://prove2.me/submissions/f2018bab-dc4d-4a71-9632-30677d11a2db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
namespace GlobalTheory.Chow
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (E : Ideal (Polynomial R)) [hE : E.IsPrime]
    (h : ∀ r, Polynomial.C r ∈ E → r = 0) : E.IsPrincipal := by
  by_cases h0 : E = ⊥
  · rw [h0]; exact bot_isPrincipal
  obtain ⟨g, hg, hgp⟩ := hE.exists_mem_prime_of_ne_bot h0
  have hP : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).2 hgp
  have hle : Ideal.span {g} ≤ E := (Ideal.span_singleton_le_iff_mem _).2 hg
  let F := FractionRing R
  let M : Submonoid (Polynomial R) := (nonZeroDivisors R).map Polynomial.C
  have hd : Disjoint (M : Set (Polynomial R)) E := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨r, hr, rfl⟩ hrE
    exact nonZeroDivisors.ne_zero hr (h r hrE)
  have hd' : Disjoint (M : Set (Polynomial R)) (Ideal.span {g} : Ideal _) := hd.mono_right hle
  have h1 := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial F) E hE hd
  have h2 := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial F) _ hP hd'
  have h3 : (Ideal.span {g}).map (algebraMap (Polynomial R) (Polynomial F)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R F)).2 hgp.ne_zero
  have h4 := (IsPrime.to_maximal_ideal h3).eq_of_le h1.ne_top (Ideal.map_mono hle)
  refine ⟨g, ?_⟩
  rw [← IsLocalization.under_map_of_isPrime_disjoint M (Polynomial F) hE hd, ← h4,
    IsLocalization.under_map_of_isPrime_disjoint M (Polynomial F) hP hd']
end GlobalTheory.Chow

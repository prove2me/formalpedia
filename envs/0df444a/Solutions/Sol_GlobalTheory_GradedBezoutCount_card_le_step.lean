-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.card_le_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:21:35.211585+00:00
-- url     : https://prove2.me/submissions/502fa5df-9b33-4573-9e31-5d00b4830261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
import Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_minimalPrime_le
import Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_GradedBezout_sum_gradedQuotDeg_le
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GradedBezoutCount
open GradedBezout
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] {𝒜 : ℕ → Submodule K T}
  [GradedAlgebra 𝒜]
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
open Classical
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution {n : ℕ} (φ : Fin n → (T →ₐ[K] K)) {P : Ideal T} [P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 2 : ℕ)) {f : T} {b : ℕ}
    (hf : f ∈ 𝒜 b) (hfP : f ∉ P) (h0 : ∀ j, φ j f = 0) {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ Q : Ideal T, Q.IsPrime → Q.IsHomogeneous 𝒜 → ringKrullDim (T ⧸ Q) = (r + 1 : ℕ) →
      ((Finset.univ.filter fun j => ∀ y ∈ Q, φ j y = 0).card : ℚ) ≤ B * gradedQuotDeg 𝒜 r Q) :
    ((Finset.univ.filter fun j => ∀ y ∈ P, φ j y = 0).card : ℚ) ≤
      B * (b * gradedQuotDeg 𝒜 (r + 1) P) := by
  haveI := isNoetherianRing hfin
  have hfinite := (P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have h1 : (Finset.univ.filter fun j => ∀ y ∈ P, φ j y = 0) ⊆
      hfinite.toFinset.biUnion fun Q => Finset.univ.filter fun j => ∀ y ∈ Q, φ j y = 0 := by
    intro j hj
    obtain ⟨Q, hQ, hle⟩ := exists_minimalPrime_le (φ j) (Finset.mem_filter.1 hj).2 (h0 j)
    exact Finset.mem_biUnion.2 ⟨Q, hfinite.mem_toFinset.2 hQ,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hle⟩⟩
  have h2 := (Finset.card_le_card h1).trans Finset.card_biUnion_le
  have h3 := sum_gradedQuotDeg_le hx hfin hI hr hf hfP hfinite.toFinset
    fun Q hQ => hfinite.mem_toFinset.1 hQ
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h3 hB)
  rw [Finset.mul_sum]
  refine ((Nat.cast_le (α := ℚ)).2 h2).trans ?_
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun Q hQ => ?_
  rw [hfinite.mem_toFinset] at hQ
  exact h Q hQ.1.1 (isHomogeneous_of_mem_minimalPrimes _ (isHomogeneous_sup_span hI hf) hQ)
    (ringKrullDim_quotient_of_mem_minimalPrimes_sup (r := r + 1) hfin hr hfP hQ)
end GlobalTheory.GradedBezoutCount

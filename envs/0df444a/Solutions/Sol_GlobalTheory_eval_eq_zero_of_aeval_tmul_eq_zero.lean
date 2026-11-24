-- Prove2me | solution 1 for GlobalTheory.eval_eq_zero_of_aeval_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:20.32884+00:00
-- url     : https://prove2.me/submissions/a64bed1c-4454-4b54-a627-494c5699c2f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
import Theorems.Thm_GlobalTheory_sum_mul_eq_zero_of_forall_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F K J ι : Type} [Field F] [Field K] [Algebra F K]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (w : ∀ i, J → A i) (v : J → K)
    (h : ∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0)
    (G : MvPolynomial J K) (d : ℕ) (hG : G.IsHomogeneous d)
    (h0 : ∀ i, MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) G = 0) :
    MvPolynomial.eval v G = 0 := by
  rw [MvPolynomial.eval_eq]
  refine sum_mul_eq_zero_of_forall_dual (F := F) _ _ _ fun l => ?_
  have key : ∀ (B : Type) [CommRing B] [Algebra F B] (u : J → B),
      MvPolynomial.aeval u (∑ s ∈ G.support, MvPolynomial.monomial s (l (G.coeff s))) =
        ∑ s ∈ G.support, l (G.coeff s) • ∏ j ∈ s.support, u j ^ s j := fun B _ _ u => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.aeval_monomial, Algebra.smul_def]
    rfl
  rw [← key]
  refine h _ d (MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_) fun i => ?_
  · refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hG (MvPolynomial.mem_support_iff.mp hs)
  · rw [key]
    have h1 := congrArg ((TensorProduct.lid F (A i)).toLinearMap ∘ₗ l.rTensor (A i)) (h0 i)
    rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h2 : algebraMap K (K ⊗[F] A i) (G.coeff s) * ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
        = G.coeff s ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
      have : ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
          = (1 : K) ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
        simp only [← Algebra.TensorProduct.includeRight_apply (R := F) (A := K), map_prod, map_pow]
      rw [this]
      simp
    rw [h2]
    simp
end GlobalTheory

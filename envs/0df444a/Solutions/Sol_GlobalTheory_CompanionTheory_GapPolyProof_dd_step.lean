-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dd_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:11.864831+00:00
-- url     : https://prove2.me/submissions/7d04e60d-856d-4b52-a79d-2f5f3608a9d3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (ψ : E →ₗ[ℂ] ℂ) :
    X * dd n v ψ - dd n v (ψ ∘ₗ T) = C (ψ x) * (S.map (fun t => X - C t)).prod := by
  have key : X * dd n v ψ = (∑ j ∈ Finset.range (n + 1), C (ψ (v (j + 1))) * X ^ (n - j)) + C (ψ x) * X ^ (n + 1) := by
    have h1 := Finset.sum_range_succ (fun j => (C (ψ (v j)) : ℂ[X]) * X ^ (n + 1 - j)) (n + 1)
    have h2 := Finset.sum_range_succ' (fun j => (C (ψ (v j)) : ℂ[X]) * X ^ (n + 1 - j)) (n + 1)
    rw [h1] at h2
    simp only [hn, map_zero, zero_mul, add_zero, h0, Nat.sub_zero, Nat.add_sub_add_right] at h2
    rw [← h2, dd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : n + 1 - j = (n - j) + 1 := by have := Finset.mem_range.1 hj; omega
    rw [this, pow_succ]; ring
  have hG : (S.map (fun t => X - C t)).prod =
      (∑ j ∈ Finset.range (n + 1), C (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) * X ^ (n - j)) + X ^ (n + 1) := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hS, Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Nat.add_sub_add_right, map_mul, map_pow, map_neg, map_one]
      ring
    · simp [Multiset.esymm]
  rw [key, hG, dd, mul_add, Finset.mul_sum, add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := congrArg ψ (hrec j (by have := Finset.mem_range.1 hj; omega))
  simp only [map_sub, map_smul, smul_eq_mul] at h
  have h' : ψ (v (j + 1)) = ψ (T (v j)) + (-1 : ℂ) ^ (j + 1) * S.esymm (j + 1) * ψ x := by
    rw [← h]; ring
  rw [h']
  simp only [LinearMap.comp_apply, map_add, map_mul]
  ring
end GlobalTheory.CompanionTheory.GapPolyProof

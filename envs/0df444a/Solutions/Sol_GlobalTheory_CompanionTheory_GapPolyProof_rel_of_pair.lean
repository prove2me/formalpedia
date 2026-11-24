-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.rel_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:15.820814+00:00
-- url     : https://prove2.me/submissions/e150e98d-9b16-41d8-b2f0-018f0a49dd65

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
theorem _root_.solution (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (q c d : ℂ) (v : ℕ → E)
    (φ : E →ₗ[ℂ] ℂ)
    (hp : ∀ j ≤ n, d * φ (v j) = (q ^ (n + 1 - j) - 1) * (((-1 : ℂ) ^ j) * S.esymm j) * c) :
    C d * (X * dd n v φ) =
      C c * (((S.map (fun t => X - C t)).prod).comp (C q * X) - (S.map (fun t => X - C t)).prod) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hS, ← coe_compRingHom_apply, map_sum, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ, dd, Finset.mul_sum, Finset.mul_sum]
  simp only [coe_compRingHom_apply]
  have hlast : ((-1 : ℂ[X]) ^ (n + 1) * (C (S.esymm (n + 1)) * X ^ (n + 1 - (n + 1)))).comp (C q * X) -
      (-1 : ℂ[X]) ^ (n + 1) * (C (S.esymm (n + 1)) * X ^ (n + 1 - (n + 1))) = 0 := by
    simp
  rw [hlast, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
  have e : n + 1 - j = (n - j) + 1 := by omega
  have h := congrArg (C : ℂ → ℂ[X]) (hp j hj')
  simp only [map_mul, map_sub, map_pow, map_neg, map_one] at h
  simp only [mul_comp, pow_comp, neg_comp, one_comp, C_comp, X_comp]
  rw [e] at h ⊢
  rw [mul_pow]
  calc C d * (X * (C (φ (v j)) * X ^ (n - j))) = (C d * C (φ (v j))) * X ^ (n - j + 1) := by ring
    _ = _ := by rw [h]; ring
end GlobalTheory.CompanionTheory.GapPolyProof

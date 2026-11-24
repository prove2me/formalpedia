-- Prove2me | solution 1 for GlobalTheory.RationalValueRealScalar.exists_rat_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:55.285965+00:00
-- url     : https://prove2.me/submissions/3a6d0546-721d-4573-b485-2f57aa933f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRatBilinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalValueRealScalar
namespace GlobalTheory.RationalValueRealScalar
theorem _root_.solution {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring
end GlobalTheory.RationalValueRealScalar

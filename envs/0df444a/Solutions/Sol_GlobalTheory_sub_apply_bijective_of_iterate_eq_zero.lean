-- Prove2me | solution 1 for GlobalTheory.sub_apply_bijective_of_iterate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:29.703119+00:00
-- url     : https://prove2.me/submissions/c52e6b07-d164-412e-a9a6-1a9ba47d6461

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {M : Type} [AddCommGroup M] (L : M →+ M) (K : ℕ)
    (hK : ∀ z, (⇑L)^[K] z = 0) : Function.Bijective (fun z => z - L z) := by
  constructor
  · intro a b hab
    have hab' : a - L a = b - L b := hab
    have hfix : L (a - b) = a - b := by
      rw [map_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at hab'
      exact hab'.symm
    have h1 : ∀ m, (⇑L)^[m] (a - b) = a - b := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
    exact sub_eq_zero.mp ((h1 K).symm.trans (hK _))
  · intro c
    refine ⟨∑ k ∈ Finset.range K, (⇑L)^[k] c, ?_⟩
    show (∑ k ∈ Finset.range K, (⇑L)^[k] c) - L (∑ k ∈ Finset.range K, (⇑L)^[k] c) = c
    rw [map_sum]
    have hs : ∀ k, L ((⇑L)^[k] c) = (⇑L)^[k + 1] c := fun k =>
      (Function.iterate_succ_apply' (⇑L) k c).symm
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', hK, sub_zero]
    rfl
end GlobalTheory

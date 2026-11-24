-- Prove2me | solution 1 for GlobalTheory.isUnit_aeval_of_forall_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:28.86898+00:00
-- url     : https://prove2.me/submissions/9015373c-6631-45aa-b2db-3327b65d1c4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _
end GlobalTheory

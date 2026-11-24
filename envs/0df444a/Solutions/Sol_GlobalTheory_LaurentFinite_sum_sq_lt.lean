-- Prove2me | solution 1 for GlobalTheory.LaurentFinite.sum_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:43.817421+00:00
-- url     : https://prove2.me/submissions/7980f6d6-ed48-464f-8e7f-79654f51c4de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
import Theorems.Thm_GlobalTheory_LaurentFinite_pointwise_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra
namespace GlobalTheory.LaurentFinite
theorem _root_.solution {m : ℕ} (j : ℤ) (ν κ : Fin m → ℤ) (hj : 2 ≤ j) (hν : ∀ i, |ν i| ≠ j - 1)
    (hκ : ∀ i, |κ i| ≤ 1) (hs : ∑ i, |κ i| ≤ ∑ i, |cut j (ν i)|)
    (hne : κ ≠ fun i => cut j (ν i)) :
    ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 < ∑ i, ν i ^ 2 := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
  have h1 : ∑ i, (2 * j - 2) * (|cut j (ν i)| - |κ i|)
      < ∑ i, (ν i ^ 2 - (ν i - cut j (ν i) + κ i) ^ 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases h : κ i = cut j (ν i)
      · rw [h]; simp
      · exact (pointwise_lt j _ _ hj (hν i) (hκ i) h).le
    · exact ⟨i0, Finset.mem_univ _, pointwise_lt j _ _ hj (hν i0) (hκ i0) hi0⟩
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  have : 0 ≤ (2 * j - 2) * (∑ i, |cut j (ν i)| - ∑ i, |κ i|) :=
    mul_nonneg (by omega) (by omega)
  omega
end GlobalTheory.LaurentFinite

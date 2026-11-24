-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.exists_last_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:51.639809+00:00
-- url     : https://prove2.me/submissions/87500249-46a8-4949-940f-ea9528b2f6f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (n : ℕ) (hn : 1 < t n) :
    ∃ k, 1 < t k ∧ (∀ a, t a ≤ t k) ∧ ∀ a, k < a → t a < t k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  have hnM : n ∈ range M := by
    rw [mem_range]
    by_contra h
    exact absurd (hM n (not_lt.1 h)) (not_lt.2 hn.le)
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (range M) t ⟨n, hnM⟩
  obtain ⟨k, hk, hlast⟩ := Finset.exists_max_image ((range M).filter fun a => t a = t k₀) id
    ⟨k₀, by simp [mem_range.1 hk₀]⟩
  rw [mem_filter] at hk
  have h1 : 1 < t k := by rw [hk.2]; exact hn.trans_le (hmax n hnM)
  have hall : ∀ a, t a ≤ t k := fun a => by
    by_cases ha : a < M
    · rw [hk.2]; exact hmax a (mem_range.2 ha)
    · exact ((hM a (not_lt.1 ha)).trans h1).le
  refine ⟨k, h1, hall, fun a hka => ?_⟩
  by_cases ha : a < M
  · refine lt_of_le_of_ne (hall a) fun h => ?_
    have := hlast a (by rw [mem_filter]; exact ⟨mem_range.2 ha, h.trans hk.2⟩)
    exact absurd hka (not_lt.2 this)
  · exact (hM a (not_lt.1 ha)).trans h1
end GlobalTheory.NearlyPrimitive

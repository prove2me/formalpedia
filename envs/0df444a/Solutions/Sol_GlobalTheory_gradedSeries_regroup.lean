-- Prove2me | solution 1 for GlobalTheory.gradedSeries_regroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:28.408249+00:00
-- url     : https://prove2.me/submissions/94735f4d-c654-4e8d-a84e-673a1d6c55d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by
  have h1 := hs.tsum_fiberwise deg
  have e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) =
      (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i) := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    rintro ⟨i, hi⟩
    simp only [mem_preimage, mem_singleton_iff] at hi
    simp [hi]
  rw [e]
  exact h1
end GlobalTheory

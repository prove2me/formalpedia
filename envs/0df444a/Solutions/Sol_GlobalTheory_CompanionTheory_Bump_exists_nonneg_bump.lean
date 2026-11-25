-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:21.907145+00:00
-- url     : https://prove2.me/submissions/6a8e9917-43b5-463b-bb0b-84d0802dcda2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNonnegBump

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bump
namespace GlobalTheory.CompanionTheory.Bump
theorem _root_.solution :
    ∀ {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (x : X) (N : Set X),
      N ∈ 𝓝 x → ∃ φ : X → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ 0 ≤ φ ∧ φ x ≠ 0 ∧
        Function.support φ ⊆ N := by
  intro X _ _ _ x N hN
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.mpr hN
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (s := {x}) (t := (interior N)ᶜ) isCompact_singleton isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h hx))
  refine ⟨f, f.continuous, hfc, fun y => (hfI y).1, ?_, ?_⟩
  · have h1 : f x = 1 := hf1 (Set.mem_singleton x)
    rw [h1]
    exact one_ne_zero
  · intro y hy
    by_contra hyN
    exact hy (hf0 (fun hi => hyN (interior_subset hi)))
end GlobalTheory.CompanionTheory.Bump

-- Prove2me | solution 1 for InvariantSubspaceProblem.nonseparable_exists_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:06:34.236348+00:00
-- url     : https://prove2.me/submissions/8c66c98f-08a9-4dd6-9e1c-5c7b4ae04fd1

import Mathlib
import Definitions.Def_InvariantSubspaceProblem_Defs

open InvariantSubspaceProblem in
theorem solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hE : ¬ TopologicalSpace.SeparableSpace E) (T : E →L[ℂ] E) :
    HasNontrivialClosedInvariantSubspace T := by
  have hx : ∃ x : E, x ≠ 0 := by
    by_contra h
    push_neg at h
    have : Subsingleton E := ⟨fun a b => by rw [h a, h b]⟩
    exact hE inferInstance
  obtain ⟨x, hx0⟩ := hx
  set V : Submodule ℂ E := Submodule.span ℂ (Set.range fun n : ℕ => (T ^ n) x) with hV
  refine ⟨V.topologicalClosure, V.isClosed_topologicalClosure, ?_, ?_, ?_⟩
  · intro h
    have : x ∈ V.topologicalClosure := V.le_topologicalClosure
      (Submodule.subset_span ⟨0, by simp⟩)
    rw [h] at this
    exact hx0 ((Submodule.mem_bot ℂ).1 this)
  · intro h
    apply hE
    have hs : TopologicalSpace.IsSeparable (V.topologicalClosure : Set E) := by
      rw [Submodule.topologicalClosure_coe]
      exact ((Set.countable_range _).isSeparable.span (R := ℂ)).closure
    rw [h] at hs
    exact TopologicalSpace.isSeparable_univ_iff.1 (by simpa using hs)
  · intro y hy
    have hmaps : Set.MapsTo T (V : Set E) (V : Set E) := by
      intro z hz
      have : V ≤ V.comap (T : E →ₗ[ℂ] E) := by
        rw [hV, Submodule.span_le]
        rintro _ ⟨n, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
        have : T ((T ^ n) x) = (T ^ (n + 1)) x := by rw [pow_succ']; rfl
        rw [this]
        exact Submodule.subset_span ⟨n + 1, rfl⟩
      exact this hz
    have hy' : y ∈ closure (V : Set E) := by rwa [← Submodule.topologicalClosure_coe]
    have := map_mem_closure T.continuous hy' hmaps
    rwa [← Submodule.topologicalClosure_coe] at this

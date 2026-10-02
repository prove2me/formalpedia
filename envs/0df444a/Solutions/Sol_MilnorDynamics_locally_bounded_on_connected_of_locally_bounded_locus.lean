-- Prove2me | solution 1 for MilnorDynamics.locally_bounded_on_connected_of_locally_bounded_locus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T00:28:22.907337+00:00
-- url     : https://prove2.me/submissions/472b0489-9b49-483e-a2e4-5f7ecf479fc1

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Local boundedness at every point of an open set gives a single bound on every compact
subset of that set.  Both witnesses (`V` and `M`) are produced by a *single* `choose` from one
source hypothesis, so `V z` and `M z` come from the same `hloc` instance and no second
Skolemization is needed. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U) (f : ℕ → ℂ → ℂ)
    (hloc : ∀ z₀ ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ n, ∀ z ∈ V, ‖f n z‖ ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ M' : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M' := by
  intro K hKU hK
  -- the empty compact set is trivial, and the membership proof is consumed by `rw`
  rcases K.eq_empty_or_nonempty with hKe | ⟨z₀, hz₀⟩
  · refine ⟨0, ?_⟩
    intro n w hw
    rw [hKe] at hw
    exact absurd hw (by simp)
  -- ONE `choose` over a four-witness existential: `V`, its openness, the two memberships,
  -- and finally `M` with its uniform bound.
  have hVex : ∀ z : K, ∃ V : Set ℂ, IsOpen V ∧ (z : ℂ) ∈ V ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ n, ∀ w ∈ V, ‖f n w‖ ≤ M := by
    intro z
    obtain ⟨V, hV, hzV, hVU, M, hM⟩ := hloc (z : ℂ) (hKU z.2)
    exact ⟨V, hV, hzV, hVU, M, hM⟩
  choose V hVo hzV hVU M hMb using hVex
  -- the open cover of `K` and its finite subcover
  have hsub : K ⊆ ⋃ z : K, V z :=
    fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo hsub
  -- `z₀ ∈ K` and `z₀` is covered force `t` to be nonempty, so the fold below is well defined
  have htne : t.Nonempty := by
    obtain ⟨j, hj, _⟩ := mem_iUnion₂.1 (ht hz₀)
    exact ⟨j, hj⟩
  refine ⟨t.sup' htne M, fun n z hz => ?_⟩
  obtain ⟨j, hj, hjmem⟩ := mem_iUnion₂.1 (ht hz)
  exact (hMb j n z hjmem).trans (Finset.le_sup' (s := t) (f := M) hj)

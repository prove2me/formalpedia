-- Prove2me | solution 1 for MetricGenerators.IsometryExt.initial_candidates
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:19.930551+00:00
-- url     : https://prove2.me/submissions/ca2616b4-7702-4b90-a5da-65a0dbd23e51

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsMetricGenerator H T) (f : ↥T → VG) (hf : IsIsometryOn H G T f) :
    (∀ u v : VH, u ≠ v → Disjoint (cand H G T f 0 u) (cand H G T f 0 v)) ∧
    (∀ t : ↥T, cand H G T f 0 t = {f t}) := by
  have h0 : ∀ u, cand H G T f 0 u = initialCandidates H G T f u := fun u => rfl
  constructor
  · intro u v huv
    rw [Set.disjoint_left]
    intro x hxu hxv
    rw [h0] at hxu hxv
    obtain ⟨t, ht, hd⟩ := hT u v huv
    apply hd
    have h1 := hxu ⟨t, ht⟩
    have h2 := hxv ⟨t, ht⟩
    exact h1.symm.trans h2
  · intro t
    ext x
    rw [h0]
    simp only [initialCandidates, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have h3 : G.dist (f t) x = 0 := by rw [h t]; exact SimpleGraph.dist_self
      exact (hG.dist_eq_zero_iff.mp h3).symm
    · rintro rfl s
      exact hf s t

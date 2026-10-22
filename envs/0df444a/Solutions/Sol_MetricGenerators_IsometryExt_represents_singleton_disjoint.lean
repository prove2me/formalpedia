-- Prove2me | solution 1 for MetricGenerators.IsometryExt.represents_singleton_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:21.366901+00:00
-- url     : https://prove2.me/submissions/cc80d491-6e90-4837-9621-17b3b6acf7ab

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsMetricGenerator H T) (f : ↥T → VG) (hf : IsIsometryOn H G T f)
    (C : VH → Set VG) (hC : Represents H G T f C) :
    (∀ t : ↥T, C t = {f t}) ∧ (∀ u v : VH, u ≠ v → Disjoint (C u) (C v)) := by
  obtain ⟨hne, hi, hii⟩ := hC
  constructor
  · intro t
    have key : ∀ x ∈ C t, x = f t := by
      intro x hx
      have h3 : G.dist (f t) x = 0 := by rw [hi t t x hx]; exact SimpleGraph.dist_self
      exact (hG.dist_eq_zero_iff.mp h3).symm
    obtain ⟨x0, hx0⟩ := hne t
    ext x
    constructor
    · intro hx; exact key x hx
    · intro hx
      rw [Set.mem_singleton_iff.mp hx, ← key x0 hx0]
      exact hx0
  · intro u v huv
    rw [Set.disjoint_left]
    intro x hxu hxv
    obtain ⟨t, ht, hd⟩ := hT u v huv
    apply hd
    have h1 := hi ⟨t, ht⟩ u x hxu
    have h2 := hi ⟨t, ht⟩ v x hxv
    exact h1.symm.trans h2

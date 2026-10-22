-- Prove2me | solution 1 for MetricGenerators.IsometryExt.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:06:20.240979+00:00
-- url     : https://prove2.me/submissions/fbef614f-e1ad-4e8e-8598-3eaebb5abe88

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T) (f : ↥T → VG)
    (hf : IsIsometryOn H G T f) (C : VH → Set VG) (hC : Represents H G T f C) :
    ∀ u v : VH, ∀ x ∈ C u,
      (∃ y ∈ C v, G.dist x y = H.dist u v) ∧ (∀ y ∈ C v, H.dist u v ≤ G.dist x y) := by
  obtain ⟨hne, hi, hii⟩ := hC
  -- lower bound
  have lower : ∀ u v : VH, ∀ x ∈ C u, ∀ y ∈ C v, H.dist u v ≤ G.dist x y := by
    intro u v x hx y hy
    obtain ⟨s, hs, h⟩ := hT u v
    have h1 := hi ⟨s, hs⟩ u x hx
    have h2 := hi ⟨s, hs⟩ v y hy
    have hxy : G.dist (f ⟨s, hs⟩) x ≤ G.dist (f ⟨s, hs⟩) y + G.dist y x := hG.dist_triangle
    have hyx : G.dist (f ⟨s, hs⟩) y ≤ G.dist (f ⟨s, hs⟩) x + G.dist x y := hG.dist_triangle
    have c1 : H.dist u v = H.dist v u := SimpleGraph.dist_comm
    have c2 : G.dist x y = G.dist y x := SimpleGraph.dist_comm
    rcases h with h | h
    · -- dist s u = dist s v + dist v u
      simp only [] at h1 h2
      omega
    · simp only [] at h1 h2
      omega
  -- upper bound by induction on the distance
  have upper : ∀ n : ℕ, ∀ u v : VH, H.dist u v ≤ n → ∀ x ∈ C u, ∃ y ∈ C v, G.dist x y ≤ n := by
    intro n
    induction n with
    | zero =>
      intro u v huv x hx
      have : u = v := hH.dist_eq_zero_iff.mp (by omega)
      subst this
      exact ⟨x, hx, by simp⟩
    | succ n ih =>
      intro u v huv x hx
      by_cases heq : u = v
      · subst heq
        exact ⟨x, hx, by simp⟩
      · obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
        cases p with
        | nil => exact absurd rfl heq
        | cons hadj p' =>
          rename_i u'
          have hlen : p'.length ≤ n := by
            have : (SimpleGraph.Walk.cons hadj p').length = p'.length + 1 := rfl
            omega
          have hd' : H.dist u' v ≤ n := le_trans (SimpleGraph.dist_le p') hlen
          obtain ⟨x', hx', hxx'⟩ := hii u u' hadj x hx
          obtain ⟨y, hy, hyd⟩ := ih u' v hd' x' hx'
          refine ⟨y, hy, ?_⟩
          have h1 : G.dist x y ≤ G.dist x x' + G.dist x' y := hG.dist_triangle
          have h2 : G.dist x x' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxx'
          omega
  intro u v x hx
  obtain ⟨y, hy, hyd⟩ := upper (H.dist u v) u v le_rfl x hx
  refine ⟨⟨y, hy, ?_⟩, fun y' hy' => lower u v x hx y' hy'⟩
  have := lower u v x hx y hy
  omega

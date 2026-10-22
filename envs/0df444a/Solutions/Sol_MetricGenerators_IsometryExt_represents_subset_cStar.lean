-- Prove2me | solution 1 for MetricGenerators.IsometryExt.represents_subset_cStar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:06:16.455552+00:00
-- url     : https://prove2.me/submissions/e10ca611-0922-4c66-bd26-13f60adc96d3

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem strong_to_metric {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (S : Finset V) (hS : IsStrongMetricGenerator G S) :
    IsMetricGenerator G S := by
  intro x y hxy
  obtain ⟨s, hs, h⟩ := hS x y
  refine ⟨s, hs, ?_⟩
  have hpos : 0 < G.dist y x := hG.pos_dist_of_ne (Ne.symm hxy)
  have hpos' : 0 < G.dist x y := hG.pos_dist_of_ne hxy
  intro heq
  rcases h with h | h <;> omega

theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T) (f : ↥T → VG)
    (hf : IsIsometryOn H G T f) (C : VH → Set VG) (hC : Represents H G T f C) :
    ∀ u : VH, C u ⊆ cStar H G T f u := by
  have hT' := strong_to_metric H hH T hT
  obtain ⟨hne, hi, hii⟩ := hC
  have c1 : ∀ i, candSet H G T f (i + 1) =
      {x | x ∈ candSet H G T f i ∧ ∀ u v : VH, x ∈ cand H G T f i u → H.Adj u v →
        ∃ y ∈ cand H G T f i v, G.Adj x y} := fun i => rfl
  have c2 : ∀ i u, cand H G T f (i + 1) u = cand H G T f i u ∩ candSet H G T f (i + 1) :=
    fun i u => rfl
  have mono : ∀ i u, cand H G T f i u ⊆ cand H G T f 0 u := by
    intro i
    induction i with
    | zero => intro u; exact le_rfl
    | succ i ih =>
      intro u x hx
      rw [c2] at hx
      exact ih u hx.1
  have hdisj : ∀ u v x, x ∈ cand H G T f 0 u → x ∈ cand H G T f 0 v → u = v := by
    intro u v x hxu hxv
    by_contra huv
    obtain ⟨t, ht, hd⟩ := hT' u v huv
    apply hd
    have h1 : G.dist (f ⟨t, ht⟩) x = H.dist t u := hxu ⟨t, ht⟩
    have h2 : G.dist (f ⟨t, ht⟩) x = H.dist t v := hxv ⟨t, ht⟩
    exact h1.symm.trans h2
  have hmain : ∀ i u, C u ⊆ cand H G T f i u := by
    intro i
    induction i with
    | zero =>
      intro u x hx t
      exact hi t u x hx
    | succ i ih =>
      intro u x hx
      rw [c2]
      have hxi : x ∈ cand H G T f i u := ih u hx
      have hxs : x ∈ candSet H G T f (i + 1) := by
        rw [c1]
        refine ⟨?_, ?_⟩
        · cases i with
          | zero => exact Set.mem_iUnion.mpr ⟨u, hxi⟩
          | succ i =>
            have := hxi
            rw [c2] at this
            exact this.2
        · intro u' v hu' hadj
          have h0u : x ∈ cand H G T f 0 u := mono i u hxi
          have h0u' : x ∈ cand H G T f 0 u' := mono i u' hu'
          have : u' = u := hdisj u' u x h0u' h0u
          subst this
          obtain ⟨y, hy, hxy⟩ := hii u' v hadj x hx
          exact ⟨y, ih v hy, hxy⟩
      exact ⟨hxi, hxs⟩
  intro u
  exact hmain _ u

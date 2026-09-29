-- Prove2me | solution 1 for GoldbergTarjan.Generic.positive_excess_reaches_source
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:46:20.608995+00:00
-- url     : https://prove2.me/submissions/525969e1-8717-423c-9116-0a82f0768c43

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

open GoldbergTarjan.Generic

theorem solution {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (v : V)
    (hf : IsPreflow N f) (hv : 0 < excess f v) :
    ResidualReachable N f v N.s := by
  classical
  by_contra hcon
  -- `T` is the set of vertices from which the source is *not* reachable
  set T : Finset V := Finset.univ.filter (fun u => ¬ ResidualReachable N f u N.s) with hT
  have hmemT : ∀ u : V, u ∈ T ↔ ¬ ResidualReachable N f u N.s := by
    intro u; simp [hT]
  have hvT : v ∈ T := (hmemT v).mpr hcon
  have hsT : N.s ∉ T := by
    rw [hmemT]
    exact fun h => h Relation.ReflTransGen.refl
  -- no flow enters `T` from outside
  have hnores : ∀ u ∈ T, ∀ w ∈ Tᶜ, f w u ≤ 0 := by
    intro u hu w hw
    rw [hmemT] at hu
    have hws : ResidualReachable N f w N.s := by
      by_contra h
      exact (Finset.mem_compl.mp hw) ((hmemT w).mpr h)
    have hnotedge : ¬ IsResidualEdge N f u w := fun he =>
      hu (Relation.ReflTransGen.head he hws)
    have h1 : N.c u w - f u w ≤ 0 := not_lt.mp hnotedge
    have h2 : (0:ℝ) ≤ N.c u w := N.cap_nonneg u w
    have h3 : f w u = -f u w := hf.2.1 w u
    linarith
  -- the flow inside `T` cancels by antisymmetry
  have hanti : ∑ u ∈ T, ∑ w ∈ T, f w u = 0 := by
    have key : ∑ u ∈ T, ∑ w ∈ T, f w u = -∑ u ∈ T, ∑ w ∈ T, f w u := by
      calc ∑ u ∈ T, ∑ w ∈ T, f w u
          = ∑ u ∈ T, ∑ w ∈ T, (-f u w) := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
            rw [hf.2.1 w u]
        _ = -∑ u ∈ T, ∑ w ∈ T, f u w := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_neg_distrib]
        _ = -∑ u ∈ T, ∑ w ∈ T, f w u := by rw [Finset.sum_comm]
    linarith
  -- the flow from outside is nonpositive
  have houter : ∑ u ∈ T, ∑ w ∈ Tᶜ, f w u ≤ 0 :=
    Finset.sum_nonpos fun u hu => Finset.sum_nonpos fun w hw => hnores u hu w hw
  -- total excess over `T` is therefore nonpositive
  have hsplit : ∑ u ∈ T, excess f u
      = (∑ u ∈ T, ∑ w ∈ T, f w u) + ∑ u ∈ T, ∑ w ∈ Tᶜ, f w u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [excess, ← Finset.sum_add_sum_compl T (fun w => f w u)]
  have hle : ∑ u ∈ T, excess f u ≤ 0 := by rw [hsplit, hanti]; linarith
  -- but the excesses inside `T` are nonnegative and `v` has positive excess
  have hpos : 0 < ∑ u ∈ T, excess f u := by
    refine Finset.sum_pos' (fun u hu => ?_) ⟨v, hvT, hv⟩
    refine hf.2.2 u ?_
    intro h
    exact hsT (h ▸ hu)
  linarith

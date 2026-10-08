-- Prove2me | solution 1 for JordanCurve.jordan_frontier_intersection_dense_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:40:11.267706+00:00
-- url     : https://prove2.me/submissions/c55bd60c-c375-4097-b6fb-a2179a87448a

import Theorems.Thm_JordanCurve_one_sided_frontier_from_arc_complement
import Mathlib.Topology.Closure

theorem solution
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure (frontier inside ∩ frontier outside) := by
  have hi := JordanCurve.one_sided_frontier_from_arc_complement
    hArc γ hγ hinj inside outside hiopen hoopen hiconn hoconn hdisj hcover
  have ho := JordanCurve.one_sided_frontier_from_arc_complement
    hArc γ hγ hinj outside inside hoopen hiopen hoconn hiconn
      hdisj.symm (by rw [Set.union_comm]; exact hcover)
  intro x hx
  exact subset_closure ⟨hi hx, ho hx⟩

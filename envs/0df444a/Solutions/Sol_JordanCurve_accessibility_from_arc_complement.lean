-- Prove2me | solution 1 for JordanCurve.accessibility_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:37:34.633276+00:00
-- url     : https://prove2.me/submissions/9c9b6466-98db-46e5-9bab-c59699f08110

import Theorems.Thm_JordanCurve_jordan_frontier_intersection_dense_from_arc_complement
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
    Set.range γ ⊆ closure inside ∩ closure outside := by
  have hdense :=
    JordanCurve.jordan_frontier_intersection_dense_from_arc_complement
      hArc γ hγ hinj inside outside hiopen hoopen hiconn hoconn hdisj hcover
  have hclosed : IsClosed (frontier inside ∩ frontier outside) :=
    isClosed_frontier.inter isClosed_frontier
  have hfront : Set.range γ ⊆ frontier inside ∩ frontier outside :=
    hdense.trans hclosed.closure_subset
  intro x hx
  have hf := hfront hx
  exact ⟨frontier_subset_closure hf.1, frontier_subset_closure hf.2⟩

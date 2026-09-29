-- Prove2me | solution 1 for JordanCurve.jordan_curve_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:16:50.485143+00:00
-- url     : https://prove2.me/submissions/cef53798-781b-43d2-9bf2-b2c5287dabce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_JordanCurve_simple_closed_curve_two_regions
import Theorems.Thm_JordanCurve_simple_closed_curve_two_sided_accessibility
import Theorems.Thm_JordanCurve_frontiers_of_open_partition

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = (Set.range γ)ᶜ ∧
      frontier inside = Set.range γ ∧
      frontier outside = Set.range γ := by
  obtain ⟨inside, outside, hiopen, hoopen, hiconn, hoconn,
      hibounded, hounbounded, hdisj, hcover⟩ :=
    JordanCurve.simple_closed_curve_two_regions γ hγ hinj
  have haccess :=
    JordanCurve.simple_closed_curve_two_sided_accessibility γ hγ hinj
      inside outside hiopen hoopen hiconn hoconn hdisj hcover
  obtain ⟨hfronti, hfronto⟩ :=
    JordanCurve.frontiers_of_open_partition (Set.range γ) inside outside
      hiopen hoopen hdisj hcover haccess
  exact ⟨inside, outside, hiopen, hoopen, hiconn, hoconn,
    hibounded, hounbounded, hdisj, hcover, hfronti, hfronto⟩

-- Prove2me | solution 1 for JordanCurve.simple_closed_curve_two_sided_accessibility
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:27:07.070885+00:00
-- url     : https://prove2.me/submissions/6f4957c6-4237-42b6-b5d4-746e38d6dfa0

import Theorems.Thm_JordanCurve_simple_arc_complement_connected
import Theorems.Thm_JordanCurve_accessibility_from_arc_complement

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure inside ∩ closure outside := by
  apply JordanCurve.accessibility_from_arc_complement
    (fun α hα hinj => JordanCurve.simple_arc_complement_connected α hα hinj)
    γ hγ hinj inside outside hiopen hoopen hiconn hoconn hdisj hcover

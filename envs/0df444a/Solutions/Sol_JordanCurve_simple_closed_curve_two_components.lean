-- Prove2me | solution 1 for JordanCurve.simple_closed_curve_two_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:29:33.830092+00:00
-- url     : https://prove2.me/submissions/0d80bf79-a407-4d47-b246-e595a86b2704
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_JordanCurve_simple_arc_complement_connected
import Theorems.Thm_JordanCurve_two_components_from_arc_complement

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ a b : EuclideanSpace ℝ (Fin 2),
      a ∉ Set.range γ ∧ b ∉ Set.range γ ∧
      Disjoint
        (connectedComponentIn ((Set.range γ)ᶜ) a)
        (connectedComponentIn ((Set.range γ)ᶜ) b) ∧
      connectedComponentIn ((Set.range γ)ᶜ) a ∪
        connectedComponentIn ((Set.range γ)ᶜ) b = (Set.range γ)ᶜ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) b) := by
  exact JordanCurve.two_components_from_arc_complement
    (fun α hα hinj => JordanCurve.simple_arc_complement_connected α hα hinj)
    γ hγ hinj

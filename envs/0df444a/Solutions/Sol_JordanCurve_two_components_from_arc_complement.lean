-- Prove2me | solution 1 for JordanCurve.two_components_from_arc_complement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:37:20.354116+00:00
-- url     : https://prove2.me/submissions/23537fdd-70f3-4aba-b1ec-7f69e7abe402
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_JordanCurve_jordan_complement_two_distinct_regions
import Theorems.Thm_JordanCurve_arc_complement_at_most_two_regions

theorem solution
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
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
  obtain ⟨a, b, ha, hb, hdisj, hibounded, hounbounded⟩ :=
    JordanCurve.jordan_complement_two_distinct_regions γ hγ hinj
  have hcover :=
    JordanCurve.arc_complement_at_most_two_regions
      hArc γ hγ hinj a b ha hb hdisj
  exact ⟨a, b, ha, hb, hdisj, hcover, hibounded, hounbounded⟩

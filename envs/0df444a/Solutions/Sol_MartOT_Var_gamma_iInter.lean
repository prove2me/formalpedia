-- Prove2me | solution 1 for MartOT.Var.gamma_iInter
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:37:40.627446+00:00
-- url     : https://prove2.me/submissions/f657c213-867a-4595-bcde-e2869593801e

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

open MartOT.Var in
theorem solution (c : ℝ → ℝ → ℝ) (π : Measure (ℝ × ℝ)) (Γn : ℕ → Set (ℝ × ℝ))
    (hmeas : ∀ n, MeasurableSet (Γn n)) (hfull : ∀ n, π (Γn n)ᶜ = 0)
    (hopt : ∀ n (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), S.card ≤ n →
      (↑S : Set (ℝ × ℝ)) ⊆ Γn n → ∀ α' : Measure (ℝ × ℝ),
        IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α') :
    MeasurableSet (⋂ n, Γn n) ∧ π (⋂ n, Γn n)ᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ ⋂ n, Γn n →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by
  refine ⟨MeasurableSet.iInter hmeas, ?_, ?_⟩
  · rw [Set.compl_iInter]
    exact measure_iUnion_null hfull
  · intro S w hS α' hα'
    exact hopt S.card S w le_rfl (hS.trans (Set.iInter_subset _ _)) α' hα'

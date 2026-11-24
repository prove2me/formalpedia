-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalPastCylinderPiSystemV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:19:24.961072+00:00
-- url     : https://prove2.me/submissions/e630236b-840e-4146-b84a-c5f5f8babe65

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (t : NNReal) :
    IsPiSystem {A : Set {path : NNReal → ℝ // path 0 = 0} | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E} := by
  classical
  let C : Set (Set {path : NNReal → ℝ // path 0 = 0}) :=
    {A | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E}
  have hPi : IsPiSystem C := by
    rintro A₁ ⟨I₁, hI₁, E₁, hE₁, rfl⟩ A₂ ⟨I₂, hI₂, E₂, hE₂, rfl⟩ _
    let I : Finset NNReal := I₁ ∪ I₂
    have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
      rcases Finset.mem_union.mp hs with h1 | h2
      · exact hI₁ s h1
      · exact hI₂ s h2
    have h1 : I₁ ⊆ I := Finset.subset_union_left
    have h2 : I₂ ⊆ I := Finset.subset_union_right
    let E : Set (∀ _ : I, ℝ) :=
      Finset.restrict₂ (π := fun _ : NNReal => ℝ) h1 ⁻¹' E₁ ∩
        Finset.restrict₂ (π := fun _ : NNReal => ℝ) h2 ⁻¹' E₂
    have hE : MeasurableSet E :=
      ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h1) hE₁).inter
        ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h2) hE₂)
    exact ⟨I, hI, E, hE, by ext w; rfl⟩
  exact hPi

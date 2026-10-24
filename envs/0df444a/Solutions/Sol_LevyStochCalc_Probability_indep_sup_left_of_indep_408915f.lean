-- Prove2me | solution 1 for LevyStochCalc.Probability.indep_sup_left_of_indep_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:02:40.353472+00:00
-- url     : https://prove2.me/submissions/5def1551-9ba7-44f8-bb51-d78ca205a867

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
lemma LevyStochCalc.Probability.isPiSystem_interSets : IsPiSystem (interSets m₁ m₂) := by
  rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ -
  exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by ext x; simp; tauto⟩
omit [IsProbabilityMeasure P] in
lemma LevyStochCalc.Probability.sup_eq_generateFrom_interSets : m₁ ⊔ m₂ = MeasurableSpace.generateFrom (interSets m₁ m₂) := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · intro A hA
    exact MeasurableSpace.measurableSet_generateFrom ⟨A, Set.univ, hA, MeasurableSet.univ,
      (Set.inter_univ A).symm⟩
  · intro B hB
    exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, B, MeasurableSet.univ, hB,
      (Set.univ_inter B).symm⟩
  · rintro _ ⟨A, B, hA, hB, rfl⟩
    exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) _ hA).inter ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) _ hB)
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- If `m₁ ⟂ m₃` and `m₂ ⟂ m₁ ⊔ m₃`, then `m₁ ⊔ m₂ ⟂ m₃`. -/
theorem solution (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ)
    (h13 : Indep m₁ m₃ P) (h2 : Indep m₂ (m₁ ⊔ m₃) P) : Indep (m₁ ⊔ m₂) m₃ P := by
  refine IndepSets.indep (sup_le h₁ h₂) h₃ LevyStochCalc.Probability.isPiSystem_interSets
    (@MeasurableSpace.isPiSystem_measurableSet Ω m₃) LevyStochCalc.Probability.sup_eq_generateFrom_interSets
    (@MeasurableSpace.generateFrom_measurableSet Ω m₃).symm ?_
  rw [IndepSets_iff]
  rintro _ C ⟨A, B, hA, hB, rfl⟩ hC
  have hAC : MeasurableSet[m₁ ⊔ m₃] (A ∩ C) :=
    ((le_sup_left : m₁ ≤ m₁ ⊔ m₃) _ hA).inter ((le_sup_right : m₃ ≤ m₁ ⊔ m₃) _ hC)
  have hA' : MeasurableSet[m₁ ⊔ m₃] A := (le_sup_left : m₁ ≤ m₁ ⊔ m₃) _ hA
  rw [Indep_iff] at h13 h2
  have e1 : A ∩ B ∩ C = B ∩ (A ∩ C) := by ext x; simp; tauto
  have e2 : A ∩ B = B ∩ A := Set.inter_comm A B
  rw [e1, h2 B (A ∩ C) hB hAC, h13 A C hA hC, e2, h2 B A hB hA']
  ring

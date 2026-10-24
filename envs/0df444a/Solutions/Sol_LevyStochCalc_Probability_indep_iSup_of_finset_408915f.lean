-- Prove2me | solution 1 for LevyStochCalc.Probability.indep_iSup_of_finset_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:59:37.762735+00:00
-- url     : https://prove2.me/submissions/6af992e6-0991-44e3-8df4-38dc27e58e6c

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
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- **Independence of a supremum from independence of its finite subjoins.** -/
theorem solution {ι : Type*} {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
    (h : ∀ S : Finset ι, Indep (⨆ i ∈ S, m i) m' P) :
    Indep (⨆ i, m i) m' P := by
  classical
  have hsup : (⨆ S : Finset ι, ⨆ i ∈ S, m i) = ⨆ i, m i :=
    le_antisymm (iSup_le fun _ => iSup_le fun i => iSup_le fun _ => le_iSup m i)
      (iSup_le fun i => le_iSup_of_le {i} (le_iSup₂_of_le i (Finset.mem_singleton_self i) le_rfl))
  rw [← hsup]
  refine indep_iSup_of_directed_le h
    (fun _ => iSup_le fun i => iSup_le fun _ => h_le i) h_le' fun S T => ⟨S ∪ T, ?_, ?_⟩
  · exact iSup_le fun i => iSup_le fun hi =>
      le_iSup₂_of_le i (Finset.mem_union_left T hi) le_rfl
  · exact iSup_le fun i => iSup_le fun hi =>
      le_iSup₂_of_le i (Finset.mem_union_right S hi) le_rfl

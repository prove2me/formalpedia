-- Prove2me | solution 1 for OAI.C0Absorption.nat_constant_or_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:36:15.509471+00:00
-- url     : https://prove2.me/submissions/5291c98f-d473-47d9-a3c4-a1ee0e5ca39f

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology


theorem solution (f : ℕ → ℕ) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    Tendsto f atTop atTop := by
  by_cases ht : Tendsto f atTop atTop
  · exact Or.inr ht
  left
  rw [Filter.tendsto_atTop] at ht
  push_neg at ht
  obtain ⟨b, hb⟩ := ht
  have hfin : ∃ a, ∃ᶠ i in atTop, f i = a := by
    by_contra hno
    push_neg at hno
    have hall : ∀ a ∈ Finset.range b, ∀ᶠ i in atTop, f i ≠ a := by
      intro a _
      have := hno a
      exact this
    have hev := (Filter.eventually_all_finset _).2 hall
    obtain ⟨i, hlt, hi⟩ := (hb.and_eventually hev).exists
    exact hi (f i) (Finset.mem_range.2 hlt) rfl
  obtain ⟨a, ha⟩ := hfin
  obtain ⟨φ, hφ, hφa⟩ := Filter.extraction_of_frequently_atTop ha
  exact ⟨a, φ, hφ, hφa⟩


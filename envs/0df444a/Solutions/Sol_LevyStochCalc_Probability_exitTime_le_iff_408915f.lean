-- Prove2me | solution 1 for LevyStochCalc.Probability.exitTime_le_iff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:06:58.002262+00:00
-- url     : https://prove2.me/submissions/bdef5f15-9803-4a47-9af1-94022872fbc6

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Mathlib.Data.Rat.Denumerable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
theorem LevyStochCalc.Probability.bddBelow_exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : BddBelow (exitSet X k ω) :=
  ⟨0, fun _ ht => ht.1⟩
theorem LevyStochCalc.Probability.isClosed_exitSet {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) :
    IsClosed (exitSet X k ω) := by
  have h : exitSet X k ω = Set.Ici (0 : ℝ) ∩ (fun r => ‖X ω r‖) ⁻¹' Set.Ici k := by
    ext r
    simp only [exitSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Ici.preimage hX.norm)
theorem LevyStochCalc.Probability.csInf_exitSet_mem {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k : ℝ}
    (h : (exitSet X k ω).Nonempty) : sInf (exitSet X k ω) ∈ exitSet X k ω :=
  (isClosed_exitSet hX k).csInf_mem h (bddBelow_exitSet X k ω)
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- For a continuous path, the exit time is at most `t` exactly when the path reaches norm `k`
somewhere on `[0, t]`. -/
theorem solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    LevyStochCalc.Probability.exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by
  constructor
  · intro hle
    rw [LevyStochCalc.Probability.exitTime] at hle
    split_ifs at hle with h
    · have hmem := LevyStochCalc.Probability.csInf_exitSet_mem hX h
      have hst : sInf (LevyStochCalc.Probability.exitSet X k ω) ≤ t := by exact_mod_cast hle
      exact ⟨sInf (LevyStochCalc.Probability.exitSet X k ω), ⟨hmem.1, hst⟩, hmem.2⟩
    · exact absurd hle (by simp)
  · rintro ⟨s, ⟨hs0, hst⟩, hks⟩
    have hne : (LevyStochCalc.Probability.exitSet X k ω).Nonempty := ⟨s, hs0, hks⟩
    rw [LevyStochCalc.Probability.exitTime, if_pos hne]
    have hle : sInf (LevyStochCalc.Probability.exitSet X k ω) ≤ t :=
      le_trans (csInf_le (LevyStochCalc.Probability.bddBelow_exitSet X k ω) ⟨hs0, hks⟩) hst
    exact_mod_cast hle

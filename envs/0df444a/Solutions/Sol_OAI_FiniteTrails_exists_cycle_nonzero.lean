-- Prove2me | solution 1 for OAI.FiniteTrails.exists_cycle_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:12:32.373131+00:00
-- url     : https://prove2.me/submissions/9f8b9bed-c211-4f8c-a08a-7e65a2fb7362

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails

open OAI OAI.FiniteTrails
universe uD uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Classical Function
variable {D : Type uD} {V : Type uV} [Fintype D]


theorem solution (σ : Equiv.Perm D) (w : D → ℤ)
    (hw : ∑ d, w d ≠ 0) :
    ∃ d, (∑ e : D, if σ.SameCycle d e then w e else 0) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  apply hw
  let S : Setoid D := ⟨σ.SameCycle, Equiv.Perm.SameCycle.refl σ, fun h => h.symm, fun h k => h.trans k⟩
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := (Quotient.mk S : D → Quotient S))]
  apply Finset.sum_eq_zero
  intro q _
  induction q using Quotient.ind with
  | _ d =>
    rw [← hcon d, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    apply propext
    constructor
    · intro h; exact (Quotient.exact h).symm
    · intro h; exact Quotient.sound h.symm


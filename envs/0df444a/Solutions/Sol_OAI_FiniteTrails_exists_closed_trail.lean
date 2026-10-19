-- Prove2me | solution 1 for OAI.FiniteTrails.exists_closed_trail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:16:04.893984+00:00
-- url     : https://prove2.me/submissions/fc0bdad6-0489-424a-8e1e-240c637a4090

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
theorem pl_succ_tail {D : Type uD} {V : Type uV} [Fintype D] (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v}) (d : D) :
    tail (successor tail head hbal d) = head d :=
  (Fintype.equivOfCardEq (hbal (head d)) ⟨d, rfl⟩).property

theorem solution (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by
  set σ := successor tail head hbal with hσ
  have hst : ∀ d, tail (σ d) = head d := pl_succ_tail tail head hbal
  let g : D → Quotient (Equiv.Perm.SameCycle.setoid σ) := fun d => Quotient.mk _ d
  have hsum := Finset.sum_fiberwise Finset.univ g w
  rw [← hsum] at hw
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  induction q using Quotient.inductionOn with
  | h d =>
  refine ⟨minimalPeriod σ d, period_pos σ d, fun i => σ^[i.val] d, ?_, ?_, ?_⟩
  · intro i j hij; exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij)
  · intro i
    show tail (σ^[((i.val+1) % minimalPeriod σ d)] d) = head (σ^[i.val] d)
    rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply', hst]
  · have h1 : ∑ i : Fin (minimalPeriod σ d), w (σ^[i.val] d) = ∑ e : {e // σ.SameCycle d e}, w e.val :=
      Equiv.sum_comp (cycleEquiv σ d) (fun e => w e.val)
    rw [h1]
    convert hq using 1
    symm
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    rw [Quotient.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩


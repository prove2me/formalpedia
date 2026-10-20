-- Prove2me | solution 1 for OAI.TalagrandThreshold.isCompact_fractionalFeasible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T14:11:43.183292+00:00
-- url     : https://prove2.me/submissions/8310e9d5-61e1-40c2-b1bc-5680859f01e5

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMain

open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α] in
theorem solution (F : Family α) :
    IsCompact (fractionalFeasible F) := by
  classical
  let K : Set (ℝ × (Finset α → ℝ)) :=
    (Set.Icc (0:ℝ) 1 ×ˢ Set.univ.pi (fun _ => Set.Icc (0:ℝ) 1)) ∩
      ({x | ∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, x.2 S} ∩ {x | fracCost x.1 x.2 ≤ 1/2})
  have hK : IsCompact K := by
    refine (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)).inter_right ?_
    refine IsClosed.inter ?_ ?_
    · simp only [Set.setOf_forall]
      refine isClosed_biInter fun H _ => isClosed_le continuous_const ?_
      exact continuous_finset_sum _ fun S _ => (continuous_apply S).comp continuous_snd
    · refine isClosed_le ?_ continuous_const
      unfold fracCost
      exact continuous_finset_sum _ fun S _ =>
        ((continuous_apply S).comp continuous_snd).mul (continuous_fst.pow _)
  have hEq : fractionalFeasible F = Prod.fst '' K := by
    ext p
    constructor
    · rintro ⟨h0, h1, g, ⟨hg, hcov⟩, hc⟩
      exact ⟨(p, g), ⟨⟨⟨h0, h1⟩, fun S _ => hg S⟩, hcov, hc⟩, rfl⟩
    · rintro ⟨⟨q, g⟩, ⟨⟨⟨h0, h1⟩, hg⟩, hcov, hc⟩, rfl⟩
      exact ⟨h0, h1, g, ⟨fun S => hg S (Set.mem_univ _), hcov⟩, hc⟩
  rw [hEq]; exact hK.image continuous_fst

-- Prove2me | solution 2 for OAI.TalagrandThreshold.isCompact_fractionalFeasible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:18:36.579549+00:00
-- url     : https://prove2.me/submissions/ffe75dda-dc2b-4693-bc1a-f7f3ba8bbea3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ThresholdCompactness.lean:L32-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.isCompact_fractionalFeasible. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.ThresholdCompactness ----
namespace OAI

/-!
# Compactness of the fractional feasible densities

The cover coefficients and the density range over closed unit intervals.
The coverage inequalities and the polynomial cost bound cut out a closed
subset of their compact product. Its projection is exactly the set of
fractionally feasible densities, including when that set is empty.
-/

namespace TalagrandThreshold

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The fractional cost is jointly continuous in the density and coefficients. -/
theorem continuous_fracCost :
    Continuous (fun z : ℝ × (Finset α → ℝ) => fracCost z.1 z.2) := by
  unfold fracCost
  exact continuous_finsetSum Finset.univ fun S _ =>
    ((continuous_apply S).comp continuous_snd).mul (continuous_fst.pow S.card)

omit [DecidableEq α] in
/-- Fractional feasibility is the projection of the actual compact set of covers. -/
theorem isCompact_fractionalFeasible (F : Family α) :
    IsCompact (fractionalFeasible F) := by
  let B : Set (ℝ × (Finset α → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ {g | ∀ S, 0 ≤ g S ∧ g S ≤ 1}
  let C : Set (ℝ × (Finset α → ℝ)) :=
    {z | (∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, z.2 S) ∧ fracCost z.1 z.2 ≤ 1 / 2}
  have hbox : IsCompact B :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).prod
      (isCompact_pi_infinite fun _ : Finset α =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
  have hcoverage : IsClosed
      {z : ℝ × (Finset α → ℝ) | ∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, z.2 S} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun H => isClosed_iInter fun _ => ?_
    exact isClosed_le continuous_const
      (continuous_finsetSum H.powerset fun S _ =>
        (continuous_apply S).comp continuous_snd)
  have hcost : IsClosed
      {z : ℝ × (Finset α → ℝ) | fracCost z.1 z.2 ≤ 1 / 2} :=
    isClosed_le continuous_fracCost continuous_const
  have hclosed : IsClosed C := hcoverage.inter hcost
  have himage : Prod.fst '' (B ∩ C) = fractionalFeasible F := by
    ext p
    constructor
    · rintro ⟨⟨q, g⟩, ⟨hB, hC⟩, hp⟩
      change (0 ≤ q ∧ q ≤ 1) ∧ (∀ S, 0 ≤ g S ∧ g S ≤ 1) at hB
      change (∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, g S) ∧ fracCost q g ≤ 1 / 2 at hC
      change q = p at hp
      subst p
      exact ⟨hB.1.1, hB.1.2, g, ⟨hB.2, hC.1⟩, hC.2⟩
    · rintro ⟨hp0, hp1, g, hcover, hcost⟩
      exact ⟨(p, g), ⟨⟨⟨hp0, hp1⟩, hcover.1⟩, ⟨hcover.2, hcost⟩⟩, rfl⟩
  rw [← himage]
  exact (hbox.inter_right hclosed).image continuous_fst

end
end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.isCompact_fractionalFeasible := @_root_.OAI.TalagrandThreshold.isCompact_fractionalFeasible

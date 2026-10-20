-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.isClosed_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:49:35.454126+00:00
-- url     : https://prove2.me/submissions/f4ce16fd-f1ba-445e-b852-1d69b90e4d75

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationCompact.lean:L33-L56
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.isClosed_admissible. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorTruncationDefinitions ----
namespace OAI

/-!
# Finite weighted truncation

The heavy set uses a strict cutoff. Weights equal to the cutoff are already
saturated when the cutoff increases, as required by the maximal truncation
argument.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem Admissible.outside_le {w : α → ℝ} {A : Finset α} {m d u : ℝ}
    (hu : Admissible w A m d u) {x : α} (hx : x ∉ A) : w x ≤ u := by
  exact le_of_not_gt (fun h => hx (hu.2.2.1 x h))

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorTruncationCompact ----
namespace OAI

/-!
# Existence of the maximal admissible truncation

The condition that every heavy point belongs to `A` is a family of closed
lower bounds on the cutoff, one for each point outside `A`. The excess is a
continuous finite sum. Thus the admissible cutoffs form a closed subset of
`[0, 1]`, and a nonempty such set has a greatest element.

This existence argument does not use positivity or normalization of the
weights, or sign assumptions on the parameters `m` and `d`.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Finite truncation gives a continuous excess as the cutoff varies. -/
theorem continuous_truncatedExcess (w : α → ℝ) (A : Finset α) (d : ℝ) :
    Continuous (fun u => truncatedExcess w A d u) := by
  unfold truncatedExcess
  apply continuous_finsetSum
  intro x _
  exact (continuous_const.min continuous_id).mul continuous_const

/-- The heavy-point inclusion and the excess test are closed conditions. -/
theorem isClosed_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ) :
    IsClosed {u : ℝ | Admissible w A m d u} := by
  have hlarge : IsClosed {u : ℝ | ∀ x, x ∉ A → w x ≤ u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_le continuous_const continuous_id
  have hexcess : IsClosed {u : ℝ | m * u ≤ truncatedExcess w A d u} :=
    isClosed_le (continuous_const.mul continuous_id)
      (continuous_truncatedExcess w A d)
  have hrepr : {u : ℝ | Admissible w A m d u} =
      (Set.Icc 0 1 ∩ {u : ℝ | ∀ x, x ∉ A → w x ≤ u}) ∩
        {u : ℝ | m * u ≤ truncatedExcess w A d u} := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨⟨hu.1, hu.2.1⟩, fun _ hx => hu.outside_le hx⟩, hu.2.2.2⟩
    · intro hu
      refine ⟨hu.1.1.1, hu.1.1.2, ?_, hu.2⟩
      intro x hux
      by_contra hx
      exact (not_lt_of_ge (hu.1.2 x hx)) hux
  rw [hrepr]
  exact (isClosed_Icc.inter hlarge).inter hexcess

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.isClosed_admissible := @_root_.OAI.TalagrandThreshold.Selector.isClosed_admissible

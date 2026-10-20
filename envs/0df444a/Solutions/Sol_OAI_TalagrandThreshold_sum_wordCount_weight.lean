-- Prove2me | solution 1 for OAI.TalagrandThreshold.sum_wordCount_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:37:54.937788+00:00
-- url     : https://prove2.me/submissions/f0648f07-0efb-4436-903a-133377ed4e4e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWords.lean:L69-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.sum_wordCount_weight. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingWords ----
namespace OAI

/-!
# Counting finite words by their color profiles

The coefficient attached to a profile is the actual cardinality of its fiber
among finite words. Regrouping the weighted sum over words proves the finite
multinomial identity without introducing a factorial formula or a counting
hypothesis.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The weight from a profile equals the product of the individual letter weights. -/
theorem prod_weight_wordProfile {D : Type*} [Fintype D]
    (f : D → H) (π : H → ℝ) :
    (∏ h, π h ^ wordProfile f h) = ∏ i, π (f i) := by
  simpa only [wordProfile, Finset.prod_const] using
    (Finset.prod_fiberwise' (Finset.univ : Finset D) f π)

/-- The multinomial identity obtained by grouping actual words by their profile. -/
theorem sum_wordCount_weight (t : ℕ) (π : H → ℝ) :
    (∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h) =
      (∑ h, π h) ^ t := by
  have hgroup : (∑ f : Fin t → H, ∏ h, π h ^ wordProfile f h) =
      ∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h := by
    simpa only [wordProfiles, wordCount, wordFiber, nsmul_eq_mul] using
      (Finset.sum_comp (s := (Finset.univ : Finset (Fin t → H)))
        (fun n : H → ℕ => ∏ h, π h ^ n h) (fun f : Fin t → H => wordProfile f))
  calc
    _ = ∑ f : Fin t → H, ∏ h, π h ^ wordProfile f h := hgroup.symm
    _ = ∑ f : Fin t → H, ∏ i, π (f i) := by
      apply Finset.sum_congr rfl
      intro f _
      exact prod_weight_wordProfile f π
    _ = (∑ h, π h) ^ t := (Fintype.sum_pow π t).symm

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.sum_wordCount_weight := @_root_.OAI.TalagrandThreshold.sum_wordCount_weight

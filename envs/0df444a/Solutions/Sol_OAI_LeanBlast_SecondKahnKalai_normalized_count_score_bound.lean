-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:23:34.254896+00:00
-- url     : https://prove2.me/submissions/9be3d25d-0b8b-4dac-beca-e6ad5b20427f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean:L72-L88
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor

-- ---- from OAI.Combinatorics.GraphThreshold.Predecessor ----
namespace OAI

/-!
# Maximizing predecessors

The predecessor is chosen by maximization over the actual finite powerset,
including its empty member.  The graph application uses distinct group-orbit
copies and the actual containment probability, not labeled embeddings.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

/-- Arithmetic form of the expectation constraint and internal-copy count bound. -/
theorem normalized_count_score_bound {a m h r : ℕ} {q : ℝ}
    (hq : 0 < q) (hm : 0 < m) (ha : a ≤ h.choose r)
    (he : (1 / 2 : ℝ) ≤ (m : ℝ) * q ^ r) :
    ((a : ℝ) / (m : ℝ)) / (128 * q) ^ r ≤
      2 * (h.choose r : ℝ) / (128 : ℝ) ^ r := by
  apply (div_le_iff₀ (pow_pos (by positivity : 0 < 128 * q) r)).mpr
  have hscale : (2 * (h.choose r : ℝ) / (128 : ℝ) ^ r) * (128 * q) ^ r =
      2 * (h.choose r : ℝ) * q ^ r := by
    rw [mul_pow]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (show 0 < (m : ℝ) by exact_mod_cast hm)).mpr
  have ha' : (a : ℝ) ≤ (h.choose r : ℝ) := by exact_mod_cast ha
  have hprod := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2 * (h.choose r : ℝ) by positivity)
  nlinarith

section FiniteMaximum

variable {X : Type*}

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound := @_root_.OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound

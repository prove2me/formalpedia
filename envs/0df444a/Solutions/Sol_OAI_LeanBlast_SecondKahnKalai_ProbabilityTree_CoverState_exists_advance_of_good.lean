-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:13:37.780205+00:00
-- url     : https://prove2.me/submissions/0e60abf2-b9f8-46c3-abe9-e8b822fc6dee

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean:L335-L353
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_ProbabilityTree_CoverState_exists_advance_of_halved
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_reduceTree_hasSpread
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_reduceTree_isDisjoint
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_reduceTree_path_recovery

-- ---- from OAI.Combinatorics.GraphThreshold.CapacityIteration ----
-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
private abbrev Finset.prod_le_prod_of_subset_of_le_one₀ := @Finset.prod_le_prod_of_subset_of_le_one

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

theorem retentionFactor_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - Real.exp (-(m : ℝ)) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact neg_neg_of_pos (by exact_mod_cast hm)

theorem retentionFactor_le_one (m : ℕ) :
    1 - Real.exp (-(m : ℝ)) ≤ 1 := sub_le_self _ (Real.exp_pos _).le

theorem capacityReserve_pos {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    0 < capacityReserve σ m := by
  apply mul_pos (mul_pos (by norm_num) hσ)
  apply Finset.prod_pos
  intro j hj
  exact retentionFactor_pos (Finset.mem_Icc.mp hj).1

theorem antitone_capacityReserve {σ : ℝ} (hσ : 0 ≤ σ) :
    Antitone (capacityReserve σ) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro j hj
    obtain ⟨hj1, hja⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hj1, hja.trans hab⟩
  · intro j hj
    exact (retentionFactor_pos (Finset.mem_Icc.mp hj).1).le
  · intro j _ _
    exact retentionFactor_le_one j

theorem capacityReserve_succ (σ : ℝ) (m : ℕ) :
    capacityReserve σ (m + 1) = capacityReserve σ m *
      (1 - Real.exp (-((m + 1 : ℕ) : ℝ))) := by
  simp only [capacityReserve, Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega), mul_assoc]

theorem capacityReserve_div_le_half {σ : ℝ} (hσ : 0 ≤ σ) {m : ℕ} (hm : 0 < m) :
    capacityReserve σ m / (1 - Real.exp (-(m : ℝ))) ≤ capacityReserve σ (m / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [capacityReserve_succ, mul_div_cancel_right₀ _ (retentionFactor_pos (Nat.succ_pos m)).ne']
  exact antitone_capacityReserve hσ (show (m + 1) / 2 ≤ m by omega)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReductionData ----
namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem successfulTargetMass_pos_capacity (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) (W : Finset X) (b : B)
    (hb : 0 < successfulTargetMass μ A ρ m W b) : (A b \ W).card ≤ m / 2 := by
  by_contra hcap
  have hfail (c : B) : ¬LocalSuccess μ A ρ m W c b := fun h => hcap h.2
  simp [successfulTargetMass, hfail] at hb

end LocalMasses

variable {X : Type} [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Classical

noncomputable section

namespace LeanBlast.SecondKahnKalai

section RetainedLaw

variable {B X : Type*} [Fintype B] [DecidableEq X]

end RetainedLaw

section Construction

variable {X : Type} [DecidableEq X]

theorem reduceTree_hasCapacities (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) :
    (reduceTree ρ m W T hρ hm hg).HasCapacities (fun j => m j / 2) := by
  induction T generalizing m with
  | leaf => simp only [reduceTree, ProbabilityTree.HasCapacities]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.HasCapacities]
      constructor
      · intro b
        exact successfulTargetMass_pos_capacity μ A ρ (m 0) W b.val b.property.2
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1

end Construction

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeCovering ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

/-- A good draw produces an actual strict advance: construct the pruned tree,
preserve the reserve budget, and delete exactly its zero-capacity prefix. -/
theorem exists_advance_of_good (state : CoverState original σ) (W : Finset X)
    (hσ : 0 < σ) {ρ : ℝ} (hρ : 0 < ρ) (hrank : state.rank ≠ 0)
    (hgood : Good ρ state.capacity W state.tree) :
    ∃ next, state.Advances W next := by
  let U := reduceTree ρ state.capacity W state.tree hρ state.positive hgood
  have ha : ∀ i, i < state.depth → 0 ≤ capacityReserve σ (state.capacity i) :=
    fun i _ => (capacityReserve_pos hσ (state.capacity i)).le
  have hspread := reduceTree_hasSpread ρ state.capacity W state.tree hρ state.positive
    hgood (fun i => capacityReserve σ (state.capacity i)) ha state.spread
  refine state.exists_advance_of_halved W
    (fun hd => hrank ((rank_eq_zero_iff state).mpr hd)) U
    (reduceTree_isDisjoint ρ state.capacity W state.tree hρ state.positive hgood state.disjoint)
    (reduceTree_hasCapacities ρ state.capacity W state.tree hρ state.positive hgood) ?_
    (reduceTree_path_recovery ρ state.capacity W state.tree hρ state.positive hgood)
  exact hspread.mono
    (fun i hi => div_nonneg (ha i hi) (retentionFactor_pos (state.positive i hi)).le)
    (fun i hi => capacityReserve_div_le_half hσ.le (state.positive i hi))

end CoverState

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.ProbabilityTree OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good := @_root_.OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good

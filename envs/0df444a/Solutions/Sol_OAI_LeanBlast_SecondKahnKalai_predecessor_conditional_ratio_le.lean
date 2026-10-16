-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:26:09.77267+00:00
-- url     : https://prove2.me/submissions/c1744e3a-2bff-4fc3-9d46-50529fc051e9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean:L195-L210
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem prob_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.CopyOrbits ----
namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

theorem card_eq_of_mem_copyOrbit {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    J.card = F.card := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact Finset.card_smul_finset _ _

/-- Acting permutes the distinct orbit elements with no multiplicity. -/
theorem sum_copyOrbit_smul (g : G) (F : Finset X) (f : Finset X → ℕ) :
    (∑ J ∈ copyOrbit G F, f (g • J)) = ∑ J ∈ copyOrbit G F, f J := by
  calc
    _ = ∑ J : OrbitCopy G F, f (g • J.val) :=
      (Finset.sum_coe_sort (copyOrbit G F) (fun J => f (g • J))).symm
    _ = ∑ J : OrbitCopy G F, f J.val :=
      (orbitCopyEquiv G g F).sum_comp (fun J : OrbitCopy G F => f J.val)
    _ = _ := Finset.sum_coe_sort (copyOrbit G F) f

theorem containingCopyCount_smul (g : G) (I U : Finset X) :
    containingCopyCount G I (g • U) = containingCopyCount G I U := by
  have h := sum_copyOrbit_smul G g I (fun J => if g • U ⊆ J then 1 else 0)
  simpa only [Finset.smul_finset_subset_smul_finset_iff, Finset.sum_boole,
    Nat.cast_id, containingCopyCount] using h.symm

/-- Positive containment can be pulled back to an actual subset of `I`. -/
theorem exists_pullback_of_containingCopyCount_pos {I U : Finset X}
    (hpos : 0 < containingCopyCount G I U) :
    ∃ V : Finset X, V ⊆ I ∧ U ∈ copyOrbit G V ∧ V.card = U.card := by
  obtain ⟨g, hg⟩ := (containingCopyCount_pos_iff G I U).mp hpos
  refine ⟨g⁻¹ • U, (Finset.subset_smul_finset_iff.mp hg), ?_,
    Finset.card_smul_finset _ _⟩
  exact (mem_copyOrbit_iff G).mpr ⟨g, smul_inv_smul _ _⟩

theorem containmentProb_nonneg (I U : Finset X) : 0 ≤ containmentProb G I U :=
  (copyLaw G I).prob_nonneg _

theorem containmentProb_smul (g : G) (I U : Finset X) :
    containmentProb G I (g • U) = containmentProb G I U := by
  rw [containmentProb_eq_count, containmentProb_eq_count, containingCopyCount_smul]

theorem containmentProb_eq_of_mem_copyOrbit {I F F₀ : Finset X}
    (hF : F₀ ∈ copyOrbit G F) : containmentProb G I F₀ = containmentProb G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hF
  exact containmentProb_smul G g I F

theorem exists_pullback_of_containmentProb_pos {I U : Finset X}
    (hpos : 0 < containmentProb G I U) :
    ∃ V : Finset X, V ⊆ I ∧ U ∈ copyOrbit G V ∧ V.card = U.card := by
  apply exists_pullback_of_containingCopyCount_pos G
  exact (containingCopyCount_pos_iff G I U).mpr ((containmentProb_pos_iff G I U).mp hpos)

end LeanBlast.SecondKahnKalai

end

end OAI

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

section FiniteMaximum

variable {X : Type*}

theorem maximizingSubset_subset (I : Finset X) (score : Finset X → ℝ) :
    maximizingSubset I score ⊆ I :=
  Finset.mem_powerset.mp (exists_powerset_max I score).choose_spec.1

theorem le_maximizingSubset (I : Finset X) (score : Finset X → ℝ)
    {U : Finset X} (hU : U ⊆ I) : score U ≤ score (maximizingSubset I score) :=
  (exists_powerset_max I score).choose_spec.2 U (Finset.mem_powerset.mpr hU)

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

theorem maximizingPredecessor_subset (I : Finset X) (σ : ℝ) :
    maximizingPredecessor G I σ ⊆ I :=
  maximizingSubset_subset I _

theorem predecessorScore_le_max (I : Finset X) (σ : ℝ)
    {S : Finset X} (hS : S ⊆ I) :
    predecessorScore G I σ S ≤ predecessorScore G I σ (maximizingPredecessor G I σ) :=
  le_maximizingSubset I _ hS

theorem one_le_predecessorScore_max (I : Finset X) (σ : ℝ) :
    1 ≤ predecessorScore G I σ (maximizingPredecessor G I σ) := by
  simpa using predecessorScore_le_max G I σ (Finset.empty_subset I)

theorem predecessorScore_eq_of_mem_copyOrbit (σ : ℝ) {I S S₀ : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G S) :
    predecessorScore G I σ S₀ = predecessorScore G I σ S := by
  rw [predecessorScore, predecessorScore,
    containmentProb_eq_of_mem_copyOrbit G hS₀, card_eq_of_mem_copyOrbit G hS₀]

/-- A positive observation pulls back to an actual subset of `I`; zero-probability
observations cannot exceed the empty set's score.  Thus the chosen finite
maximum controls every observed set, not only subsets of the original copy. -/
theorem predecessorScore_le_max_all (I U : Finset X) (σ : ℝ) :
    predecessorScore G I σ U ≤ predecessorScore G I σ (maximizingPredecessor G I σ) := by
  by_cases hzero : containmentProb G I U = 0
  · rw [predecessorScore, hzero, zero_div]
    exact zero_le_one.trans (one_le_predecessorScore_max G I σ)
  · have hpos : 0 < containmentProb G I U :=
      lt_of_le_of_ne (containmentProb_nonneg G I U) (Ne.symm hzero)
    obtain ⟨V, hVI, hcopy, _⟩ := exists_pullback_of_containmentProb_pos G hpos
    rw [predecessorScore_eq_of_mem_copyOrbit G σ hcopy]
    exact predecessorScore_le_max G I σ hVI

theorem predecessor_copy_prob_pos (I : Finset X) (σ : ℝ) {S₀ : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G (maximizingPredecessor G I σ)) :
    0 < containmentProb G I S₀ :=
  containmentProb_pos_of_copy_subset G (maximizingPredecessor_subset G I σ) hS₀

theorem predecessor_conditional_ratio_le (I : Finset X) {σ : ℝ} (hσ : 0 < σ)
    {S₀ J : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G (maximizingPredecessor G I σ))
    (hdisj : Disjoint S₀ J) :
    containmentProb G I (S₀ ∪ J) / containmentProb G I S₀ ≤ σ ^ J.card := by
  have hscore := predecessorScore_le_max_all G I (S₀ ∪ J) σ
  rw [← predecessorScore_eq_of_mem_copyOrbit G σ hS₀] at hscore
  simp only [predecessorScore, Finset.card_union_of_disjoint hdisj, pow_add] at hscore
  have hpowS : 0 < σ ^ S₀.card := pow_pos hσ _
  have hpowJ : 0 < σ ^ J.card := pow_pos hσ _
  have hclear := (div_le_div_iff₀ (mul_pos hpowS hpowJ) hpowS).mp hscore
  have hnum : containmentProb G I (S₀ ∪ J) ≤
      σ ^ J.card * containmentProb G I S₀ := by
    apply (mul_le_mul_iff_right₀ hpowS).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hclear
  exact (div_le_iff₀ (predecessor_copy_prob_pos G I σ hS₀)).mpr hnum

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le := @_root_.OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le

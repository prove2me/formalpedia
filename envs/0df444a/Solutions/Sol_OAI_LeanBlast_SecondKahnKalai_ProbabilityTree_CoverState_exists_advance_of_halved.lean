-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:12:29.716989+00:00
-- url     : https://prove2.me/submissions/58a6a6ff-4d2e-4483-b9f6-ffc994aa2a2a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean:L285-L333
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_zero_prefix_positive_suffix

-- ---- from OAI.Combinatorics.GraphThreshold.ProbabilityTreeTrim ----
namespace OAI

/-! Deterministic removal of initial zero-capacity levels. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai.ProbabilityTree

variable {X : Type}

section Properties

variable [DecidableEq X]

theorem pathUnion_prependChosen {d : ℕ} (T : ProbabilityTree X (d + 1))
    (p : (firstChild T).Path) :
    T.pathUnion (prependChosen T p) = firstLabel T ∪ (firstChild T).pathUnion p := by
  cases T
  rfl

theorem firstChild_isDisjoint {d : ℕ} {T : ProbabilityTree X (d + 1)}
    (hT : T.IsDisjoint) : (firstChild T).IsDisjoint := by
  cases T
  exact hT.2 _

omit [DecidableEq X] in
theorem firstChild_hasCapacities {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstChild T).HasCapacities (fun i => m (i + 1)) := by
  cases T
  exact hT.2 _

theorem firstChild_hasSpread {d : ℕ} {T : ProbabilityTree X (d + 1)} {a : ℕ → ℝ}
    (hT : T.HasSpread a) : (firstChild T).HasSpread (fun i => a (i + 1)) := by
  cases T
  exact hT.2 _

omit [DecidableEq X] in
theorem firstLabel_card_le {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstLabel T).card ≤ m 0 := by
  cases T
  exact hT.1 _

omit [DecidableEq X] in
theorem firstLabel_eq_empty {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (hm : m 0 = 0) : firstLabel T = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := firstLabel_card_le hT
  omega

theorem pathUnion_liftDropPath (k : ℕ) {d : ℕ} (T : ProbabilityTree X (d + k))
    (p : (drop k T).Path) :
    T.pathUnion (liftDropPath k T p) = prefixUnion k T ∪ (drop k T).pathUnion p := by
  induction k generalizing d with
  | zero => simp [liftDropPath, prefixUnion, drop]
  | succ k ih =>
      change T.pathUnion (prependChosen T (liftDropPath k T.firstChild p)) =
        (T.firstLabel ∪ prefixUnion k T.firstChild) ∪ (drop k T.firstChild).pathUnion p
      rw [pathUnion_prependChosen, ih T.firstChild p, Finset.union_assoc]

theorem drop_isDisjoint (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    (hT : T.IsDisjoint) : (drop k T).IsDisjoint := by
  induction k generalizing d with
  | zero => exact hT
  | succ k ih => exact ih (firstChild_isDisjoint hT)

omit [DecidableEq X] in
theorem drop_hasCapacities (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) :
    (drop k T).HasCapacities (fun i => m (i + k)) := by
  induction k generalizing d m with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasCapacities hT)

theorem drop_hasSpread (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {a : ℕ → ℝ} (hT : T.HasSpread a) :
    (drop k T).HasSpread (fun i => a (i + k)) := by
  induction k generalizing d a with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasSpread hT)

theorem prefixUnion_eq_empty_of_capacities (k : ℕ) {d : ℕ}
    {T : ProbabilityTree X (d + k)} {m : ℕ → ℕ} (hT : T.HasCapacities m)
    (hm : ∀ i, i < k → m i = 0) : prefixUnion k T = ∅ := by
  induction k generalizing d m with
  | zero => rfl
  | succ k ih =>
      rw [prefixUnion, firstLabel_eq_empty hT (hm 0 (by omega)), Finset.empty_union]
      exact ih (firstChild_hasCapacities hT) (fun i hi => hm (i + 1) (by omega))

/-- Removing zero-capacity levels preserves every retained full path union exactly. -/
theorem pathUnion_liftDropPath_eq (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) (hm : ∀ i, i < k → m i = 0)
    (p : (drop k T).Path) : T.pathUnion (liftDropPath k T p) = (drop k T).pathUnion p := by
  rw [pathUnion_liftDropPath, prefixUnion_eq_empty_of_capacities k hT hm, Finset.empty_union]

theorem pathUnion_castPath_symm {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (p : (castDepth h T).Path) :
    T.pathUnion ((castPath h T).symm p) = (castDepth h T).pathUnion p := by cases h; rfl

theorem dropPrefix_isDisjoint {d : ℕ} {T : ProbabilityTree X d} (hT : T.IsDisjoint)
    (k : ℕ) (hk : k ≤ d) : (dropPrefix T k hk).IsDisjoint := by
  apply drop_isDisjoint
  simpa using hT

omit [DecidableEq X] in
theorem dropPrefix_hasCapacities {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasCapacities (fun i => m (i + k)) := by
  apply drop_hasCapacities
  simpa using hT

theorem dropPrefix_hasSpread {d : ℕ} {T : ProbabilityTree X d} {a : ℕ → ℝ}
    (hT : T.HasSpread a) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasSpread (fun i => a (i + k)) := by
  apply drop_hasSpread
  simpa using hT

/-- Every path after zero-prefix trimming is an original full path with exactly the same union. -/
theorem pathUnion_liftDropPrefixPath_eq {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d)
    (hm : ∀ i, i < k → m i = 0) (p : (dropPrefix T k hk).Path) :
    T.pathUnion (liftDropPrefixPath T k hk p) = (dropPrefix T k hk).pathUnion p := by
  unfold liftDropPrefixPath
  rw [pathUnion_castPath_symm]
  apply pathUnion_liftDropPath_eq k _ hm
  simpa using hT

end Properties

end LeanBlast.SecondKahnKalai.ProbabilityTree

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.CapacityIteration ----
-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

theorem reducedCapacity_growth {a b : ℕ} (hab : 16 * a ≤ b) (t : ℕ) :
    16 * reducedCapacity a t ≤ reducedCapacity b t := by
  unfold reducedCapacity
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ t)).mpr
  calc
    16 * (a / 2 ^ t) * 2 ^ t = 16 * (a / 2 ^ t * 2 ^ t) := by ring
    _ ≤ 16 * a := Nat.mul_le_mul_left 16 (Nat.div_mul_le_self a (2 ^ t))
    _ ≤ b := hab

theorem successesNeeded_half_lt {m : ℕ} (hhalf : 0 < m / 2) :
    successesNeeded (m / 2) < successesNeeded m := by
  have hm : 2 ≤ m := by omega
  have hl : Nat.log2 m = Nat.log2 (m / 2) + 1 := by
    rw [Nat.log2_def m, ite_eq_left hm]
  simp only [successesNeeded]
  omega

/-- Index monotonicity also holds before an initial zero-capacity segment is
removed. No positivity assumption is needed here. -/
theorem monotoneOn_capacities (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    MonotoneOn m (Set.Iio k) := by
  apply monotoneOn_of_le_succ Set.ordConnected_Iio
  intro j _ _ hj
  have hg := hgrowth j hj
  change m j ≤ m (j + 1)
  omega

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeCovering ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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

/-- Recovery composes through the union of the independent draws. -/
theorem Recovers.trans {d e f : ℕ}
    {T : ProbabilityTree X d} {S : ProbabilityTree X e} {U : ProbabilityTree X f}
    {W V : Finset X} (hTS : Recovers T S W) (hSU : Recovers S U V) :
    Recovers T U (W ∪ V) := by
  intro r
  obtain ⟨q, hq⟩ := hSU r
  obtain ⟨p, hp⟩ := hTS q
  refine ⟨p, ?_⟩
  simpa only [Finset.union_assoc] using
    hp.trans (Finset.union_subset_union (Finset.Subset.refl W) hq)

/-- Removing empty initial labels preserves recovery without adding any
coordinates. The path lifting premise is supplied by deterministic prefix
removal. -/
theorem Recovers.of_pathUnion_eq {d e : ℕ}
    {T : ProbabilityTree X d} {S : ProbabilityTree X e}
    (h : ∀ q : S.Path, ∃ p : T.Path, T.pathUnion p = S.pathUnion q) :
    Recovers T S ∅ := by
  intro q
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, by simp [hp]⟩

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

/-- A halved tree, after its zero prefix is removed, is a strict improvement
of the current positive-capacity tree. -/
theorem exists_advance_of_halved (state : CoverState original σ) (W : Finset X)
    (hdepth : state.depth ≠ 0) (U : ProbabilityTree X state.depth)
    (hdisjoint : U.IsDisjoint)
    (hcapacity : U.HasCapacities (fun i => state.capacity i / 2))
    (hspread : U.HasSpread (fun i => capacityReserve σ (state.capacity i / 2)))
    (hrecovery : Recovers state.tree U W) :
    ∃ next, state.Advances W next := by
  let m : ℕ → ℕ := fun i => state.capacity i / 2
  have hgrowth : ∀ i, i + 1 < state.depth → 16 * m i ≤ m (i + 1) := by
    intro i hi
    simpa [m, reducedCapacity] using reducedCapacity_growth (state.growth i hi) 1
  obtain ⟨j, hj, hzero, hpositive⟩ := exists_zero_prefix_positive_suffix m state.depth
    (monotoneOn_capacities m state.depth hgrowth)
  let V := U.dropPrefix j hj
  have htrim : Recovers U V ∅ := by
    apply Recovers.of_pathUnion_eq
    intro q
    exact ⟨liftDropPrefixPath U j hj q,
      pathUnion_liftDropPrefixPath_eq hcapacity j hj hzero q⟩
  let next : CoverState original σ :=
    { depth := state.depth - j
      tree := V
      capacity := fun i => m (i + j)
      disjoint := dropPrefix_isDisjoint hdisjoint j hj
      capacities := dropPrefix_hasCapacities hcapacity j hj
      spread := dropPrefix_hasSpread hspread j hj
      positive := hpositive
      growth := by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hgrowth (i + j) (by omega)
      seen := state.seen ∪ W
      recovery := by
        simpa only [Finset.union_empty] using (state.recovery.trans hrecovery).trans htrim }
  refine ⟨next, ?_, rfl⟩
  change (if state.depth - j = 0 then 0 else
    successesNeeded (m (state.depth - j - 1 + j))) < state.rank
  by_cases hempty : state.depth - j = 0
  · rw [ite_eq_left hempty]
    exact Nat.pos_of_ne_zero (fun h => hdepth ((rank_eq_zero_iff state).mp h))
  · rw [ite_eq_right hempty]
    have hindex : state.depth - j - 1 + j = state.depth - 1 := by omega
    rw [hindex]
    unfold rank
    rw [ite_eq_right hdepth]
    apply successesNeeded_half_lt
    have hp := hpositive (state.depth - j - 1) (by omega)
    simpa only [hindex] using hp

end CoverState

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.ProbabilityTree OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved := @_root_.OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved

-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.exists_common_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:56:17.819129+00:00
-- url     : https://prove2.me/submissions/25f16f9d-ca8e-4d9e-bf43-e4feff76a6f1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCommonWitness.lean:L56-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.exists_common_witness. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_crossings_eq_profileCrossings
import Theorems.Thm_OAI_TalagrandThreshold_Selector_isClosed_admissible
import Theorems.Thm_OAI_TalagrandThreshold_Selector_maximal_admissible_card_bound
import Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_movedRow_subset_heavySet

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorDefinitionsLemmas ----
namespace OAI

/-! Elementary bounds on the literal truncation scales. -/

namespace TalagrandThreshold.Selector

theorem dscale_pos {s : ℕ} (i : Fin s) : 0 < dscale i := by
  exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)

theorem dscale_lt_one {s : ℕ} (i : Fin s) : dscale i < 1 := by
  exact inv_lt_one_of_one_lt₀
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i.val))

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorProfile ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Exact counts in a selector profile

The full profile records each strict downward move by its final and original
colors. These counting identities hold even without a global `Earlier`
hypothesis: every point counted by a crossing already moves downward.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- Restricting to entries crossing one level cannot increase total size. -/
theorem profileCrossings_le_profileSize (n : Profile s) (i : Fin s) :
    profileCrossings n i ≤ profileSize n := by
  unfold profileCrossings profileSize rowCount
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro h _
  split_ifs <;> omega

end TalagrandThreshold.Selector

end

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

/-- Admissible cutoffs are compact because they are closed and lie in `[0, 1]`. -/
theorem isCompact_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ) :
    IsCompact {u : ℝ | Admissible w A m d u} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).of_isClosed_subset
    (isClosed_admissible w A m d)
  intro u hu
  exact ⟨hu.1, hu.2.1⟩

/-- Every nonempty admissible set has an actual greatest cutoff. -/
theorem exists_greatest_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧ ∀ u, Admissible w A m d u → u ≤ ε := by
  obtain ⟨ε, hε⟩ := (isCompact_admissible w A m d).exists_isGreatest hne
  exact ⟨ε, hε.1, fun _ hu => hε.2 hu⟩

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorTruncation ----
namespace OAI

/-!
# Maximal weighted truncation

This is the maximal truncation lemma used by the multiscale selector. The
cutoff is obtained from the actual compact admissible set. Its heavy-set
bound follows from the exact affine increase on the next interval between
weights, rather than an assumed slope or regularity certificate.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A nonempty admissible set has a greatest cutoff, whose heavy set satisfies
the multiplied cardinality bound. -/
theorem exists_maximal_truncation (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hm : 0 ≤ m) (hd0 : 0 < d) (hd1 : d < 1)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧
      (∀ u, Admissible w A m d u → u ≤ ε) ∧
      d * ((heavySet w ε).card : ℝ) ≤ m := by
  obtain ⟨ε, hε, hmax⟩ := exists_greatest_admissible w A m d hne
  exact ⟨ε, hε, hmax,
    maximal_admissible_card_bound w A m d ε hw hsum hm hd0 hd1 hε hmax⟩

/-- The division form of the maximal truncation lemma. -/
theorem exists_maximal_truncation_div (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hm : 0 ≤ m) (hd0 : 0 < d) (hd1 : d < 1)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧
      (∀ u, Admissible w A m d u → u ≤ ε) ∧
      ((heavySet w ε).card : ℝ) ≤ m / d := by
  obtain ⟨ε, hε, hmax, hcard⟩ :=
    exists_maximal_truncation w A m d hw hsum hm hd0 hd1 hne
  refine ⟨ε, hε, hmax, (le_div_iff₀ hd0).2 ?_⟩
  simpa only [mul_comm] using hcard

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCommonWitness ----
namespace OAI

/-!
# One witness for an entire selector profile group

A nonempty group contains an actual selected move, hence an actual feasible
family member. Its admissibility tests depend on the original coloring only
through the full profile. Maximizing each cutoff for this one member therefore
produces common heavy sets for the entire group. Selected-move minimality puts
every moved row inside its corresponding common heavy set.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private theorem card_le_profile_of_truncation {s : ℕ}
    (R : Finset α) (i : Fin s) (n : Profile s) (m : ℕ)
    (hcard : (R.card : ℝ) ≤ (m : ℝ) / dscale i)
    (hm : m ≤ profileSize n) :
    R.card ≤ 2 ^ (i.val + 1) * profileSize n := by
  have hreal : (R.card : ℝ) ≤ ((m * 2 ^ (i.val + 1) : ℕ) : ℝ) := by
    simpa only [dscale, div_inv_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using hcard
  have hnat : R.card ≤ m * 2 ^ (i.val + 1) := (Nat.cast_le (α := ℝ)).mp hreal
  calc
    R.card ≤ m * 2 ^ (i.val + 1) := hnat
    _ ≤ profileSize n * 2 ^ (i.val + 1) := Nat.mul_le_mul_right _ hm
    _ = 2 ^ (i.val + 1) * profileSize n := Nat.mul_comm _ _

/-- The common witness is constructed from the actual nonempty group; no
additional feasibility, reconstruction, or cardinality certificate is assumed. -/
theorem exists_common_witness {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s)
    (hne : (groupOriginals mu z n).Nonempty) : Nonempty (CommonWitness mu z n) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  have ha₀' := (mem_groupOriginals mu a₀ z n).mp ha₀
  obtain ⟨H₀, hminimal⟩ := ha₀'.2.1
  obtain ⟨H, hfeasible⟩ := hminimal.1.1.2
  have hcross₀ (i : Fin s) : crossings a₀ z i = profileCrossings n i := by
    rw [crossings_eq_profileCrossings, ha₀'.2.2]
  have hcutoff (i : Fin s) : ∃ ε : ℝ,
      Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ) (dscale i) ε ∧
      (∀ u, Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ)
        (dscale i) u → u ≤ ε) ∧
      ((heavySet (mu.weight H) ε).card : ℝ) ≤ (profileCrossings n i : ℝ) / dscale i := by
    apply exists_maximal_truncation_div (mu.weight H) (prefixSet z i)
      (profileCrossings n i : ℝ) (dscale i) (mu.nonneg H) (mu.total H)
      (Nat.cast_nonneg _) (dscale_pos i) (dscale_lt_one i)
    simpa only [hcross₀ i] using hfeasible i
  let ε : Fin s → ℝ := fun i => Classical.choose (hcutoff i)
  have hε (i : Fin s) :
      Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ) (dscale i) (ε i) ∧
      (∀ u, Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ)
        (dscale i) u → u ≤ ε i) ∧
      ((heavySet (mu.weight H) (ε i)).card : ℝ) ≤
        (profileCrossings n i : ℝ) / dscale i :=
    Classical.choose_spec (hcutoff i)
  have hadmissible : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
      Admissible (mu.weight H) (prefixSet z i) (crossings a z i : ℝ) (dscale i) (ε i) := by
    intro a ha i
    have hprofile := ((mem_groupOriginals mu a z n).mp ha).2.2
    rw [crossings_eq_profileCrossings, hprofile]
    exact (hε i).1
  refine ⟨{
    member := H
    cutoff := ε
    admissible := hadmissible
    maximal := fun i => (hε i).2.1
    card_le := ?_
    moved_subset := ?_
  }⟩
  · intro i
    exact card_le_profile_of_truncation (heavySet (mu.weight H) (ε i)) i n
      (profileCrossings n i) (hε i).2.2 (profileCrossings_le_profileSize n i)
  · intro a ha i
    have hselected := ((mem_groupOriginals mu a z n).mp ha).2.1
    have hfeasible' : FeasibleFor mu a z H := fun j => ⟨ε j, hadmissible a ha j⟩
    exact selected_movedRow_subset_heavySet mu a z hselected H hfeasible' i (ε i)
      (hadmissible a ha i)

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.exists_common_witness := @_root_.OAI.TalagrandThreshold.Selector.exists_common_witness

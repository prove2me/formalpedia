-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:11:36.321247+00:00
-- url     : https://prove2.me/submissions/df8b2ae5-25c2-4dfe-9d54-04444aba97ff

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean:L98-L129
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_captured_of_feasible_self
import Theorems.Thm_OAI_TalagrandThreshold_Selector_group_cost_le
import Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_endpoint_cost_grouped
import Theorems.Thm_OAI_TalagrandThreshold_Selector_sum_profile_weights_lt_one_twentieth

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityColors ----
namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α]

theorem colorMass_pos (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 < colorMass p s a := by
  exact Finset.prod_pos fun x _ => colorProb_pos p s hp hs (a x)

variable [DecidableEq α]

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Feasible minima and the actual containment cover

Resetting an original family member to the first color proves existence of
a bounded feasible move. Minimization itself retains the unrestricted
feasibility witness from `Feasible`; the witness need not be that member.
All retained minima contribute their actual changed sets to a cover.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

theorem Selected.feasible {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) : Feasible mu a z := by
  obtain ⟨H₀, hz⟩ := hz
  exact hz.1.1

theorem Selected.earlier {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) : Earlier a z := hz.feasible.1

omit [DecidableEq α] in
/-- An earlier move with no changed vertex is the unchanged coloring. -/
theorem eq_of_changes_eq_empty {a z : Coloring α s} (hz : Earlier a z)
    (hempty : changes a z = ∅) : z = a := by
  funext x
  apply le_antisymm (hz x)
  apply le_of_not_gt
  intro hlt
  have hx : x ∈ changes a z := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩
  rw [hempty] at hx
  exact Finset.notMem_empty x hx

theorem Selected.changes_nonempty {mu : MassFamily F} {a z : Coloring α s}
    (hz : Selected mu a z) (ha : Bad mu a) : (changes a z).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hza : z = a := eq_of_changes_eq_empty hz.earlier hempty
  have hself : Feasible mu a a := by simpa only [hza] using hz.feasible
  exact ha (captured_of_feasible_self hself)

end TalagrandThreshold.Selector

end

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

omit [DecidableEq α] in
/-- The last color cannot be the final color of a strict downward move. -/
theorem changes_filter_last (a z : Coloring α s) :
    (changes a z).filter (fun x => z x = Fin.last s) = ∅ := by
  ext x
  simp only [Finset.mem_filter, changes, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  intro hmove hlast
  have hlt : (z x).val < (a x).val := hmove
  have hz : (z x).val = s := congrArg Fin.val hlast
  have ha := (a x).isLt
  omega

omit [DecidableEq α] in
/-- The nonterminal final-color fibers are exactly the moved rows. -/
theorem changes_filter_castSucc (a z : Coloring α s) (i : Fin s) :
    (changes a z).filter (fun x => z x = i.castSucc) = movedRow a z i := by
  ext x
  simp only [Finset.mem_filter, changes, movedRow, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hmove, hz⟩
    exact ⟨congrArg Fin.val hz, hmove⟩
  · rintro ⟨hz, hmove⟩
    exact ⟨hmove, Fin.ext hz⟩

omit [DecidableEq α] in
/-- Every changed point has exactly one nonterminal final color. -/
theorem profileSize_profile (a z : Coloring α s) :
    profileSize (profile a z) = (changes a z).card := by
  have hpartition :
      (∑ h : Color s, ((changes a z).filter fun x => z x = h).card) =
        (changes a z).card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (changes a z) Finset.univ z
  rw [Fin.sum_univ_castSucc, changes_filter_last, Finset.card_empty,
    add_zero] at hpartition
  simp_rw [changes_filter_castSucc] at hpartition
  simpa only [profileSize, rowCount_profile] using hpartition

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCost ----
namespace OAI

/-!
# The global cost of actual selected moves

Partition selected pairs first by their final coloring and then by their
full profile. The profile estimate removes the profile-dependent heavy
sets before summation. Word-count normalization and the finite geometric
bound then give the strict budget under the actual coloring law.
-/

noncomputable section

open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- A selected move from a bad coloring has a nonzero tuple of row sizes. -/
theorem selectedProfiles_rowCount_ne_zero (mu : MassFamily F)
    (z : Coloring α s) (n : Profile s) (hn : n ∈ selectedProfiles mu z) :
    rowCount n ≠ 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hbad, hselected⟩ := (mem_selectedOriginals mu a z).mp ha
  intro hz
  have hpos := Finset.card_pos.mpr (hselected.changes_nonempty hbad)
  rw [← profileSize_profile a z] at hpos
  simp only [profileSize, hz, Pi.zero_apply, Finset.sum_const_zero,
    lt_self_iff_false] at hpos

/-- All actual original colorings for one endpoint fit its probability-weighted budget. -/
theorem selected_endpoint_cost_lt (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2)
    (z : Coloring α s) :
    (∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) <
      colorMass p s z * (1 / 20) := by
  classical
  calc
    (∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) =
        ∑ n ∈ selectedProfiles mu z,
          ∑ a ∈ groupOriginals mu z n, colorMass p s a * p ^ (changes a z).card :=
      selected_endpoint_cost_grouped mu z _
    _ ≤ ∑ n ∈ selectedProfiles mu z,
        colorMass p s z *
          (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
          (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
            ∏ h : Color s, colorProb p s h ^ (n i h))) :=
      Finset.sum_le_sum fun n _ => group_cost_le mu p s hp hs z n
    _ = colorMass p s z *
        (∑ n ∈ selectedProfiles mu z,
          (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
          (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
            ∏ h : Color s, colorProb p s h ^ (n i h)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      exact mul_assoc _ _ _
    _ < colorMass p s z * (1 / 20) :=
      mul_lt_mul_of_pos_left
        (sum_profile_weights_lt_one_twentieth p s hp hs (selectedProfiles mu z)
          (selectedProfiles_rowCount_ne_zero mu z))
        (colorMass_pos p s hp hs z)

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt := @_root_.OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt

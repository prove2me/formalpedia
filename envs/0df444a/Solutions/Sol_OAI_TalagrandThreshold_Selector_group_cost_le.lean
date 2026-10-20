-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.group_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:03:29.051659+00:00
-- url     : https://prove2.me/submissions/85e2e93c-4516-443b-812f-0842cfb9e228

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGroupCost.lean:L93-L121
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.group_cost_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_exists_common_witness
import Theorems.Thm_OAI_TalagrandThreshold_Selector_profile_group_cost_le

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

theorem colorMass_nonneg (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 ≤ colorMass p s a :=
  (colorMass_pos p s hp hs a).le

variable [DecidableEq α]

end TalagrandThreshold

end

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

/-- The finite sets needed for counting are common to the whole actual group. -/
theorem exists_common_heavy_sets {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s)
    (hne : (groupOriginals mu z n).Nonempty) :
    ∃ R : Fin s → Finset α,
      (∀ i, (R i).card ≤ 2 ^ (i.val + 1) * profileSize n) ∧
      ∀ a ∈ groupOriginals mu z n, ∀ i, movedRow a z i ⊆ R i := by
  obtain ⟨w⟩ := exists_common_witness mu z n hne
  exact ⟨fun i => heavySet (mu.weight w.member) (w.cutoff i), w.card_le, w.moved_subset⟩

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGroupCost ----
namespace OAI

/-!
# The actual contribution of one full selector profile

The common heavy sets are obtained separately for each occurring profile.
The entropy estimate removes their sizes before profiles are summed, so no
uniform choice of heavy sets across distinct profiles is required.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The contribution of an actual selected profile. All reconstruction and
counting premises are discharged by the concrete selector construction. -/
theorem group_cost_le {F : Family α} (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2)
    (z : Coloring α s) (n : Profile s) :
    (∑ a ∈ groupOriginals mu z n, colorMass p s a * p ^ (changes a z).card) ≤
      colorMass p s z *
        (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
        (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
          ∏ h : Color s, colorProb p s h ^ (n i h))) := by
  classical
  by_cases hne : (groupOriginals mu z n).Nonempty
  · obtain ⟨R, hR, hrows⟩ := exists_common_heavy_sets mu z n hne
    apply profile_group_cost_le p s hp hs (groupOriginals mu z n) z n R
    · intro a ha
      have h := (Finset.mem_filter.mp ha).2
      obtain ⟨H₀, hmin⟩ := h.2.1
      exact hmin.1.1.1
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.2.2
    · exact hrows
    · exact hR
  · have hempty : groupOriginals mu z n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg (colorMass_nonneg p s hp hs z)
        (Finset.prod_nonneg fun i _ => pow_nonneg (by positivity) _))
      (Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun h _ => pow_nonneg (colorProb_nonneg p s hp hs h) _))

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.group_cost_le := @_root_.OAI.TalagrandThreshold.Selector.group_cost_le

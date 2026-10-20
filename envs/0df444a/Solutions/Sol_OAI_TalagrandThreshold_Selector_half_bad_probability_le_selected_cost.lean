-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.half_bad_probability_le_selected_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:15:15.153389+00:00
-- url     : https://prove2.me/submissions/59af6470-e92e-48f3-b381-01a24453076b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorMain.lean:L27-L45
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.half_bad_probability_le_selected_cost. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_reset_feasibleFor

-- ---- from OAI.Combinatorics.ExpectationThreshold.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] in
theorem cost_image_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Finset α) :
    cost p (T.image G) ≤ ∑ i ∈ T, p ^ (G i).card := by
  exact Finset.sum_image_le_of_nonneg (fun S _ => pow_nonneg hp S.card)

omit [Fintype α] [DecidableEq α] in
theorem cost_gt_of_not_small {F G : Family α} {p : ℝ}
    (h : ¬ Small p F) (hG : Covers G F) : 1 / 2 < cost p G :=
  lt_of_not_ge (fun hc => h ⟨G, hG, hc⟩)

end
end TalagrandThreshold

end OAI

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

omit [Fintype α] in
theorem reset_earlier (a : Coloring α s) (H₀ : ↥F) :
    Earlier a (reset a H₀) := by
  intro x
  by_cases hx : x ∈ H₀.val
  · simp [reset, hx]
  · simp [reset, hx]

theorem changes_reset_subset (a : Coloring α s) (H₀ : ↥F) :
    changes a (reset a H₀) ⊆ H₀.val := by
  intro x hx
  by_contra hnot
  have hlt := (Finset.mem_filter.mp hx).2
  simp [reset, hnot] at hlt

theorem reset_boundedFeasible (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    BoundedFeasible mu a H₀ (reset a H₀) :=
  ⟨⟨reset_earlier a H₀, H₀, reset_feasibleFor mu a H₀⟩, changes_reset_subset a H₀⟩

/-- A minimum exists for every member, without restricting its witness. -/
theorem exists_isMinimalMove (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    ∃ z, IsMinimalMove mu a H₀ z := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ z : Coloring α s, BoundedFeasible mu a H₀ z ∧ movement a z = k
  have hex : ∃ k, P k :=
    ⟨movement a (reset a H₀), reset a H₀, reset_boundedFeasible mu a H₀, rfl⟩
  obtain ⟨z, hz, hcost⟩ := Nat.find_spec hex
  refine ⟨z, hz, ?_⟩
  intro w hw
  rw [hcost]
  exact Nat.find_min' hex ⟨w, hw, rfl⟩

theorem selectedChanges_covers (mu : MassFamily F) (a : Coloring α s) :
    Covers (selectedChanges mu a) F := by
  classical
  intro H hH
  obtain ⟨z, hz⟩ := exists_isMinimalMove mu a ⟨H, hH⟩
  refine ⟨changes a z, ?_, hz.1.2⟩
  exact Finset.mem_image.mpr
    ⟨z, mem_selectedMoves.mpr ⟨⟨H, hH⟩, hz⟩, rfl⟩

/-- The sum over selected colorings dominates the cost with duplicates removed. -/
theorem half_lt_selectedMoves_cost (mu : MassFamily F) (a : Coloring α s)
    {p : ℝ} (hp : 0 ≤ p) (hF : ¬ Small p F) :
    (1 / 2 : ℝ) < ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card := by
  classical
  exact (cost_gt_of_not_small hF (selectedChanges_covers mu a)).trans_le
    (cost_image_le hp (selectedMoves mu a) (changes a))

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorMain ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# The simultaneous multiscale selector

The actual minimum-move cover bounds the bad probability from below by its
weighted cost. The profile reconstruction and counting theorem bounds that
same cost from above. Both conclusions use the literal independent color law.
-/

noncomputable section
open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected changed sets give the cover-cost inequality. -/
theorem half_bad_probability_le_selected_cost {F : Family α}
    (mu : MassFamily F) (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (hF : ¬ Small p F) :
    (1 / 2 : ℝ) * (coloringLaw (α := α) p s hp hs).prob (Bad mu) ≤
      ∑ a : Coloring α s, if Bad mu a then
        colorMass p s a * ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card
      else 0 := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Bad mu a
  · simp only [ite_eq_left ha, coloringLaw_weight]
    have hcover := (half_lt_selectedMoves_cost mu a hp.le hF).le
    have hmass := colorMass_nonneg p s hp hs a
    nlinarith
  · simp only [ite_eq_right ha, mul_zero, le_refl]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.half_bad_probability_le_selected_cost := @_root_.OAI.TalagrandThreshold.Selector.half_bad_probability_le_selected_cost

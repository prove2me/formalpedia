-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.crossings_eq_profileCrossings
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:39:56.467004+00:00
-- url     : https://prove2.me/submissions/28cbc53e-6e3c-4727-ac67-45d9b5c1bddd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorProfile.lean:L112-L178
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.crossings_eq_profileCrossings. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorProfile ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- The full profile determines every actual crossing count. -/
theorem crossings_eq_profileCrossings (a z : Coloring α s) (i : Fin s) :
    crossings a z i = profileCrossings (profile a z) i := by
  classical
  let C := prefixSet z i \ prefixSet a i
  have hC (x : α) :
      x ∈ C ↔ (z x).val ≤ i.val ∧ i.val < (a x).val := by
    simp [C, prefixSet, not_le]
  have hsplit :
      C.card = ∑ j : Color s, ∑ h : Color s,
        (C.filter fun x => z x = j ∧ a x = h).card := by
    calc
      C.card = ∑ j : Color s, (C.filter fun x => z x = j).card :=
        Finset.card_eq_sum_card_fiberwise
          (s := C) (t := (Finset.univ : Finset (Color s))) (f := z)
          (fun _ _ => Finset.mem_univ _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Finset.filter_filter] using
          (Finset.card_eq_sum_card_fiberwise
            (s := C.filter fun x => z x = j)
            (t := (Finset.univ : Finset (Color s))) (f := a)
            (fun _ _ => Finset.mem_univ _))
  have hcell (j h : Color s) :
      (C.filter fun x => z x = j ∧ a x = h) =
        if j.val ≤ i.val ∧ i.val < h.val then
          Finset.univ.filter (fun x =>
            (z x).val = j.val ∧ a x = h ∧ j.val < h.val)
        else ∅ := by
    by_cases hc : j.val ≤ i.val ∧ i.val < h.val
    · rw [ite_eq_left hc]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hz, ha⟩
        exact ⟨congrArg Fin.val hz, ha, lt_of_le_of_lt hc.1 hc.2⟩
      · rintro ⟨hz, ha, _⟩
        have hz' : z x = j := Fin.ext hz
        refine ⟨(hC x).mpr ?_, hz', ha⟩
        simpa only [hz', ha] using hc
    · rw [ite_eq_right hc]
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hpair
      rcases hpair with ⟨hz, ha⟩
      apply hc
      simpa only [hz, ha] using (hC x).mp hx
  have hlast :
      (∑ h : Color s,
        (C.filter fun x => z x = Fin.last s ∧ a x = h).card) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    rw [hcell]
    have hnot : ¬ (Fin.last s).val ≤ i.val :=
      Nat.not_le.mpr i.isLt
    simp only [hnot, false_and, ite_false, Finset.card_empty]
  change C.card = _
  rw [hsplit, Fin.sum_univ_castSucc, hlast, add_zero]
  unfold profileCrossings
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  rw [hcell]
  by_cases hc : j.val ≤ i.val ∧ i.val < h.val
  · simp only [Fin.val_castSucc, ite_eq_left hc, profile]
  · simp only [Fin.val_castSucc, ite_eq_right hc, Finset.card_empty]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.crossings_eq_profileCrossings := @_root_.OAI.TalagrandThreshold.Selector.crossings_eq_profileCrossings

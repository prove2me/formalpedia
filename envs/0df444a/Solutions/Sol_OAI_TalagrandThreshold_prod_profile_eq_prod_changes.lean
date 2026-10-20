-- Prove2me | solution 1 for OAI.TalagrandThreshold.prod_profile_eq_prod_changes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:59:10.652621+00:00
-- url     : https://prove2.me/submissions/d2a20adb-6f07-4419-a2e8-82a284910f4a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityLikelihood.lean:L29-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.prod_profile_eq_prod_changes. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityLikelihood ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Likelihood of an actual move of colors

The full guarded profile records every changed coordinate exactly once.
Grouping the coordinate likelihood factors by that profile gives the precise
ratio used by the selector estimate.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold

open Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- Group a product over changed vertices by the actual full profile. -/
theorem prod_profile_eq_prod_changes (a z : Coloring α s)
    (F : Color s → Color s → ℝ) :
    (∏ i : Fin s, ∏ h : Color s, F i.castSucc h ^ profile a z i h) =
      ∏ x ∈ changes a z, F (z x) (a x) := by
  classical
  let n (c h : Color s) : ℕ :=
    (Finset.univ.filter
      (fun x : α => z x = c ∧ a x = h ∧ c.val < h.val)).card
  have hfiber (c h : Color s) :
      (changes a z).filter (fun x => (z x, a x) = (c, h)) =
        Finset.univ.filter
          (fun x : α => z x = c ∧ a x = h ∧ c.val < h.val) := by
    ext x
    simp only [changes, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
      Fin.lt_def]
    constructor
    · rintro ⟨hx, hz, ha⟩
      exact ⟨hz, ha, by simpa only [hz, ha] using hx⟩
    · rintro ⟨hz, ha, hch⟩
      exact ⟨by simpa only [hz, ha] using hch, hz, ha⟩
  have hgroup :
      (∏ c : Color s, ∏ h : Color s, F c h ^ n c h) =
        ∏ x ∈ changes a z, F (z x) (a x) := by
    calc
      _ = ∏ ch : Color s × Color s,
          F ch.1 ch.2 ^
            ((changes a z).filter (fun x => (z x, a x) = ch)).card := by
        rw [Fintype.prod_prod_type]
        apply Finset.prod_congr rfl
        intro c _
        apply Finset.prod_congr rfl
        intro h _
        rw [hfiber c h]
      _ = ∏ x ∈ changes a z, F (z x) (a x) := by
        simpa only [Finset.prod_const] using
          (Finset.prod_fiberwise' (changes a z)
            (fun x => (z x, a x))
            (fun ch : Color s × Color s => F ch.1 ch.2))
  have hlast : (∏ h : Color s, F (Fin.last s) h ^ n (Fin.last s) h) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    have hnot : ¬ (Fin.last s).val < h.val :=
      Nat.not_lt_of_ge (Nat.le_of_lt_succ h.isLt)
    simp only [n, hnot, and_false, Finset.filter_false, Finset.card_empty, pow_zero]
  have hcount (i : Fin s) (h : Color s) : n i.castSucc h = profile a z i h := by
    simp only [n, profile, Fin.ext_iff, Fin.val_castSucc]
  rw [Fin.prod_univ_castSucc, hlast, mul_one] at hgroup
  simpa only [hcount] using hgroup

end TalagrandThreshold

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators
open Selector


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.prod_profile_eq_prod_changes := @_root_.OAI.TalagrandThreshold.prod_profile_eq_prod_changes

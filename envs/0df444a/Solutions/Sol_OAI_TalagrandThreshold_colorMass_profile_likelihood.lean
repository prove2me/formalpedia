-- Prove2me | solution 1 for OAI.TalagrandThreshold.colorMass_profile_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:00:13.790621+00:00
-- url     : https://prove2.me/submissions/066c1e24-e554-497a-9282-e7a4015ddc62

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityLikelihood.lean:L90-L143
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.colorMass_profile_likelihood. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_prod_profile_eq_prod_changes

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityLikelihood ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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
/-- The profile exponent is the product of one p-factor per actual changed vertex. -/
theorem pow_profileSize_eq_prod_changes (p : ℝ) (a z : Coloring α s) :
    p ^ profileSize (profile a z) = ∏ _x ∈ changes a z, p := by
  calc
    _ = ∏ i : Fin s, ∏ h : Color s, p ^ profile a z i h := by
      simp only [Finset.prod_pow_eq_pow_sum, profileSize, rowCount]
    _ = ∏ _x ∈ changes a z, p :=
      prod_profile_eq_prod_changes a z (fun _ _ => p)

omit [DecidableEq α] in
/-- Exact likelihood regrouping for the original independent color law and an
actual move to earlier colors. Each source row retains all original-color counts. -/
theorem colorMass_profile_likelihood (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a z : Coloring α s) (haz : Selector.Earlier a z) :
    p ^ Selector.profileSize (Selector.profile a z) * colorMass p s a =
      colorMass p s z * ∏ i : Fin s,
        ((p / colorProb p s i.castSucc) ^ Selector.rowCount (Selector.profile a z) i *
          ∏ h : Color s, (colorProb p s h) ^ Selector.profile a z i h) := by
  classical
  have hpowers : p ^ profileSize (profile a z) =
      ∏ x : α, if z x < a x then p else 1 := by
    calc
      _ = ∏ _x ∈ changes a z, p := pow_profileSize_eq_prod_changes p a z
      _ = ∏ x : α, if z x < a x then p else 1 :=
        Finset.prod_filter (fun x => z x < a x) (fun _ => p)
  have hratios :
      (∏ x ∈ changes a z, (p / colorProb p s (z x)) * colorProb p s (a x)) =
        ∏ x : α, if z x < a x then
          (p / colorProb p s (z x)) * colorProb p s (a x) else 1 :=
    Finset.prod_filter (fun x => z x < a x)
      (fun x => (p / colorProb p s (z x)) * colorProb p s (a x))
  have hpoint (x : α) :
      (if z x < a x then p else 1) * colorProb p s (a x) =
        colorProb p s (z x) * (if z x < a x then
          (p / colorProb p s (z x)) * colorProb p s (a x) else 1) := by
    by_cases h : z x < a x
    · rw [ite_eq_left h, ite_eq_left h, ← mul_assoc,
        mul_div_cancel₀ p (ne_of_gt (colorProb_pos p s hp hs (z x)))]
    · have heq : z x = a x := le_antisymm (haz x) (le_of_not_gt h)
      simp only [heq, lt_self_iff_false, ite_false, one_mul, mul_one]
  calc
    _ = ∏ x : α, (if z x < a x then p else 1) * colorProb p s (a x) := by
      rw [hpowers, colorMass, Finset.prod_mul_distrib]
    _ = ∏ x : α, colorProb p s (z x) * (if z x < a x then
        (p / colorProb p s (z x)) * colorProb p s (a x) else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      exact hpoint x
    _ = colorMass p s z *
        ∏ x ∈ changes a z, (p / colorProb p s (z x)) * colorProb p s (a x) := by
      rw [Finset.prod_mul_distrib, ← hratios, colorMass]
    _ = colorMass p s z *
        ∏ i : Fin s, ∏ h : Color s,
          ((p / colorProb p s i.castSucc) * colorProb p s h) ^ profile a z i h := by
      rw [prod_profile_eq_prod_changes a z
        (fun c h => (p / colorProb p s c) * colorProb p s h)]
    _ = colorMass p s z * ∏ i : Fin s,
        ((p / colorProb p s i.castSucc) ^ rowCount (profile a z) i *
          ∏ h : Color s, (colorProb p s h) ^ profile a z i h) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, rowCount]

end TalagrandThreshold

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators
open Selector


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.colorMass_profile_likelihood := @_root_.OAI.TalagrandThreshold.colorMass_profile_likelihood

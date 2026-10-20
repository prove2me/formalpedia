-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:08:07.440671+00:00
-- url     : https://prove2.me/submissions/4ee407eb-076f-4886-a146-afae590c11d0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCostProfiles.lean:L20-L69
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_sum_prod_wordCount_weight_le_one
import Theorems.Thm_OAI_TalagrandThreshold_tuple_geometric_sum_lt_one_twentieth

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCostProfiles ----
namespace OAI

/-!
# Summing the full-profile weights

The reconstruction sets may depend on the entire profile. Once their counting
bound has been replaced by the uniform entropy bound, the remaining full
profiles can be grouped by row counts. The literal word-count weights have
total mass at most one within each such group.
-/

open scoped BigOperators

namespace TalagrandThreshold.Selector

/-- The full-profile sum satisfies the selector budget for any finite family
whose row-count vectors are nonzero. No independence of the rows of the
profile family is required. -/
theorem sum_profile_weights_lt_one_twentieth (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (N : Finset (Profile s))
    (hN : ∀ n ∈ N, rowCount n ≠ 0) :
    (∑ n ∈ N,
      (∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (rowCount n i)) *
      (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
        ∏ h : Color s, colorProb p s h ^ (n i h)))) < 1 / 20 := by
  classical
  let c : (Fin s → ℕ) → ℝ := fun t =>
    ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)
  let w : (Fin s → ℕ) → Profile s → ℝ := fun t n =>
    ∏ i : Fin s, ((wordCount (t i) (n i) : ℝ) *
      ∏ h : Color s, colorProb p s h ^ (n i h))
  let T : Finset (Fin s → ℕ) := N.image rowCount
  have hc (t : Fin s → ℕ) : 0 ≤ c t := by
    exact Finset.prod_nonneg fun i _ =>
      pow_nonneg (div_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) _
  have hfiber (t : Fin s → ℕ) :
      (∑ n ∈ N.filter (fun n => rowCount n = t),
        c (rowCount n) * w (rowCount n) n) ≤ c t := by
    have hw : (∑ n ∈ N.filter (fun n => rowCount n = t), w t n) ≤ 1 :=
      sum_prod_wordCount_weight_le_one t (N.filter (fun n => rowCount n = t))
        (colorProb p s) (colorProb_nonneg p s hp hs) (sum_colorProb p s).le
    calc
      (∑ n ∈ N.filter (fun n => rowCount n = t),
          c (rowCount n) * w (rowCount n) n) =
          c t * ∑ n ∈ N.filter (fun n => rowCount n = t), w t n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ ≤ c t * 1 := mul_le_mul_of_nonneg_left hw (hc t)
      _ = c t := mul_one _
  have hT : ∀ t ∈ T, t ≠ 0 := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact hN n hn
  change (∑ n ∈ N, c (rowCount n) * w (rowCount n) n) < 1 / 20
  calc
    (∑ n ∈ N, c (rowCount n) * w (rowCount n) n) =
        ∑ t ∈ T, ∑ n ∈ N.filter (fun n => rowCount n = t),
          c (rowCount n) * w (rowCount n) n :=
      (Finset.sum_fiberwise_of_maps_to
        (fun n hn => Finset.mem_image_of_mem rowCount hn)
        (fun n => c (rowCount n) * w (rowCount n) n)).symm
    _ ≤ ∑ t ∈ T, c t := Finset.sum_le_sum fun t _ => hfiber t
    _ < 1 / 20 := tuple_geometric_sum_lt_one_twentieth T hT

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth := @_root_.OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth

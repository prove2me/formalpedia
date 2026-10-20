-- Prove2me | solution 1 for OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:04:24.683422+00:00
-- url     : https://prove2.me/submissions/6e1ae43a-9ed0-40f3-9483-c3451a73aa3e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWordsProducts.lean:L48-L76
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_sum_wordCount_weight

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingWords ----
namespace OAI

/-!
# Counting finite words by their color profiles

The coefficient attached to a profile is the actual cardinality of its fiber
among finite words. Regrouping the weighted sum over words proves the finite
multinomial identity without introducing a factorial formula or a counting
hypothesis.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem mem_wordProfiles_iff (t : ℕ) (n : H → ℕ) :
    n ∈ wordProfiles H t ↔ ∃ f : Fin t → H, wordProfile f = n := by
  simp only [wordProfiles, Finset.mem_image, Finset.mem_univ, true_and]

theorem wordCount_eq_zero_of_not_mem_wordProfiles (t : ℕ) (n : H → ℕ)
    (hn : n ∉ wordProfiles H t) : wordCount t n = 0 := by
  unfold wordCount wordFiber
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro f _ hf
  exact hn ((mem_wordProfiles_iff t n).mpr ⟨f, hf⟩)

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingWordsProducts ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

namespace OAI

/-!
# Products of counting-word weights

An arbitrary finite collection of row profiles has total counting-word weight
at most one when the nonnegative color weights have total mass at most one.
The coefficients are the actual cardinalities of words with each profile.
-/

open scoped BigOperators

namespace TalagrandThreshold

private theorem sum_prod_le_prod_sum_of_support {I A : Type*} [Fintype I]
    (S : I → Finset A) (w : I → A → ℝ)
    (hw : ∀ i a, 0 ≤ w i a)
    (hz : ∀ i a, a ∉ S i → w i a = 0) (E : Finset (I → A)) :
    (∑ n ∈ E, ∏ i, w i (n i)) ≤ ∏ i, ∑ a ∈ S i, w i a := by
  classical
  let P : Finset (I → A) := Fintype.piFinset S
  have hzero (n : I → A) (hn : n ∉ P) : (∏ i, w i (n i)) = 0 := by
    have hn' : ¬ ∀ i, n i ∈ S i := by
      simpa only [P, Fintype.mem_piFinset] using hn
    obtain ⟨i, hi⟩ := not_forall.mp hn'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i (n i) hi)
  calc
    (∑ n ∈ E, ∏ i, w i (n i)) = ∑ n ∈ E ∩ P, ∏ i, w i (n i) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro n hn hnot
      apply hzero n
      intro hnP
      exact hnot (Finset.mem_inter.mpr ⟨hn, hnP⟩)
    _ ≤ ∑ n ∈ P, ∏ i, w i (n i) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun n _ _ => Finset.prod_nonneg fun i _ => hw i (n i))
    _ = ∏ i, ∑ a ∈ S i, w i a := (Finset.prod_univ_sum S w).symm

/-- Summing the literal counting-word weights over any finite set of row
profiles is bounded by one. Neither the row type nor the color type needs
to be nonempty. -/
theorem sum_prod_wordCount_weight_le_one {I H : Type*} [Fintype I]
    [Fintype H] [DecidableEq H] (t : I → ℕ) (E : Finset (I → H → ℕ))
    (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h) (hπsum : (∑ h, π h) ≤ 1) :
    (∑ n ∈ E, ∏ i, ((wordCount (t i) (n i) : ℝ) * ∏ h, π h ^ (n i h))) ≤ 1 := by
  classical
  have hπsum_nonneg : 0 ≤ ∑ h, π h := Finset.sum_nonneg fun h _ => hπ h
  calc
    (∑ n ∈ E, ∏ i, ((wordCount (t i) (n i) : ℝ) * ∏ h, π h ^ (n i h))) ≤
        ∏ i, ∑ n ∈ wordProfiles H (t i),
          (wordCount (t i) n : ℝ) * ∏ h, π h ^ (n h) := by
      refine sum_prod_le_prod_sum_of_support (I := I) (A := H → ℕ)
        (fun i => wordProfiles H (t i))
        (fun i (n : H → ℕ) => (wordCount (t i) n : ℝ) * ∏ h, π h ^ n h) ?_ ?_ E
      · intro i n
        exact mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun h _ => pow_nonneg (hπ h) _)
      · intro i n hn
        rw [wordCount_eq_zero_of_not_mem_wordProfiles (t i) n hn]
        simp
    _ = ∏ i, (∑ h, π h) ^ (t i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_wordCount_weight (t i) π
    _ ≤ 1 := Finset.prod_le_one₀
      (fun i _ => pow_nonneg hπsum_nonneg (t i))
      (fun _ _ => pow_le_one₀ hπsum_nonneg hπsum)

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one := @_root_.OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one

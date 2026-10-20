-- Prove2me | solution 1 for OAI.TalagrandThreshold.card_rowEncoding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:39:15.280609+00:00
-- url     : https://prove2.me/submissions/95811a70-4043-4dc6-a6d4-fa8869557837

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingRows.lean:L42-L62
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.card_rowEncoding. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingWordsTransport ----
namespace OAI

/-!
# Transport of words with a prescribed profile

Reindexing the domain of a word preserves every letter count. Consequently,
the number of words with a prescribed profile depends only on the size of
the domain, including when that domain is the subtype of a finite set.
-/

namespace TalagrandThreshold

section Profile

variable {D E H : Type*} [Fintype D] [Fintype E] [DecidableEq H]

end Profile

section Fiber

variable {D E H : Type*} [Fintype D] [Fintype E]
variable [DecidableEq D] [DecidableEq E] [Fintype H] [DecidableEq H]

/-- Equivalent finite domains have equally many words of each profile. -/
theorem wordFiber_card_eq_of_equiv (e : D ≃ E) (n : H → ℕ) :
    (wordFiber D n).card = (wordFiber E n).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (wordFiberEquiv e n)

end Fiber

/-- Labels on a finite set are counted by the word count for its cardinality. -/
theorem wordFiber_finset_card {α H : Type*} [DecidableEq α]
    [Fintype H] [DecidableEq H] (U : Finset α) (n : H → ℕ) :
    (wordFiber ↥U n).card = wordCount U.card n := by
  change (wordFiber ↥U n).card = (wordFiber (Fin U.card) n).card
  exact wordFiber_card_eq_of_equiv U.equivFin n

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncodingRows ----
namespace OAI

/-!
# Counting row encodings

A row encoding chooses a subset of the available positions and labels those
positions with a word of a prescribed profile. The word count depends only on
the number of chosen positions, so the total count factors into a binomial
coefficient and the corresponding word count.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α H : Type*} [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]

/-- The number of subsets of `R` with exactly `t` elements. -/
theorem card_fixedSize_subsets (R : Finset α) (t : ℕ) :
    Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} =
      Nat.choose R.card t := by
  calc
    Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} =
        (R.powersetCard t).card :=
      Fintype.card_of_subtype (R.powersetCard t)
        (fun _ => Finset.mem_powersetCard)
    _ = Nat.choose R.card t := Finset.card_powersetCard t R

/-- Each chosen set admits the same number of words, so the count factors. -/
theorem card_rowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) :
    Fintype.card (RowEncoding R t n) = Nat.choose R.card t * wordCount t n := by
  classical
  change Fintype.card
    (Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)) = _
  rw [Fintype.card_sigma]
  have hFiber (U : {U : Finset α // U ⊆ R ∧ U.card = t}) :
      Fintype.card ↥(wordFiber ↥U.val n) = wordCount t n := by
    rw [Fintype.card_coe, wordFiber_finset_card, U.property.2]
  calc
    (∑ U : {U : Finset α // U ⊆ R ∧ U.card = t},
        Fintype.card ↥(wordFiber ↥U.val n)) =
        Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} * wordCount t n := by
      simpa only [Finset.card_univ] using
        (Finset.sum_const_nat (s := Finset.univ)
          (f := fun U : {U : Finset α // U ⊆ R ∧ U.card = t} =>
            Fintype.card ↥(wordFiber ↥U.val n))
          (m := wordCount t n) (fun U _ => hFiber U))
    _ = Nat.choose R.card t * wordCount t n := by
      rw [card_fixedSize_subsets]

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.card_rowEncoding := @_root_.OAI.TalagrandThreshold.card_rowEncoding

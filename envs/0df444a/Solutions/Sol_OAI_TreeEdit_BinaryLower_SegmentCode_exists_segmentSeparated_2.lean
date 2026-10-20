-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:04:34.718793+00:00
-- url     : https://prove2.me/submissions/77435770-de57-4fd1-8946-7a1c4a848871

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean:L80-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Theorems.Thm_OAI_TreeEdit_BinaryLower_CodeUnionBound_exists_avoiding_of_sum_card_lt
import Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_comparisonBad_fraction_le

-- ---- from OAI.Combinatorics.BinaryEdit.CodeUnionBound ----
namespace OAI

/-!
Finite union-bound lemmas for the independent random binary codebook argument
in polynomial-code.tex, Lemma `lem:random-segments`.
-/

namespace TreeEdit.BinaryLower
namespace CodeUnionBound

open scoped BigOperators

/-- The same existence statement in terms of real-valued probability bounds
for the uniform distribution on a nonempty finite ambient type. -/
theorem exists_avoiding_of_probability_bounds
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Finset Ω) (p : I → ℝ)
    (hbound : ∀ i, ((bad i).card : ℝ) / Fintype.card Ω ≤ p i)
    (hsum : (∑ i, p i) < 1) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  apply exists_avoiding_of_sum_card_lt bad
  have hpos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hsum' : (∑ i, ((bad i).card : ℝ)) / Fintype.card Ω < 1 := by
    rw [Finset.sum_div]
    exact (Finset.sum_le_sum fun i _ => hbound i).trans_lt hsum
  have hc : (∑ i, ((bad i).card : ℝ)) < Fintype.card Ω := by
    simpa using (div_lt_iff₀ hpos).mp hsum'
  exact_mod_cast hc

/-- A uniform bad-event estimate needs only a bound on the number of events. -/
theorem exists_avoiding_of_uniform_probability_bound
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Finset Ω) (ε : ℝ)
    (hbound : ∀ i, ((bad i).card : ℝ) / Fintype.card Ω ≤ ε)
    (hsum : (Fintype.card I : ℝ) * ε < 1) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  apply exists_avoiding_of_probability_bounds bad (fun _ => ε) hbound
  simpa using hsum

theorem card_segmentComparison (K P : ℕ) :
    Fintype.card (SegmentComparison K P) = K ^ 2 * P ^ 3 := by
  simp only [SegmentComparison, Fintype.card_prod, Fintype.card_fin]
  ring

end CodeUnionBound
end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentCode ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
Finite probabilistic construction of a codebook simultaneously separating every
long segment of every pair of differently labelled blocks. Counting is done on
all Boolean codebooks, so no randomness or existence hypothesis is retained.
-/

namespace TreeEdit.BinaryLower.SegmentCode

open RandomMatching CodeUnionBound

/-- A finite numerical union-bound criterion produces one codebook that works
for every pair of labels, every valid pair of windows, and every matching. -/
theorem exists_segmentSeparated (K P a₀ : ℕ)
    (hprob : (K : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 * (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Fin K → Fin P → Bool, SegmentSeparated c a₀ := by
  classical
  have hsum : (Fintype.card (SegmentComparison K (P+1)) : ℝ) *
      (9/10 : ℝ)^a₀ < 1 := by
    simpa only [card_segmentComparison, Nat.cast_mul, Nat.cast_pow] using hprob
  obtain ⟨c, hc⟩ := exists_avoiding_of_uniform_probability_bound
    (comparisonBad (K := K) (P := P) a₀) ((9/10 : ℝ)^a₀)
    (comparisonBad_fraction_le a₀) hsum
  refine ⟨c, ?_⟩
  intro k l hkl a i j ha hi hj r f g heq
  by_contra hn
  have hs : a-a/100 ≤ r := by omega
  let fs : IncreasingPositions a (a-a/100) :=
    ⟨fun t => f.1 (Fin.castLE hs t), f.2.comp (Fin.strictMono_castLE hs)⟩
  let gs : IncreasingPositions a (a-a/100) :=
    ⟨fun t => g.1 (Fin.castLE hs t), g.2.comp (Fin.strictMono_castLE hs)⟩
  let t : SegmentComparison K (P+1) :=
    (k, l, ⟨a, by omega⟩, ⟨i, by omega⟩, ⟨j, by omega⟩)
  apply hc t
  dsimp [t, comparisonBad]
  rw [dite_eq_left ⟨hkl, ha, hi, hj⟩]
  simp only [segmentMatchingEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fs, gs, fun u => heq (Fin.castLE hs u)⟩

end TreeEdit.BinaryLower.SegmentCode

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching CodeUnionBound


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated := @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated

-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:22:28.857731+00:00
-- url     : https://prove2.me/submissions/66e63cbe-00e9-4720-a6e7-de647106e296

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/UnequalCounting.lean:L23-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Theorems.Thm_OAI_TreeEdit_BinaryLower_card_grid_chain_le
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_gap_budget

-- ---- from OAI.Combinatorics.BinaryEdit.BlockPairCount ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- The distinct values attained by a componentwise monotone sequence of
block indices form a short grid chain. -/
theorem card_monotone_pair_image_le {r M N : ℕ}
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M) (hgb : ∀ a, g a < N) :
    (Finset.univ.image (fun a => (f a, g a))).card ≤ M + N - 1 := by
  apply card_grid_chain_le
  · intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hfb a, hgb a⟩
  · intro p hp q hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    rcases le_total a b with h | h
    · exact Or.inl ⟨hf h, hg h⟩
    · exact Or.inr ⟨hf h, hg h⟩

/-- The number of block pairs visited by an increasing bit matching between
words with `M` and `N` blocks of width `P` is at most `M + N - 1`. -/
theorem card_block_pair_image_le {r M N P : ℕ} (hP : 0 < P)
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M * P) (hgb : ∀ a, g a < N * P) :
    (Finset.univ.image (fun a => (f a / P, g a / P))).card ≤ M + N - 1 := by
  apply card_monotone_pair_image_le
  · intro a b hab
    exact Nat.div_le_div_right (hf hab)
  · intro a b hab
    exact Nat.div_le_div_right (hg hab)
  · intro a
    exact (Nat.div_lt_iff_lt_mul hP).mpr (hfb a)
  · intro a
    exact (Nat.div_lt_iff_lt_mul hP).mpr (hgb a)

/-- In the equal-length case, at most `2 * M - 1` block pairs occur. -/
theorem card_equal_block_pair_image_le {r M P : ℕ} (hP : 0 < P)
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M * P) (hgb : ∀ a, g a < M * P) :
    (Finset.univ.image (fun a => (f a / P, g a / P))).card ≤ 2 * M - 1 := by
  simpa [two_mul] using card_block_pair_image_le hP f g hf hg hfb hgb

/-- A fixed block pair occupies a consecutive portion of the matching.
This is the order-convexity fact needed for its minimal spans to contain
no positions matched under a different pair. -/
theorem monotone_pair_fiber_convex {ι : Type*} [Preorder ι]
    (f g : ι → ℕ) (hf : Monotone f) (hg : Monotone g)
    {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c)
    (h : (f a, g a) = (f c, g c)) : (f b, g b) = (f a, g a) := by
  have hfEq : f a = f c := congrArg Prod.fst h
  have hgEq : g a = g c := congrArg Prod.snd h
  have hfL := hf hab
  have hfR := hf hbc
  have hgL := hg hab
  have hgR := hg hbc
  apply Prod.ext <;> simp only <;> omega

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSpanBudget ----
namespace OAI

namespace TreeEdit.BinaryLower

noncomputable section

/-- The two words' losses can be added because their total lengths are equal. -/
theorem matchingSpan_two_sided_gap_budget {r n : ℕ} {β : Type*} [DecidableEq β]
    (f g : Fin r → Fin n) (hf : StrictMono f) (hg : StrictMono g)
    (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (s : Finset β) :
    (∑ b ∈ s,
      (((matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card) +
       ((matchingSpan g label b).card - (Finset.univ.filter fun i => label i = b).card)))
      ≤ 2 * (n - r) := by
  rw [Finset.sum_add_distrib, two_mul]
  exact Nat.add_le_add (matchingSpan_gap_budget f hf label hc s)
    (matchingSpan_gap_budget g hg label hc s)

/-- The concrete block-pair label of an increasing matching has convex fibers. -/
theorem block_pair_fiber_convex {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (hf : Monotone f) (hg : Monotone g)
    {i j k : Fin r} (hij : i ≤ j) (hjk : j ≤ k)
    (heq : ((f i).val / P, (g i).val / P) = ((f k).val / P, (g k).val / P)) :
    ((f j).val / P, (g j).val / P) = ((f i).val / P, (g i).val / P) := by
  apply monotone_pair_fiber_convex (fun a => (f a).val / P)
    (fun a => (g a).val / P) _ _ hij hjk heq
  · intro a b hab
    exact Nat.div_le_div_right (hf hab)
  · intro a b hab
    exact Nat.div_le_div_right (hg hab)

/-- For the actual quotient block-pair labels, the span losses over any
selected pairs are at most twice the global one-sided matching deficit. -/
theorem block_pair_two_sided_gap_budget {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (hf : StrictMono f) (hg : StrictMono g)
    (s : Finset (ℕ × ℕ)) :
    let label := fun i => ((f i).val / P, (g i).val / P)
    (∑ b ∈ s,
      (((matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card) +
       ((matchingSpan g label b).card - (Finset.univ.filter fun i => label i = b).card)))
      ≤ 2 * (n - r) := by
  apply matchingSpan_two_sided_gap_budget f g hf hg
  intro i j k hij hjk heq
  exact block_pair_fiber_convex P f g hf.monotone hg.monotone hij hjk heq

end
end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.UnequalCounting ----
namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- Sum the local large-pair charge, allowing a threshold-sized error for
every visited block pair.  Small pairs need no separation hypothesis. -/
theorem sum_counts_le_of_large_charge {β : Type*} (s : Finset β)
    (a g : β → ℕ) (a₀ : ℕ)
    (hlarge : ∀ b ∈ s, a₀ ≤ a b → a b ≤ 100 * g b) :
    (∑ b ∈ s, a b) ≤ 100 * (∑ b ∈ s, g b) + s.card * a₀ := by
  have hlocal : ∀ b ∈ s, a b ≤ 100 * g b + a₀ := by
    intro b hb
    by_cases h : a₀ ≤ a b
    · exact (hlarge b hb h).trans (Nat.le_add_right _ _)
    · omega
  calc
    (∑ b ∈ s, a b) ≤ ∑ b ∈ s, (100 * g b + a₀) := Finset.sum_le_sum hlocal
    _ = 100 * (∑ b ∈ s, g b) + s.card * a₀ := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- The unequal-label count estimate once the actual segment separation has
been applied to each large block pair. All gap terms here are the concrete
interval-span losses, rather than arbitrary charged weights. -/
theorem block_pair_bad_count_le {r M P : ℕ} (hP : 0 < P)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (bad : ℕ × ℕ → Prop) [DecidablePred bad] (a₀ : ℕ)
    (hlarge : ∀ b ∈ (Finset.univ.image (fun i => ((f i).val / P, (g i).val / P))).filter bad,
      a₀ ≤ (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card →
      (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card ≤
        100 * (((matchingSpan f (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card) +
          ((matchingSpan g (fun i => ((f i).val / P, (g i).val / P)) b).card -
          (Finset.univ.filter (fun i => ((f i).val / P, (g i).val / P) = b)).card))) :
    (Finset.univ.filter (fun i => bad ((f i).val / P, (g i).val / P))).card ≤
      200 * (M * P - r) + 2 * M * a₀ := by
  classical
  let label := fun i => ((f i).val / P, (g i).val / P)
  let pairs := (Finset.univ.image label).filter bad
  let a := fun b => (Finset.univ.filter (fun i => label i = b)).card
  let gap := fun b => ((matchingSpan f label b).card - a b) +
      ((matchingSpan g label b).card - a b)
  have hsum := sum_counts_le_of_large_charge pairs a gap a₀ hlarge
  have hgap := block_pair_two_sided_gap_budget P f g hf hg pairs
  have hpair : pairs.card ≤ 2 * M := by
    have h := card_equal_block_pair_image_le hP (fun i => (f i).val)
      (fun i => (g i).val) hf.monotone hg.monotone
      (fun i => (f i).isLt) (fun i => (g i).isLt)
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (h.trans (Nat.sub_le _ _))
  have hcount : (∑ b ∈ pairs, a b) =
      (Finset.univ.filter (fun i => bad (label i))).card := by
    rw [show (∑ b ∈ pairs, a b) =
        ∑ b ∈ pairs, (Finset.univ.filter (fun i => label i = b)).card from rfl]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairs]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, h⟩
  rw [hcount] at hsum
  change (Finset.univ.filter (fun i => bad (label i))).card ≤ _
  dsimp only [gap, a] at hsum
  dsimp only at hgap
  nlinarith

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le := @_root_.OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le

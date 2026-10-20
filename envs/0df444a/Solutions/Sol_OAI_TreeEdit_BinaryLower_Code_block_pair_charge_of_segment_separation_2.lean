-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:36:03.755153+00:00
-- url     : https://prove2.me/submissions/6f34cd7e-3e89-4c8c-9a67-496adfa989f6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/UnequalSegments.lean:L36-L134
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments
import Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_lower_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_subset_ofFn_segments
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_exists_endpoints
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_inter_image

-- ---- from OAI.Combinatorics.BinaryEdit.BlockPairCount ----
namespace OAI

namespace TreeEdit.BinaryLower

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

/-- Each matched position of a fiber belongs to its span. -/
theorem matchingSpan_contains_match {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (label : Fin r → β) {b : β} {i : Fin r}
    (hi : label i = b) : f i ∈ matchingSpan f label b :=
  (mem_matchingSpan f label b (f i)).mpr ⟨i, i, hi, hi, le_rfl, le_rfl⟩

/-- There cannot be more matching entries in a fiber than positions in its span. -/
theorem matchingSpan_fiber_card_le {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    (Finset.univ.filter fun i => label i = b).card ≤ (matchingSpan f label b).card := by
  classical
  calc
    (Finset.univ.filter fun i => label i = b).card =
        ((Finset.univ.filter fun i => label i = b).image f).card :=
      (Finset.card_image_of_injective _ hf.injective).symm
    _ = (matchingSpan f label b ∩ Finset.univ.image f).card := by
      rw [matchingSpan_inter_image f hf label hc]
    _ ≤ (matchingSpan f label b).card := Finset.card_le_card Finset.inter_subset_left

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

end
end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeTrimming ----
namespace OAI

/-!
# The local span-trimming step in fixed-length binary conversion

If a matched subsequence occupies two larger contiguous spans, taking prefixes
of those spans deletes at most the total number of removed positions from the
matching. This lemma does not assume that matched positions are consecutive.
-/

namespace TreeEdit.BinaryLower.Code

universe u

/-- Trimming two words loses at most the sum of the numbers of removed symbols
from any fixed common subsequence. -/
theorem common_sublist_take {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y) (a b : ℕ) :
    ∃ w : List α, w.Sublist (x.take a) ∧ w.Sublist (y.take b) ∧
      z.length ≤ w.length + (x.length - a) + (y.length - b) := by
  obtain ⟨u, huz, hux, hu⟩ :=
    common_sublist_lower_bound hzx (List.take_sublist a x)
  obtain ⟨w, hwu, hwy, hw⟩ :=
    common_sublist_lower_bound (huz.trans hzy) (List.take_sublist b y)
  refine ⟨w, hwu.trans hux, hwy, ?_⟩
  simp only [List.length_take] at hu hw
  omega

/-- The manuscript trims each span to the number of matched symbols. -/
theorem common_sublist_trim_to_matched_length {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y) :
    ∃ w : List α, w.Sublist (x.take z.length) ∧ w.Sublist (y.take z.length) ∧
      z.length ≤ w.length + ((x.length - z.length) + (y.length - z.length)) := by
  obtain ⟨w, hwx, hwy, hlen⟩ := common_sublist_take hzx hzy z.length z.length
  exact ⟨w, hwx, hwy, by omega⟩

/-- A 99-percent separation bound on the two trimmed segments charges at least
one unmatched span position for each hundred matches. All arithmetic here is
in natural numbers, avoiding rounding or division conventions. -/
theorem trim_separation_charge {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y)
    (hsep : ∀ w : List α, w.Sublist (x.take z.length) →
      w.Sublist (y.take z.length) → 100 * w.length ≤ 99 * z.length) :
    z.length ≤ 100 * ((x.length - z.length) + (y.length - z.length)) := by
  obtain ⟨w, hwx, hwy, hlen⟩ := common_sublist_trim_to_matched_length hzx hzy
  have h := hsep w hwx hwy
  omega

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.UnequalSegments ----
namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- Endpoint descriptions give the literal (untruncated) lengths of the
contiguous spans in the corresponding word. -/
theorem ofFn_segment_length_of_span {α : Type*} {r n : ℕ}
    (x : Fin n → α) (f : Fin r → Fin n) {β : Type*} [DecidableEq β]
    (label : Fin r → β) (b : β) (i j : Fin r)
    (hcard : (matchingSpan f label b).card = (f j).val + 1 - (f i).val)
    (hij : f i ≤ f j) :
    (((List.ofFn x).drop (f i).val).take (matchingSpan f label b).card).length =
      (matchingSpan f label b).card := by
  simp only [List.length_take, List.length_drop, List.length_ofFn]
  apply min_eq_left
  have hj := (f j).isLt
  change (f i).val ≤ (f j).val at hij
  omega

/-- Local charge for a visited bad block pair, using only actual contiguous
segments of the two binary words. -/
theorem block_pair_charge_of_segment_separation
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀)
    (b : ℕ × ℕ) (hb : bad b)
    (hvisit : ∃ t, ((f t).val / P, (g t).val / P) = b)
    (hlarge : a₀ ≤
      (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) :
    (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card ≤
      100 * (((matchingSpan f (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) +
        ((matchingSpan g (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card)) := by
  classical
  let label := fun t => ((f t).val / P, (g t).val / P)
  let S := Finset.univ.filter (fun t => label t = b)
  have hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i := by
    intro i j k hij hjk heq
    exact block_pair_fiber_convex P f g hf.monotone hg.monotone hij hjk heq
  obtain ⟨i, j, hi, hj, hij, hspanx, hcardx⟩ :=
    matchingSpan_exists_endpoints f hf.monotone label b hvisit
  obtain ⟨u, v, hu, hv, huv, hspany, hcardy⟩ :=
    matchingSpan_exists_endpoints g hg.monotone label b hvisit
  let sx := (matchingSpan f label b).card
  let sy := (matchingSpan g label b).card
  have hSx : S.card ≤ sx := matchingSpan_fiber_card_le f hf label hc b
  have hSy : S.card ≤ sy := matchingSpan_fiber_card_le g hg label hc b
  have hix : f i ≤ f j := hf.monotone hij
  have hiy : g u ≤ g v := hg.monotone huv
  have hSlo : ∀ t ∈ S, (f i).val ≤ (f t).val := by
    intro t ht
    have hmem := matchingSpan_contains_match f label (Finset.mem_filter.mp ht).2
    rw [hspanx] at hmem
    exact (Finset.mem_Icc.mp hmem).1
  have hShi : ∀ t ∈ S, (f t).val < (f i).val + sx := by
    intro t ht
    have hmem := matchingSpan_contains_match f label (Finset.mem_filter.mp ht).2
    rw [hspanx] at hmem
    have h := (Finset.mem_Icc.mp hmem).2
    change (f t).val ≤ (f j).val at h
    dsimp [sx]
    change (f i).val ≤ (f j).val at hix
    omega
  have hTlo : ∀ t ∈ S, (g u).val ≤ (g t).val := by
    intro t ht
    have hmem := matchingSpan_contains_match g label (Finset.mem_filter.mp ht).2
    rw [hspany] at hmem
    exact (Finset.mem_Icc.mp hmem).1
  have hThi : ∀ t ∈ S, (g t).val < (g u).val + sy := by
    intro t ht
    have hmem := matchingSpan_contains_match g label (Finset.mem_filter.mp ht).2
    rw [hspany] at hmem
    have h := (Finset.mem_Icc.mp hmem).2
    change (g t).val ≤ (g v).val at h
    dsimp [sy]
    change (g u).val ≤ (g v).val at hiy
    omega
  obtain ⟨z, hzx, hzy, hzlen⟩ := common_sublist_subset_ofFn_segments
    x y f g hf hg hmatch S (f i).val (g u).val sx sy hSlo hShi hTlo hThi
  have hlenx := ofFn_segment_length_of_span x f label b i j hcardx hix
  have hleny := ofFn_segment_length_of_span y g label b u v hcardy hiy
  have hi1 : (f i).val / P = b.1 := congrArg Prod.fst hi
  have hj1 : (f j).val / P = b.1 := congrArg Prod.fst hj
  have hu2 : (g u).val / P = b.2 := congrArg Prod.snd hu
  have hv2 : (g v).val / P = b.2 := congrArg Prod.snd hv
  have hb1 : b.1 < M := by
    rw [← hi1]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (f i).isLt
  have hb2 : b.2 < M := by
    rw [← hu2]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (g u).isLt
  have hlx : b.1 * P ≤ (f i).val := by simpa [hi1] using Nat.div_mul_le_self (f i).val P
  have hly : b.2 * P ≤ (g u).val := by simpa [hu2] using Nat.div_mul_le_self (g u).val P
  have hhx : (f i).val + S.card ≤ (b.1 + 1) * P := by
    have h := Nat.lt_mul_div_succ (f j).val hP
    rw [hj1, Nat.mul_comm P (b.1 + 1)] at h
    dsimp [sx] at hSx
    change (f i).val ≤ (f j).val at hix
    omega
  have hhy : (g u).val + S.card ≤ (b.2 + 1) * P := by
    have h := Nat.lt_mul_div_succ (g v).val hP
    rw [hv2, Nat.mul_comm P (b.2 + 1)] at h
    dsimp [sy] at hSy
    change (g u).val ≤ (g v).val at hiy
    omega
  have hcharge := trim_separation_charge hzx hzy (by
    intro w hwx hwy
    have hwx' : w.Sublist (((List.ofFn x).drop (f i).val).take S.card) := by
      simpa [hzlen, List.take_take, min_eq_left hSx] using hwx
    have hwy' : w.Sublist (((List.ofFn y).drop (g u).val).take S.card) := by
      simpa [hzlen, List.take_take, min_eq_left hSy] using hwy
    simpa [hzlen] using hsep b hb hb1 hb2 (f i).val (g u).val S.card
      hlx hhx hly hhy hlarge w hwx' hwy')
  simpa [hzlen, hlenx, hleny, sx, sy, S, label] using hcharge

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation := @_root_.OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation

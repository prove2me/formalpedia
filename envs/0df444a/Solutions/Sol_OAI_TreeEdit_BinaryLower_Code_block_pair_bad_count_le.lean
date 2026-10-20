-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.block_pair_bad_count_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:44:05.620416+00:00
-- url     : https://prove2.me/submissions/7af98213-5b29-48ca-bcfd-843a3b74b068

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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_gap_budget
import Theorems.Thm_OAI_TreeEdit_BinaryLower_card_grid_chain_le

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution {r M P : ℕ} (hP : 0 < P)
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
  set L : Fin r → ℕ × ℕ := fun i => ((f i).val / P, (g i).val / P) with hL
  set S := Finset.univ.image L with hS
  set B := S.filter bad with hB
  set c : ℕ × ℕ → ℕ := fun b => (Finset.univ.filter (fun i => L i = b)).card with hc
  have hmonoL : ∀ i j, i ≤ j → (L i).1 ≤ (L j).1 ∧ (L i).2 ≤ (L j).2 := fun i j hij =>
    ⟨Nat.div_le_div_right (hf.monotone hij), Nat.div_le_div_right (hg.monotone hij)⟩
  have hconv : ∀ {i j k : Fin r}, i ≤ j → j ≤ k → L i = L k → L j = L i := by
    intro i j k hij hjk hik
    have a1 := hmonoL i j hij
    have a2 := hmonoL j k hjk
    rw [hik] at a1
    exact Prod.ext (by have := a1.1; have := a2.1; rw [hik]; omega) (by have := a1.2; have := a2.2; rw [hik]; omega)
  -- bad count as sum over B
  have hsum : (Finset.univ.filter (fun i => bad (L i))).card = ∑ b ∈ B, c b := by
    rw [Finset.card_eq_sum_card_fiberwise (f := L) (t := B)]
    · refine Finset.sum_congr rfl fun b hb => congrArg Finset.card (Finset.ext fun i => ?_)
      have hbad : bad b := (Finset.mem_filter.1 hb).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hbad, h⟩
    · intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (Finset.mem_filter.1 hi).2⟩
  -- per-label bound
  have hper : ∀ b ∈ B, c b ≤ a₀ + 100 * (((matchingSpan f L b).card - c b) + ((matchingSpan g L b).card - c b)) := by
    intro b hb
    by_cases h : a₀ ≤ c b
    · have := hlarge b hb h
      change c b ≤ 100 * (((matchingSpan f L b).card - c b) + ((matchingSpan g L b).card - c b)) at this
      omega
    · omega
  have hgf := matchingSpan_gap_budget f hf L hconv B
  have hgg := matchingSpan_gap_budget g hg L hconv B
  have hcardS : S.card ≤ M + M - 1 := by
    apply card_grid_chain_le
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      constructor
      · exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (f i).isLt (Nat.mul_comm M P))
      · exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (g i).isLt (Nat.mul_comm M P))
    · intro p hp q hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
      rcases le_total i j with h | h
      · exact Or.inl (hmonoL i j h)
      · exact Or.inr (hmonoL j i h)
  have hBS : B.card ≤ S.card := Finset.card_filter_le _ _
  change (Finset.univ.filter (fun i => bad (L i))).card ≤ _
  rw [hsum]
  calc ∑ b ∈ B, c b ≤ ∑ b ∈ B, (a₀ + 100 * (((matchingSpan f L b).card - c b) + ((matchingSpan g L b).card - c b))) :=
        Finset.sum_le_sum hper
    _ = B.card * a₀ + 100 * (∑ b ∈ B, ((matchingSpan f L b).card - c b) +
          ∑ b ∈ B, ((matchingSpan g L b).card - c b)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 * M) * a₀ + 100 * ((M * P - r) + (M * P - r)) := by
        gcongr
        all_goals first | omega | exact hgf | exact hgg
    _ = 200 * (M * P - r) + 2 * M * a₀ := by ring


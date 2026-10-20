-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:36:23.459989+00:00
-- url     : https://prove2.me/submissions/1d0bc30f-1d31-4471-93b0-4a0c458f87d8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L132-L150
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_prime_supply

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- The globally distinct prime family indexed by depth and child, as used in
`finite-tree.tex`. An embedding makes distinctness over *all* pairs explicit. -/
theorem finite_tree_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by
  obtain ⟨k₀, hk₀⟩ := prime_supply
  refine ⟨k₀, ?_⟩
  intro k hk
  have hcard : Fintype.card (Fin k × Fin (20 * k)) ≤
      ((Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime).card := by
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, mul_assoc, mul_left_comm] using
      (hk₀ k hk).1
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset hcard
  refine ⟨p, ?_⟩
  intro ji
  have hmem := hp (Set.mem_range_self ji)
  obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hmem
  exact ⟨hprime, (Finset.mem_Icc.mp hinterval).1, (Finset.mem_Icc.mp hinterval).2⟩

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family

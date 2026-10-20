-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_odd_prime_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:38:19.214374+00:00
-- url     : https://prove2.me/submissions/53c8ab6f-7971-46b2-904a-992b9d6ee65c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L152-L170
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_odd_prime_family. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_finite_tree_prime_family

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- Strengthened finite-tree data: every selected prime is odd (expressed as
strictly greater than two), uniformly over the entire depth/child index set. -/
theorem finite_tree_odd_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 ≤ k ∧ ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ 2 < p ji ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by
  obtain ⟨k₀, hk₀⟩ := finite_tree_prime_family
  refine ⟨max 2 k₀, ?_⟩
  intro k hk
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₀ : k₀ ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨p, hp⟩ := hk₀ k hkk₀
  refine ⟨hk2, p, ?_⟩
  intro ji
  obtain ⟨hprime, hlow, hupp⟩ := hp ji
  have hpow : 2 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk2 4
  refine ⟨hprime, ?_, hlow, hupp⟩
  norm_num at hpow
  omega

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_odd_prime_family := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_odd_prime_family

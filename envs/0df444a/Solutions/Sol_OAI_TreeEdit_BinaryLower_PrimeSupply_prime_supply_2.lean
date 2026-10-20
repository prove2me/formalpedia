-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.prime_supply
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:34:21.379392+00:00
-- url     : https://prove2.me/submissions/29507573-5e01-495e-8c08-c9de56074691

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L112-L130
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.prime_supply. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_primeCounting_le_interval_card_add
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_prime_counting_pow_lower

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- Consecutive polynomial powers contain at least the lower power in primes,
for all sufficiently large bases. -/
theorem primes_in_power_interval (e : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      k ^ e ≤ ((Finset.Icc (k ^ e) (k ^ (e + 1))).filter Nat.Prime).card := by
  obtain ⟨k₀, hk₀⟩ := prime_counting_pow_lower e
  refine ⟨k₀, ?_⟩
  intro k hk
  have hcount := hk₀ k hk
  have hinterval := primeCounting_le_interval_card_add (k ^ e) (k ^ (e + 1))
  omega

/-- Prime supply in the exact two intervals required by the manuscript. -/
theorem prime_supply :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      20 * k ^ 2 ≤ ((Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime).card ∧
      1600 * k < ((Finset.Icc (k ^ 2) (k ^ 3)).filter Nat.Prime).card := by
  obtain ⟨k₄, hk₄⟩ := primes_in_power_interval 4
  obtain ⟨k₂, hk₂⟩ := primes_in_power_interval 2
  refine ⟨max 1601 (max k₄ k₂), ?_⟩
  intro k hk
  have hkbig : 1601 ≤ k := le_trans (le_max_left _ _) hk
  have hk₄' : k₄ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk₂' : k₂ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  constructor
  · have h20 : 20 ≤ k ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_right (k ^ 2) h20
    have hlower : 20 * k ^ 2 ≤ k ^ 4 := by nlinarith [hmul]
    exact hlower.trans (hk₄ k hk₄')
  · have hlower : 1600 * k < k ^ 2 := by nlinarith
    exact hlower.trans_le (hk₂ k hk₂')

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_supply := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_supply

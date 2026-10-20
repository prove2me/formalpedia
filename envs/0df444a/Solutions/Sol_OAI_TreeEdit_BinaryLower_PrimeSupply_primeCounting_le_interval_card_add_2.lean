-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.primeCounting_le_interval_card_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:32:57.936449+00:00
-- url     : https://prove2.me/submissions/90a08c50-4647-4155-8529-89efd4bda255

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L82-L98
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.primeCounting_le_interval_card_add. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- Removing all integers below `a` from the primes at most `b` loses at most `a`
primes. The inclusive lower endpoint matches the source interval convention. -/
theorem primeCounting_le_interval_card_add (a b : ℕ) :
    Nat.primeCounting b ≤ ((Finset.Icc a b).filter Nat.Prime).card + a := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE b ⊆ (Finset.Icc a b).filter Nat.Prime ∪ Finset.range a := by
    intro p hp
    obtain ⟨hpb, hprime⟩ := Nat.mem_primesLE.mp hp
    by_cases hpa : a ≤ p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpa, hpb⟩, hprime⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  calc
    (Nat.primesLE b).card ≤ ((Finset.Icc a b).filter Nat.Prime ∪ Finset.range a).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Icc a b).filter Nat.Prime).card + (Finset.range a).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_range]

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.primeCounting_le_interval_card_add := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.primeCounting_le_interval_card_add

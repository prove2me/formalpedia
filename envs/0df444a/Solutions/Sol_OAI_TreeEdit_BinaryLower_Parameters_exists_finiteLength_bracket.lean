-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Parameters.exists_finiteLength_bracket
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:10:55.856318+00:00
-- url     : https://prove2.me/submissions/bcf9705c-aacb-4051-bc3b-7da3ce7ae11d

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters
theorem h49_fl_ge (n : ℕ) (hn : 1 ≤ n) : 20 * n ≤ OAI.TreeEdit.BinaryLower.Parameters.finiteLength n := by
  unfold OAI.TreeEdit.BinaryLower.Parameters.finiteLength
  have h1 : 1 ≤ n ^ (20 * n) := Nat.one_le_pow _ _ hn
  have h2 : 20 * n ≤ 20 * n * n ^ (20 * n) := Nat.le_mul_of_pos_right _ h1
  have h3 : 20 * n * n ^ (20 * n) ≤ (20 * n * n ^ (20 * n)) ^ (3 * n) :=
    Nat.le_self_pow (by omega) _
  omega

theorem solution {k₀ d : ℕ} (hk₀ : 0 < k₀)
    (hd : finiteLength k₀ ≤ d) :
    ∃ k : ℕ, k₀ ≤ k ∧ finiteLength k ≤ d ∧ d < finiteLength (k + 1) := by
  have hex : ∃ m, k₀ ≤ m ∧ d < finiteLength m :=
    ⟨d + k₀ + 1, by omega, by have := h49_fl_ge (d + k₀ + 1) (by omega); omega⟩
  classical
  let m := Nat.find hex
  have hm : k₀ ≤ m ∧ d < finiteLength m := Nat.find_spec hex
  have hmk : m ≠ k₀ := by
    intro h; rw [h] at hm; omega
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · have := Nat.find_min hex (show m - 1 < m by omega)
    push_neg at this
    exact this (by omega)
  · have : m - 1 + 1 = m := by omega
    rw [this]; exact hm.2


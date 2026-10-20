-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:14:00.174597+00:00
-- url     : https://prove2.me/submissions/7c4f3bda-e314-428e-80a2-67603e27a6e5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteAlphabet.lean:L80-L99
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteAlphabet_tagged_alphabet_card_le

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteAlphabet ----
namespace OAI

namespace TreeEdit.BinaryLower.FiniteAlphabet

open scoped BigOperators

/-- The numerical alphabet budget holds already for every `k≥2`. -/
theorem residue_budget_le_word_length {k : ℕ} (hk : 2 ≤ k) :
    (20 * k) ^ k * (2 * k ^ (5 * k)) ≤ (20 * k * k ^ (20 * k)) ^ k := by
  rw [mul_pow (20 * k) (k ^ (20 * k)) k]
  apply Nat.mul_le_mul_left
  calc
    2 * k ^ (5 * k) ≤ k * k ^ (5 * k) := Nat.mul_le_mul_right _ hk
    _ = k ^ (5 * k + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ (k ^ (20 * k)) ^ k := by
      rw [← pow_mul]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

/-- The literal tagged residue alphabet satisfies the cardinal hypotheses of
the fixed-length binary conversion theorem. -/
theorem finite_tree_alphabet_bounds {k : ℕ} (hk : 2 ≤ k)
    (Q : Word (Fin (20 * k)) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ 2 * k ^ (5 * k)) :
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by
  classical
  let : Fintype (Word (Fin (20 * k)) k) :=
    Fintype.ofEquiv (Fin k → Fin (20 * k))
      (Equiv.vectorEquivFin (Fin (20 * k)) k).symm
  let (a : Word (Fin (20 * k)) k) : NeZero (Q a) := ⟨Nat.ne_of_gt (hQpos a)⟩
  let a : Word (Fin (20 * k)) k :=
    ⟨List.replicate k ⟨0, by omega⟩, by simp⟩
  let : Nonempty (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) := ⟨⟨a, 0⟩⟩
  refine ⟨inferInstance, Nat.card_pos, ?_⟩
  exact (tagged_alphabet_card_le Q hQpos hQupper).trans
    (residue_budget_le_word_length hk)

end TreeEdit.BinaryLower.FiniteAlphabet

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteAlphabet
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds := @_root_.OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds

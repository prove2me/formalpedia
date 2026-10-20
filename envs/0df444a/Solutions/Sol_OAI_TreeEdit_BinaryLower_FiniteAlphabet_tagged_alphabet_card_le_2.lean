-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:12:16.225816+00:00
-- url     : https://prove2.me/submissions/e9b66fe4-bf9c-4ffb-9ef6-80eddb22efd7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteAlphabet.lean:L58-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteAlphabet ----
namespace OAI

namespace TreeEdit.BinaryLower.FiniteAlphabet

open scoped BigOperators

/-- Bound the tagged residue alphabet on literal fixed-length leaf words.
The local Fintype instances are constructed here, rather than presupposed. -/
theorem tagged_alphabet_card_le {m k H : ℕ}
    (Q : Word (Fin m) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ H) :
    Nat.card (Σ a : Word (Fin m) k, ZMod (Q a)) ≤ m ^ k * H := by
  classical
  let : Fintype (Word (Fin m) k) :=
    Fintype.ofEquiv (Fin k → Fin m) (Equiv.vectorEquivFin (Fin m) k).symm
  let (a : Word (Fin m) k) : NeZero (Q a) := ⟨Nat.ne_of_gt (hQpos a)⟩
  have hleaf : Fintype.card (Word (Fin m) k) = m ^ k := by
    let e : Word (Fin m) k ≃ (Fin k → Fin m) := Equiv.vectorEquivFin (Fin m) k
    calc
      Fintype.card (Word (Fin m) k) = Fintype.card (Fin k → Fin m) := Fintype.card_congr e
      _ = m ^ k := by simp
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [ZMod.card]
  calc
    (∑ a, Q a) ≤ ∑ _a : Word (Fin m) k, H :=
      Finset.sum_le_sum fun a _ => hQupper a
    _ = m ^ k * H := by simp [hleaf]

end TreeEdit.BinaryLower.FiniteAlphabet

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteAlphabet
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le := @_root_.OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le

-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:11:07.216445+00:00
-- url     : https://prove2.me/submissions/c0d9de2e-4e04-4d91-8037-8569b029d390

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators


theorem solution {m k H : ℕ}
    (Q : Word (Fin m) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ H) :
    Nat.card (Σ a : Word (Fin m) k, ZMod (Q a)) ≤ m ^ k * H := by
  haveI : ∀ a, NeZero (Q a) := fun a => ⟨(hQpos a).ne'⟩
  haveI : Fintype (Word (Fin m) k) := (inferInstance : Fintype (List.Vector (Fin m) k))
  have hc : Fintype.card (Word (Fin m) k) = m ^ k := by
    rw [show Fintype.card (Word (Fin m) k) = Fintype.card (List.Vector (Fin m) k) from Fintype.card_congr (Equiv.refl _),
      card_vector, Fintype.card_fin]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [ZMod.card]
  calc ∑ a, Q a ≤ ∑ _a : Word (Fin m) k, H := Finset.sum_le_sum fun a _ => hQupper a
    _ = m ^ k * H := by rw [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]


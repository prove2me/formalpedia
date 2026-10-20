-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:20:09.805217+00:00
-- url     : https://prove2.me/submissions/355a6d21-27b8-4c10-8aa8-36d30ace41f8

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


theorem solution {k : ℕ} (hk : 2 ≤ k)
    (Q : Word (Fin (20 * k)) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ 2 * k ^ (5 * k)) :
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by
  haveI : ∀ a, NeZero (Q a) := fun a => ⟨(hQpos a).ne'⟩
  haveI : Fintype (Word (Fin (20 * k)) k) := (inferInstance : Fintype (List.Vector (Fin (20 * k)) k))
  have hc : Fintype.card (Word (Fin (20 * k)) k) = (20 * k) ^ k := by
    rw [show Fintype.card (Word (Fin (20 * k)) k) = Fintype.card (List.Vector (Fin (20 * k)) k) from
      Fintype.card_congr (Equiv.refl _), card_vector, Fintype.card_fin]
  have hcard : Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) = ∑ a, Q a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [ZMod.card]
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [hcard]
    let a0 : Word (Fin (20 * k)) k := ⟨List.replicate k ⟨0, by omega⟩, by simp⟩
    calc 1 ≤ Q a0 := hQpos a0
      _ ≤ ∑ a, Q a := Finset.single_le_sum (fun a _ => Nat.zero_le _) (Finset.mem_univ a0)
  · rw [hcard]
    have h1 : ∑ a, Q a ≤ (20 * k) ^ k * (2 * k ^ (5 * k)) := by
      calc ∑ a, Q a ≤ ∑ _a : Word (Fin (20 * k)) k, 2 * k ^ (5 * k) :=
            Finset.sum_le_sum fun a _ => hQupper a
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
    have h2 : 2 * k ^ (5 * k) ≤ k ^ (20 * k * k) := by
      calc 2 * k ^ (5 * k) ≤ k * k ^ (5 * k) := Nat.mul_le_mul_right _ hk
        _ = k ^ (5 * k + 1) := by ring
        _ ≤ k ^ (20 * k * k) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    calc ∑ a, Q a ≤ (20 * k) ^ k * (2 * k ^ (5 * k)) := h1
      _ ≤ (20 * k) ^ k * k ^ (20 * k * k) := Nat.mul_le_mul_left _ h2
      _ = (20 * k * k ^ (20 * k)) ^ k := by rw [mul_pow (20 * k), ← pow_mul]


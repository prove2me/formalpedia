-- Prove2me | solution 1 for OAI.TreeEdit.Words.cycles_val
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:52:41.669709+00:00
-- url     : https://prove2.me/submissions/0fbd930d-d913-4078-bb66-1f1e74f51bdd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/WordOperations.lean:L53-L94
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.Words.cycles_val. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation

-- ---- from OAI.Combinatorics.TreeEdit.WordOperations ----
namespace OAI

namespace TreeEdit

universe u v

variable {α : Type u} {x y z : List α}

attribute [local instance] Classical.propDecidable

namespace EditStep

end EditStep

namespace EditScript

end EditScript

namespace Words

variable {β : Type v} {n : ℕ}

lemma ofFn_get (x : Word β n) : List.ofFn (get x) = x.val := by
  rcases x with ⟨x, rfl⟩
  exact List.ofFn_get x

lemma cycles_val {m T B : ℕ} {β : Fin m → Type*}
    (x : Fin T → ∀ i, Word (β i) B) :
    (cycles x).val = (List.ofFn fun a =>
      (List.ofFn fun i => ((x a i).val.map (Sigma.mk i))).flatten).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext a
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [← ofFn_get (x a i), List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmB : 0 < m * B := Nat.mul_pos hm hB
  have hi : i.val * B + j.val < m * B := by nlinarith [i.isLt, j.isLt]
  have hd₁ : (a.val * (m * B) + (i.val * B + j.val)) / (m * B) = a.val := by
    rw [Nat.mul_comm a.val, Nat.mul_add_div hmB, Nat.div_eq_of_lt hi, add_zero]
  have hr₁ : (a.val * (m * B) + (i.val * B + j.val)) % (m * B) = i.val * B + j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
  have hd₂ : (i.val * B + j.val) / B = i.val := by
    rw [Nat.mul_comm i.val, Nat.mul_add_div hB, Nat.div_eq_of_lt j.isLt, add_zero]
  have hr₂ : (i.val * B + j.val) % B = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  let r : Fin (T * (m * B)) := ⟨a.val * (m * B) + (i.val * B + j.val), by
    nlinarith [a.isLt]⟩
  have hra : r.divNat = a := Fin.ext hd₁
  have hri : r.modNat.divNat = i := by
    apply Fin.ext
    change (a.val * (m * B) + (i.val * B + j.val)) % (m * B) / B = i.val
    rw [hr₁, hd₂]
  have hrj : r.modNat.modNat = j := by
    apply Fin.ext
    change (a.val * (m * B) + (i.val * B + j.val)) % (m * B) % B = j.val
    rw [hr₁, hr₂]
  change Sigma.mk r.modNat.divNat (get (x r.divNat r.modNat.divNat) r.modNat.modNat) =
    Sigma.mk i (get (x a i) j)
  rw [hra, hri, hrj]

end Words

namespace Words

variable {β : Type v} {n : ℕ}

end Words

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.Words
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.Words.cycles_val := @_root_.OAI.TreeEdit.Words.cycles_val

-- Prove2me | solution 1 for OAI.TreeEdit.div_strict_of_equal_residue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:38:56.675558+00:00
-- url     : https://prove2.me/submissions/13a376f6-0273-4e14-928a-0bf9de2a3bcb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Alignments.lean:L69-L87
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.div_strict_of_equal_residue. The node keeps its source
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

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem strictMono_fin_gap {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i j : Fin n) (hij : i ≤ j) : f i + (j.val - i.val) ≤ f j := by
  have aux : ∀ (b d : ℕ) (h : b + d < n),
      f ⟨b, by omega⟩ + d ≤ f ⟨b + d, h⟩ := by
    intro b d
    induction d with
    | zero => intro h; simp
    | succ d ih =>
        intro h
        have hi := ih (by omega)
        have hh : f ⟨b + d, by omega⟩ < f ⟨b + (d + 1), h⟩ := hf (by simp)
        omega
  have he : i.val + (j.val - i.val) = j.val := Nat.add_sub_of_le hij
  simpa only [he] using aux i.val (j.val - i.val) (by omega)

theorem div_strict_of_equal_residue {n P : ℕ} (hP : 0 < P)
    (f : Fin n → ℕ) (hf : StrictMono f) {i j : Fin n}
    (hij : i < j) (hmod : i.val % P = j.val % P) : f i / P < f j / P := by
  have hid := Nat.mod_add_div i.val P
  have hjd := Nat.mod_add_div j.val P
  have hq : i.val / P < j.val / P := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left P (Nat.le_of_not_gt hn)
    have : j.val ≤ i.val := by omega
    exact (not_le_of_gt hij) this
  have hmul := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hq)
  have hgap : P ≤ j.val - i.val := by
    rw [Nat.mul_succ] at hmul
    omega
  have hg := strictMono_fin_gap f hf i j (le_of_lt hij)
  have h : f i + P ≤ f j := by omega
  have hd := Nat.div_le_div_right (c := P) h
  rw [Nat.add_div_right _ hP] at hd
  omega

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit


theorem solution : type_of% @_root_.OAI.TreeEdit.div_strict_of_equal_residue := @_root_.OAI.TreeEdit.div_strict_of_equal_residue

-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.sampledWord_tiny
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:56:13.156973+00:00
-- url     : https://prove2.me/submissions/f4f276fe-1ebb-406a-904f-c88a79c58f0e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean:L242-L265
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.sampledWord_tiny. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Theorems.Thm_OAI_TreeEdit_TorusTree_sampledWord_diagonal_step

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, mul_add]

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.EditMetric ----
namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

end EditScript

variable {α : Type u} {x y z : List α}

theorem ed_triangle (x y z : List α) : ed x z ≤ ed x y + ed y z :=
  ed_le_of_script ((ed_script x y).trans (ed_script y z))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.RandomCircle ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma mean_translate {A : Type*} [Fintype A] [AddGroup A] (y : A) (f : A → ℝ) :
    mean (fun x => f (x + y)) = mean f := mean_equiv (Equiv.addRight y) f

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma mean_ed_add {A β : Type*} [Fintype A] [AddCommGroup A] (f : A → List β) (u v : A) :
    mean (fun x => (ed (f x) (f (x + (u + v))) : ℝ)) ≤
      mean (fun x => (ed (f x) (f (x + u)) : ℝ)) + mean (fun x => (ed (f x) (f (x + v)) : ℝ)) := by
  have hh := mean_le (fun x => (Nat.cast_le (α := ℝ)).mpr (ed_triangle (f x) (f (x+u)) (f (x+(u+v)))))
  simp only [Nat.cast_add, ← add_assoc] at hh
  rw [mean_add, mean_translate u (fun x => (ed (f x) (f (x+v)) : ℝ))] at hh
  simpa only [add_assoc] using hh

lemma mean_ed_nsmul {A β : Type*} [Fintype A] [AddCommGroup A] (f : A → List β) (u : A) (a : ℕ) :
    mean (fun x => (ed (f x) (f (x + a • u)) : ℝ)) ≤
      a * mean (fun x => (ed (f x) (f (x + u)) : ℝ)) := by
  induction a with
  | zero => simp [ed_self, mean]
  | succ a ih =>
    rw [succ_nsmul]
    apply (mean_ed_add f _ _).trans
    calc
      _ ≤ (a : ℝ) * mean (fun x => (ed (f x) (f (x+u)) : ℝ)) + mean (fun x => (ed (f x) (f (x+u)) : ℝ)) := add_le_add ih (le_refl _)
      _ = _ := by push_cast; ring

lemma sampledWord_tiny {I : Type} {g s L M T R D Q J : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R * D) (hMQ : M = J * Q)
    (h : ℕ) (C : Config I L (g*s) h) (a : ℕ) (ha : a ≤ J) :
    mean (fun x : State (ZMod M) (g*s) h =>
      (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g*s) h (a : ZMod M))).val : ℝ)) ≤
      (FiniteTree.length (g*s) T h : ℝ) * R / Q := by
  have he : diagonal (A := ZMod M) (m := g*s) h (a : ZMod M) = a • diagonal (A := ZMod M) (m := g*s) h 1 := by
    rw [← map_nsmul]; simp [nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ a * mean (fun x => (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g*s) h 1)).val : ℝ)) := mean_ed_nsmul _ _ _
    _ ≤ (a : ℝ) * ((FiniteTree.length (g*s) T h : ℝ) / D) :=
      mul_le_mul_of_nonneg_left (sampledWord_diagonal_step r j hr hPM hD hMR h C) (by positivity)
    _ ≤ (J : ℝ) * ((FiniteTree.length (g*s) T h : ℝ) / D) := mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
    _ = _ := by
      have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have he : (R : ℝ) * D = (J : ℝ) * Q := by exact_mod_cast hMR.symm.trans hMQ
      field_simp
      nlinarith

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.sampledWord_tiny := @_root_.OAI.TreeEdit.TorusTree.sampledWord_tiny

-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:50:17.460403+00:00
-- url     : https://prove2.me/submissions/b48f5904-3463-4055-8c30-0b76c5452a41

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeCosts.lean:L210-L236
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_CheapTranslations_script_rowWindow_shift
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_descendant_script

-- ---- from OAI.Combinatorics.BinaryEdit.CheapTranslations ----
namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

theorem editDistance_le_script {x y : List α} {n : ℕ}
    (h : EditScript x y n) : ed x y ≤ n := by
  exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h

theorem rowWindow_shift_index (rows : ℕ → List α) (a s n : ℕ) :
    rowWindow (fun j => rows (s + j)) a n = rowWindow rows (s + a) n := by
  induction n generalizing a with
  | zero => simp [rowWindow]
  | succ n ih =>
      simp only [rowWindow, List.range'_succ, List.flatMap_cons]
      change rows (s + a) ++ rowWindow (fun j => rows (s + j)) (a + 1) n =
        rows (s + a) ++ rowWindow rows (s + a + 1) n
      rw [ih, Nat.add_assoc]

theorem orbitRows_shift {A : Type v} [AddMonoid A] (row : A → List α)
    (x u : A) (T s : ℕ) :
    orbitRows row (x + s • u) u T =
      rowWindow (fun j => row (x + j • u)) s T := by
  unfold orbitRows
  have hfun : (fun j : ℕ => row (x + s • u + j • u)) =
      (fun j : ℕ => row (x + (s + j) • u)) := by
    funext j
    rw [add_nsmul, add_assoc]
  rw [hfun]
  simpa only [Nat.add_zero] using
    rowWindow_shift_index (fun j => row (x + j • u)) 0 s T

/-- An additive state translation by `s*u` is the exact row-window script,
also when `x` already includes offsets contributed by ancestor nodes. -/
theorem script_orbitRows_shift {A : Type v} [AddMonoid A]
    (row : A → List α) (x u : A) (T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ y, (row y).length = B) :
    EditScript (orbitRows row x u T) (orbitRows row (x + s • u) u T)
      (2 * s * B) := by
  rw [orbitRows_shift]
  simpa only [orbitRows, Nat.zero_add] using
    script_rowWindow_shift (fun j => row (x + j • u)) 0 T s B hs
      (fun j => hlen _)

end TreeEdit.BinaryLower.CheapTranslations

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeCosts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Inexpensive scripts in the recursive row evaluator

Local row advancement and descendant-occurrence lifting establish
`lem:finite-cost` from geometric hypotheses on state translations and
invisible leaf decoders.
-/

namespace TreeEdit.BinaryLower.FiniteTree

open CheapTranslations

variable {A Γ : Type*} [AddCommMonoid A]

theorem nodeWord_eq_orbitRows {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    nodeWord T leaf u (h + 1) p x =
      orbitRows (nodeRow T leaf u h p) x (u p) T := by
  simp only [nodeWord, orbitRows, rowWindow, nodeRow, List.range_eq_range']

/-- Advancing the rows in one node has exactly the source's deletion/insertion
script cost, uniformly in its state (including all ancestor offsets). -/
theorem nodeWord_cheap_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) (s : ℕ) (hs : s ≤ T) :
    EditScript (nodeWord T leaf u (h + 1) p x)
      (nodeWord T leaf u (h + 1) p (x + s • u p))
      (2 * s * m * (m * T) ^ h) := by
  rw [nodeWord_eq_orbitRows, nodeWord_eq_orbitRows]
  simpa only [Nat.mul_assoc] using
    script_orbitRows_shift (nodeRow T leaf u h p) x (u p) T s
      (m * (m * T) ^ h) hs (nodeRow_length T leaf u h p)

/-- Combined local row advancement and occurrence lifting, with exactly the
cost `T^depth * 2*s*rowLength` used in the finite-tree construction. -/
theorem nodeWord_descendant_cheap_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q)))
      (T ^ q.length * (2 * s * m * (m * T) ^ h)) :=
  nodeWord_descendant_script T leaf u (h + 1) q p (s • u (p ++ q))
    (2 * s * m * (m * T) ^ h)
    (fun y => nodeWord_cheap_script T leaf u h (p ++ q) y s hs) houtside x

theorem nodeWord_descendant_cheap_editDistance {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) ≤
      T ^ q.length * (2 * s * m * (m * T) ^ h) :=
  editDistance_le_script
    (nodeWord_descendant_cheap_script T leaf u h q p s hs houtside x)

/-- Equation `eq:finite-cost` for the recursive word evaluator: a depth-j
translation by s cheap node steps costs at most `(2s/T) M/m^j`.
The decoder-locality hypothesis is exactly what makes other subtrees unchanged. -/
theorem nodeWord_descendant_normalized_bound {m : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    (ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) : ℝ) ≤
      (2 * (s : ℝ) / T) *
        (((m * T : ℕ) : ℝ) ^ (h + 1 + q.length) / (m : ℝ) ^ q.length) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hb := nodeWord_descendant_cheap_editDistance T leaf u h q p s hs houtside x
  have hn : (ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) : ℝ) ≤
      (T : ℝ) ^ q.length * (2 * (s : ℝ) * m * ((m : ℝ) * T) ^ h) := by
    exact_mod_cast hb
  calc
    _ ≤ (T : ℝ) ^ q.length * (2 * (s : ℝ) * m * ((m : ℝ) * T) ^ h) := hn
    _ = _ := by
      simp only [Nat.cast_mul, pow_add, pow_one, mul_pow]
      field_simp

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open CheapTranslations


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_normalized_bound

-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:21:30.942141+00:00
-- url     : https://prove2.me/submissions/72d39ef0-088b-4dee-a963-394e3bcac6be

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteSeparationArithmetic.lean:L13-L29
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSeparationArithmetic ----
namespace OAI

/-!
# Deficit charges in the finite-tree separation induction

The exact deficit charges are those of `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- At least half the children each charge `q` unmatched symbols. -/
theorem row_deficit_charge {m : ℕ} (bad : Finset (Fin m))
    (δ : Fin m → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hnonneg : ∀ i, 0 ≤ δ i) (hbad : ∀ i ∈ bad, q ≤ δ i)
    (hhalf : m ≤ 2 * bad.card) :
    (m : ℝ) * q / 2 ≤ ∑ i, δ i := by
  classical
  have hpoint (i : Fin m) : (if i ∈ bad then q else 0) ≤ δ i := by
    split_ifs with hi
    · exact hbad i hi
    · exact hnonneg i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcalc : (∑ i : Fin m, if i ∈ bad then q else 0) = (bad.card : ℝ) * q := by
    simp
  rw [hcalc] at hsum
  have hmR : (m : ℝ) ≤ 2 * (bad.card : ℝ) := by exact_mod_cast hhalf
  nlinarith [mul_le_mul_of_nonneg_right hmR hq]

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.row_deficit_charge

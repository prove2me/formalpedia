-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:09:25.545356+00:00
-- url     : https://prove2.me/submissions/048116a2-5364-47a9-9c43-de5993877e4f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L325-L345
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_character_multiplier_average

-- ---- from OAI.Combinatorics.BinaryEdit.SparseActivity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- Averaging the Fourier expansion along any finite subgroup homomorphism
is twice the Fourier weight of characters nontrivial on that subgroup. -/
theorem subgroup_average_spectral_mass {A G : Type*}
    [AddCommGroup A] [Fintype A] [AddCommGroup G] [Fintype G]
    (φ : G →+ A) (H : AddChar A ℂ → ℝ) :
    (∑ z : G, ∑ χ : AddChar A ℂ, ‖1 - χ (φ z)‖ ^ 2 * H χ) /
        (Fintype.card G : ℝ) =
      2 * ∑ χ : AddChar A ℂ, if χ.compAddMonoidHom φ = 0 then 0 else H χ := by
  classical
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.sum_mul]
  have havg := character_multiplier_average (χ.compAddMonoidHom φ)
  change (∑ z : G, ‖1 - χ (φ z)‖ ^ 2) / (Fintype.card G : ℝ) =
    (if χ.compAddMonoidHom φ = 0 then 0 else 2) at havg
  calc
    (∑ z : G, ‖1 - χ (φ z)‖ ^ 2) * H χ / (Fintype.card G : ℝ) =
        ((∑ z : G, ‖1 - χ (φ z)‖ ^ 2) / (Fintype.card G : ℝ)) * H χ := by ring
    _ = (if χ.compAddMonoidHom φ = 0 then 0 else 2) * H χ := by rw [havg]
    _ = 2 * (if χ.compAddMonoidHom φ = 0 then 0 else H χ) := by split_ifs <;> simp

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass

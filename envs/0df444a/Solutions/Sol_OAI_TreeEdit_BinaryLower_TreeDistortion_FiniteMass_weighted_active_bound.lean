-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:59:51.49616+00:00
-- url     : https://prove2.me/submissions/f0b286cb-4ec4-4331-895c-1956b460d10d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L57-L96
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.SparseActivity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- A weighted version of the sparse/dense activity dichotomy.
The exceptional set may overlap the inactive set.  No disjointness assumptions
on the tests used to bound exceptional mass are required. -/
theorem weighted_active_bound {ι : Type*} [Fintype ι]
    (H w μ : ι → ℝ) (active exceptional : ι → Prop)
    (M ε K : ℝ) (hK : 0 < K)
    (hH : ∀ i, 0 ≤ H i) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, μ i ≤ 4)
    (hzero : ∀ i, ¬ active i → μ i = 0)
    (hdense : ∀ i, active i → ¬ exceptional i → K ≤ w i)
    (hleaf : 2 * ∑ i, w i * H i ≤ M)
    (hexceptional : (∑ i, if exceptional i then H i else 0) ≤ ε) :
    (∑ i, μ i * H i) ≤ 4 * (ε + M / (2 * K)) := by
  classical
  have hpoint : ∀ i, μ i * H i ≤
      4 * ((if exceptional i then H i else 0) + w i * H i / K) := by
    intro i
    have hmass : 0 ≤ w i * H i / K :=
      div_nonneg (mul_nonneg (hw i) (hH i)) (le_of_lt hK)
    by_cases he : exceptional i
    · simp only [ite_eq_left he]
      have := mul_le_mul_of_nonneg_right (hμ i) (hH i)
      linarith
    · simp only [ite_eq_right he, zero_add]
      by_cases ha : active i
      · have hlarge : H i ≤ w i * H i / K := by
          apply (le_div_iff₀ hK).2
          nlinarith [hdense i ha he, hH i]
        have := mul_le_mul_of_nonneg_right (hμ i) (hH i)
        linarith
      · rw [hzero i ha, zero_mul]
        positivity
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hsum' : (∑ i, μ i * H i) ≤
      4 * ((∑ i, if exceptional i then H i else 0) + (∑ i, w i * H i) / K) := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div] using hsum
  have hleaf' : (∑ i, w i * H i) / K ≤ M / (2 * K) := by
    apply (div_le_div_iff₀ hK (mul_pos (by norm_num) hK)).2
    nlinarith
  linarith

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_active_bound

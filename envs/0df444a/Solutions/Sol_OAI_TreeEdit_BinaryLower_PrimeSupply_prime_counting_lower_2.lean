-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:28:46.17167+00:00
-- url     : https://prove2.me/submissions/4491ac74-190f-40dc-aeed-f66ec445a487

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSupply.lean:L11-L33
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_lower. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSupply ----
namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- The elementary Chebyshev lower bound in the form used by the manuscript. -/
theorem prime_counting_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2 / 4 by positivity)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Real.log 2 / 4, by positivity, max 4 a, ?_⟩
  intro x hx
  have hx4 : 4 ≤ x := le_trans (le_max_left _ _) hx
  have hxa : a ≤ x := le_trans (le_max_right _ _) hx
  have hbound := ha (x + 2) (by linarith)
  have hx2 : 0 ≤ x + 2 := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx2] at hbound
  have hlogbound : Real.log (x + 2) ≤ (Real.log 2 / 4) * (x + 2) :=
    (le_abs_self _).trans hbound
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    (Real.log 2 / 4) * x / Real.log x ≤
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hxlog.le
      nlinarith
    _ ≤ _ := Chebyshev.pi_ge' (by linarith)

end TreeEdit.BinaryLower.PrimeSupply

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSupply
open Filter Finset
open scoped Topology


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_lower := @_root_.OAI.TreeEdit.BinaryLower.PrimeSupply.prime_counting_lower

-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Parameters.exists_finiteLength_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:20:30.981164+00:00
-- url     : https://prove2.me/submissions/b57ebbdb-e267-4a51-a065-e92db65cdc9f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteParameters.lean:L176-L193
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Parameters.exists_finiteLength_bracket. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteParameters ----
namespace OAI

namespace TreeEdit.BinaryLower.Parameters

lemma le_finiteLength {k : ℕ} (hk : 0 < k) : k ≤ finiteLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow (by omega : 0 < 3 * k))

/-- Choose adjacent construction lengths bracketing a cap.  No strict
monotonicity of the length sequence is needed for this selection argument. -/
lemma exists_finiteLength_bracket {k₀ d : ℕ} (hk₀ : 0 < k₀)
    (hd : finiteLength k₀ ≤ d) :
    ∃ k : ℕ, k₀ ≤ k ∧ finiteLength k ≤ d ∧ d < finiteLength (k + 1) := by
  have hex : ∃ n : ℕ, d < finiteLength (k₀ + n + 1) := by
    refine ⟨d, ?_⟩
    have hb := le_finiteLength (by omega : 0 < k₀ + d + 1)
    omega
  let n : ℕ := Nat.find hex
  refine ⟨k₀ + n, by omega, ?_, ?_⟩
  · by_cases hn : n = 0
    · simpa only [hn, Nat.add_zero] using hd
    · have hmin := Nat.find_min hex (m := n - 1) (by dsimp [n] at hn ⊢; omega)
      have heq : k₀ + (n - 1) + 1 = k₀ + n := by omega
      rw [heq] at hmin
      exact Nat.le_of_not_gt hmin
  · exact Nat.find_spec hex

end TreeEdit.BinaryLower.Parameters

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Parameters.exists_finiteLength_bracket := @_root_.OAI.TreeEdit.BinaryLower.Parameters.exists_finiteLength_bracket

-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:52:04.311336+00:00
-- url     : https://prove2.me/submissions/d9bc4cdf-0ea5-4314-8c36-d9e357452148

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeConcreteCosts.lean:L91-L113
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_descendant_normalized_bound

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry ----
namespace OAI

/-! Concrete tagged leaf states and subtree locality for the finite tree. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- At a valid leaf, equality is exactly equality of that leaf's state. -/
theorem leafDecoder_eq_iff {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x y : State Q) :
    leafDecoder Q base p x = leafDecoder Q base p y ↔
      x ⟨p, hp⟩ = y ⟨p, hp⟩ := by
  simp [leafDecoder, hp]

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeConcreteCosts ----
namespace OAI

/-!
Concrete tagged cyclic-state versions of `lem:finite-cost`. The only input
about a translated vector is its actual coordinate support. In particular no
injectivity of the word map, period identity, or distortion hypothesis is used.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- Exactly the root-word normalized row-translation estimate, for the tagged
cyclic-state decoder and a subtree-supported cheap vector. -/
theorem root_internal_supported_normalized_cost {m k : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (Q : Leaf m k → ℕ) (base : Leaf m k)
    (u : List (Fin m) → State Q) (h : ℕ) (q : List (Fin m))
    (hlen : h + 1 + q.length = k) (s : ℕ) (hs : s ≤ T)
    (hsupport : ∀ l : Leaf m k, ¬ q.IsPrefix l.val → u q l = 0)
    (x : State Q) :
    (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + s • u q)) : ℝ) ≤
      (2 * (s : ℝ) / T) * (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ q.length) := by
  have hout : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leafDecoder Q base ([] ++ r) (y + s • u ([] ++ q)) =
          leafDecoder Q base ([] ++ r) y := by
    intro r hr hn y
    have hrk : r.length = k := hr.trans hlen
    apply (leafDecoder_eq_iff Q base r hrk (y + s • u ([] ++ q)) y).2
    simp only [List.nil_append, Pi.add_apply, Pi.smul_apply,
      hsupport ⟨r, hrk⟩ hn, smul_zero, add_zero]
  simpa only [hlen, List.nil_append] using
    nodeWord_descendant_normalized_bound T hm hT (leafDecoder Q base) u h q [] s hs hout x

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.root_internal_supported_normalized_cost

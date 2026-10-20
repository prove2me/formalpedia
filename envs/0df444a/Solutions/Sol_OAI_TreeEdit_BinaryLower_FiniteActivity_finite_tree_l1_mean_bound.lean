-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:35:42.140234+00:00
-- url     : https://prove2.me/submissions/ef957dd0-9a4b-4c6c-9077-70e968b95537

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteL1Tree.lean:L21-L50
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_finite_tree_spectral_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_finite_group_displacement

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteL1Tree ----
namespace OAI

/-!
# Actual ℓ₁ maps and the finite-tree obstruction

The finite-group displacement identity yields the finite-tree root estimate
from geometric bounds on the concrete translations.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical
open scoped BigOperators

/-- Leaf periods, sparse-character detection and translation-cost bounds
imply the root averaged-distance estimate for arbitrary maps into ℓ₁. -/
theorem finite_tree_l1_mean_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (F : A → RealL1)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)) x,
      ‖F (x + φ f z) - F x‖ ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s x,
      ‖F (x + shift v s) - F x‖ ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (𝔼 x : A, ‖F (x + w []) - F x‖) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by
  classical
  obtain ⟨H, hH, hFourier⟩ := finite_group_displacement F
  rw [hFourier]
  apply finite_tree_spectral_bound m b h hm hb w Q φ hgen H hH shift M C
  · intro f z
    rw [← hFourier]
    exact Finset.expect_le Finset.univ_nonempty (fun x _ => hleaf f z x)
  · exact hdetect
  · intro v s
    rw [← hFourier]
    exact Finset.expect_le Finset.univ_nonempty (fun x _ => hcost v s x)

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound := @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_l1_mean_bound

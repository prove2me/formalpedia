-- Prove2me | solution 1 for OAI.DiscreteFree.MetricWedge.separated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:04:34.646191+00:00
-- url     : https://prove2.me/submissions/d5d868ff-84eb-44e2-8be2-d26fcf5b2a64

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean:L21-L35
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricWedge.separated. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge

-- ---- from OAI.Analysis.LipschitzFree.RetainedWedge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-!
# Separated metric wedges and bounded finite-component retracts
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem separated (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (x y : Point M o) (hxy : x ≠ y) : 1 ≤ dist x y := by
  change 1 ≤ distance M o x y
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩
  · exact False.elim (hxy rfl)
  · exact sep m y.val (o m) y.property
  · exact sep n x.val (o n) x.property
  · by_cases h : n = m
    · subst m
      simp only [distance,dite_true]
      apply sep n x.val y.val
      intro h
      exact hxy (congrArg (fun t : {x : M n // x ≠ o n} => (some ⟨n,t⟩ : Point M o)) (Subtype.ext h))
    · simp only [distance,dite_eq_right h]
      linarith [sep n x.val (o n) x.property,sep m y.val (o m) y.property]

end DiscreteFree.MetricWedge
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricWedge
open scoped BigOperators ENNReal
open scoped Classical BigOperators


theorem solution.{u} : type_of% @_root_.OAI.DiscreteFree.MetricWedge.separated.{u} := @_root_.OAI.DiscreteFree.MetricWedge.separated.{u}

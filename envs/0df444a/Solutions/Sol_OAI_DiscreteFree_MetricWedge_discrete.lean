-- Prove2me | solution 1 for OAI.DiscreteFree.MetricWedge.discrete
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:06:59.995622+00:00
-- url     : https://prove2.me/submissions/295479f6-af7d-4890-a63b-4850e72030a9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean:L37-L52
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricWedge.discrete. The node keeps its source
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
import Theorems.Thm_OAI_DiscreteFree_MetricWedge_separated

-- ---- from OAI.Analysis.LipschitzFree.RetainedWedge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem discrete (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y) :
    DiscreteTopology (Point M o) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have hball : Metric.ball x 1 = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      by_contra h
      have hh := separated M o sep y x h
      exact (not_lt_of_ge hh) hy
    · rintro rfl
      simp
  rw [← hball]
  exact Metric.isOpen_ball

end DiscreteFree.MetricWedge
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricWedge
open scoped BigOperators ENNReal
open scoped Classical BigOperators


theorem solution.{u} : type_of% @_root_.OAI.DiscreteFree.MetricWedge.discrete.{u} := @_root_.OAI.DiscreteFree.MetricWedge.discrete.{u}

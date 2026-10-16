-- Prove2me | solution 1 for OAI.DiscreteFree.hasBAP_of_contractive_retract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:09:38.855565+00:00
-- url     : https://prove2.me/submissions/6ecfbf1e-bb1a-4e29-9df1-e30a00abac81

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean:L37-L56
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.hasBAP_of_contractive_retract. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation

-- ---- from OAI.Analysis.LipschitzFree.WedgeApproximation ----
namespace OAI

/-!
# Compact-uniform approximation on wedges and contractive BAP inheritance
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical BigOperators

section OperatorTools
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contraction_norm (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : E) : ‖T u‖ ≤ ‖u‖ := by
  exact (T.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg u))

theorem finiteRank_sandwich (I : G →L[ℝ] H) (T : F →L[ℝ] G) (P : E →L[ℝ] F)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) :
    Module.Finite ℝ (LinearMap.range ((I.comp T).comp P).toLinearMap) := by
  have hfg := ((Submodule.fg_iff_finiteDimensional _).mpr hT).map I.toLinearMap
  apply (Submodule.fg_iff_finiteDimensional _).mp
  apply hfg.of_le
  rintro v ⟨u,rfl⟩
  exact ⟨T (P u),⟨P u,rfl⟩,rfl⟩

theorem hasBAP_of_contractive_retract (I : E →L[ℝ] F) (P : F →L[ℝ] E)
    (hI : ‖I‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPI : P.comp I = ContinuousLinearMap.id ℝ E)
    (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by
  intro C hC ε hε
  obtain ⟨U,hU,hn,η,hη,he⟩ := h (I '' C) (hC.image I.continuous) ε hε
  let T := (P.comp U).comp I
  refine ⟨T,finiteRank_sandwich P U I hU,?_,η,hη,?_⟩
  · apply le_trans _ hn
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
    intro u
    calc
      ‖T u‖ ≤ ‖U (I u)‖ := contraction_norm P hP _
      _ ≤ ‖U‖ * ‖I u‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖u‖ := mul_le_mul_of_nonneg_left (contraction_norm I hI u) (norm_nonneg U)
  · intro u hu
    have hpu : P (I u) = u := congrArg (fun A : E →L[ℝ] E => A u) hPI
    calc
      ‖T u-u‖ = ‖P (U (I u)-I u)‖ := by dsimp [T]; rw [map_sub,hpu]
      _ ≤ ‖U (I u)-I u‖ := contraction_norm P hP _
      _ ≤ η := he _ ⟨u,hu,rfl⟩
end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

end MetricWedge
end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped Classical BigOperators


theorem solution : type_of% @_root_.OAI.DiscreteFree.hasBAP_of_contractive_retract := @_root_.OAI.DiscreteFree.hasBAP_of_contractive_retract

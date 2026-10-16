-- Prove2me | solution 1 for OAI.DiscreteFree.labelBump_sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:44:38.634552+00:00
-- url     : https://prove2.me/submissions/adc87d72-9cfd-4c56-ac37-503370606269

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/LabelBumps.lean:L35-L49
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.labelBump_sub. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzFree.LabelBumps ----
namespace OAI

/-!
# Lipschitz label bumps and affine mass estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

theorem labelBump_sub (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (x y : M) :
    |labelBump h a L K x - labelBump h a L K y| ≤ (L/K) * dist x y := by
  unfold labelBump
  rw [← mul_sub, abs_mul, abs_of_nonneg hL]
  have hh' : dist (h x) (h y) ≤ dist x y := by simpa using hh.dist_le_mul x y
  calc
    _ ≤ L * |(1-dist a (h x)/K) - (1-dist a (h y)/K)| :=
      mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ 0) hL
    _ = (L/K) * |dist a (h x) - dist a (h y)| := by
      rw [show (1-dist a (h x)/K) - (1-dist a (h y)/K) =
        -(dist a (h x)-dist a (h y))/K by ring, abs_div, abs_neg, abs_of_pos hK]
      ring
    _ ≤ (L/K) * dist x y := mul_le_mul_of_nonneg_left
      ((show |dist a (h x) - dist a (h y)| ≤ dist (h x) (h y) by simpa only [dist_comm] using abs_dist_sub_le (h x) (h y) a).trans hh') (div_nonneg hL hK.le)

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.labelBump_sub := @_root_.OAI.DiscreteFree.labelBump_sub

-- Prove2me | solution 1 for OAI.DiscreteFree.affine_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:43:16.243808+00:00
-- url     : https://prove2.me/submissions/b2b2d39c-f634-408c-8fd1-437023ed3668

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/AffineWeights.lean:L95-L115
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.affine_difference_bound. The node keeps its source
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
import Theorems.Thm_OAI_DiscreteFree_affineWeights_pairing

-- ---- from OAI.Analysis.LipschitzFree.Coordinates ----
namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem dualPairing_bound (f : Lip0 o) (u : FreeSpace o) : |dualPairing o f u| ≤ ‖u‖ * ‖f‖ :=
  u.val.le_opNorm f

namespace Lip0
theorem center_norm_le (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : ‖center o g L hL hg‖ ≤ L := by
  apply (norm_le_iff _ hL).mpr
  intro x y
  simpa using hg x y
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.AffineWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Affine signed coefficients and quantitative pairing bounds
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

end DiscreteFree
end

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

theorem affine_difference_bound (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (c : ℝ) (hn : ‖T‖ ≤ c)
    (g : M → ℝ) (hg : LipschitzWith 1 g) (x y : M) :
    |pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => g j.val) -
      pairing (affineWeights o sep S ho (T (delta o y))) (fun j : S => g j.val)| ≤
        c * dist x y := by
  have hgl (s t : M) : |g s - g t| ≤ 1 * dist s t := by
    simpa only [Real.dist_eq, NNReal.coe_one] using hg.dist_le_mul s t
  let f := Lip0.center o g 1 (by norm_num) hgl
  have hf : ‖f‖ ≤ 1 := Lip0.center_norm_le o g 1 (by norm_num) hgl
  rw [affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl,
    affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl]
  rw [show dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o x)) + g o -
      (dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o y)) + g o) =
      dualPairing o f (T (delta o x - delta o y)) by rw [map_sub, map_sub]; ring]
  calc
    _ ≤ ‖T (delta o x - delta o y)‖ * ‖f‖ := dualPairing_bound o f _
    _ ≤ ‖T (delta o x - delta o y)‖ := mul_le_of_le_one_right (norm_nonneg _) hf
    _ ≤ ‖T‖ * ‖delta o x - delta o y‖ := T.le_opNorm _
    _ ≤ c * dist x y := by rw [delta_sub_norm]; exact mul_le_mul_of_nonneg_right hn dist_nonneg

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.affine_difference_bound := @_root_.OAI.DiscreteFree.affine_difference_bound

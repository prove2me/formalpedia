-- Prove2me | solution 1 for OAI.DiscreteFree.affineWeights_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:38:56.152713+00:00
-- url     : https://prove2.me/submissions/680bccb1-f398-4ba4-9d56-49530c004892

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/AffineWeights.lean:L30-L46
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.affineWeights_pairing. The node keeps its source
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

theorem affineWeights_pairing (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) (g : M → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ x y, |g x - g y| ≤ C * dist x y) :
    pairing (affineWeights o sep S ho u) (fun j : S => g j.val) =
      dualPairing o (Lip0.center o g C hC hg) u + g o := by
  have he : dualPairing o (Lip0.center o g C hC hg) u =
      ∑ j : S, coordinate o sep j.val u * (g j.val - g o) := by
    conv_lhs => rw [← hu]
    rw [supportProjection_apply]
    simp only [map_sum, map_smul, dualPairing_delta, Lip0.center_apply, smul_eq_mul]
    exact (Finset.sum_coe_sort S _).symm
  rw [he]
  simp only [pairing, affineWeights, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

end DiscreteFree
end

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.affineWeights_pairing := @_root_.OAI.DiscreteFree.affineWeights_pairing

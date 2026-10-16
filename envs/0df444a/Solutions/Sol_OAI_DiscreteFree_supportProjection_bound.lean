-- Prove2me | solution 1 for OAI.DiscreteFree.supportProjection_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:33:39.809096+00:00
-- url     : https://prove2.me/submissions/feec1fab-80b1-46ab-9c90-fa0b88c56d56

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Coordinates.lean:L139-L151
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.supportProjection_bound. The node keeps its source
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
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

omit [MetricSpace M] in
theorem sum_point_test {V : Type*} [AddCommMonoid V] (F : Finset M) (x : M) (v : M → V) :
    (∑ j ∈ F, if x = j ∧ j ≠ o then v j else 0) = if x ∈ F ∧ x ≠ o then v x else 0 := by
  have ht (j : M) : (if x = j ∧ j ≠ o then v j else 0) =
      if j = x then (if x ≠ o then v x else 0) else 0 := by
    by_cases h : j = x
    · subst j; simp
    · simp [h, Ne.symm h]
  simp_rw [ht]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem sum_abs_coordinate_le (F : Finset M) (u : FreeSpace o) :
    ∑ j ∈ F, |coordinate o sep j u| ≤ 2 * ‖u‖ := by
  let c : M → ℝ := fun j => if 0 ≤ coordinate o sep j u then 1 else -1
  let f : Lip0 o := ∑ j ∈ F, c j • indicator o sep j
  have hfc (x : M) : f x = if x ∈ F ∧ x ≠ o then c x else 0 := by
    change evaluation o x (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, evaluation_apply, indicator_apply, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    exact sum_point_test o F x c
  have hcb (x : M) : -1 ≤ f x ∧ f x ≤ 1 := by
    rw [hfc]
    dsimp [c]
    split_ifs <;> norm_num
  have hf : ‖f‖ ≤ 2 := (Lip0.norm_le_iff f (by norm_num)).mpr (by
    intro x y
    convert bounded_test_lipschitz sep hcb x y using 1; norm_num)
  have hpair : dualPairing o f u = ∑ j ∈ F, |coordinate o sep j u| := by
    change u.val (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    change c j * coordinate o sep j u = _
    dsimp [c]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hh := (dualPairing_bound o f u).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg u))
  rw [hpair, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)), mul_comm] at hh
  exact hh

theorem supportProjection_bound (F : Finset M) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, dist x o ≤ B) : ‖supportProjection o sep F‖ ≤ 2*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [supportProjection_apply]
  calc
    ‖∑ j ∈ F, coordinate o sep j u • delta o j‖ ≤
        ∑ j ∈ F, ‖coordinate o sep j u • delta o j‖ := norm_sum_le _ _
    _ = ∑ j ∈ F, |coordinate o sep j u| * dist j o := by simp only [norm_smul, Real.norm_eq_abs, delta_norm]
    _ ≤ ∑ j ∈ F, |coordinate o sep j u| * B := by gcongr with j hj; exact hb j
    _ = (∑ j ∈ F, |coordinate o sep j u|) * B := (Finset.sum_mul ..).symm
    _ ≤ (2 * ‖u‖) * B := mul_le_mul_of_nonneg_right (sum_abs_coordinate_le o sep F u) hB
    _ = (2*B) * ‖u‖ := by ring

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.supportProjection_bound := @_root_.OAI.DiscreteFree.supportProjection_bound

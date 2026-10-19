-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:28:12.959267+00:00
-- url     : https://prove2.me/submissions/b788f491-272e-4ca9-a08b-4b7179a4df65

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L875-L891
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

variable {T}

variable (T)

lemma coefficientBall_convex (K : Finset ι) (R : ℝ) :
    Convex ℝ (T.coefficientBall K R) := by
  intro c hc d hd a b ha hb hab
  change ∑ F, ‖a • c F + b • d F‖ ≤ R
  calc
    _ ≤ ∑ F, (a * ‖c F‖ + b * ‖d F‖) := by
      apply Finset.sum_le_sum
      intro F _
      calc
        ‖a • c F + b • d F‖ ≤ ‖a • c F‖ + ‖b • d F‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * (∑ F, ‖c F‖) + b * (∑ F, ‖d F‖) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hc ha)
      (mul_le_mul_of_nonneg_left hd hb)
    _ = R := by rw [← add_mul, hab, one_mul]

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex := @_root_.OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex

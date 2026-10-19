-- Prove2me | solution 2 for OAI.C0Absorption.absorption_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:56:12.23716+00:00
-- url     : https://prove2.me/submissions/c418c874-32ab-4965-96e4-8103d3f975b7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Triangular.lean:L35-L58
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.absorption_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

-- ---- from OAI.Analysis.C0Absorption.Triangular ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem absorption_upper {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) {LK : ℝ}
    (hLK : 0 ≤ LK) (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y) :
    ∀ x y, dist (absorptionMap Q K x) (absorptionMap Q K y) ≤
      (1+LK * max 1 ‖Q‖) * dist x y := by
  intro x y
  have hq : dist (Q x.1) (Q y.1) ≤ ‖Q‖ * dist x y :=
    (Q.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) (norm_nonneg Q))
  have ht : dist x.2 y.2 ≤ max 1 ‖Q‖ * dist x y := by
    calc
      dist x.2 y.2 ≤ dist x y := (by rw [Prod.dist_eq]; exact le_max_right _ _ : dist x.2 y.2 ≤ dist x y)
      _ = 1 * dist x y := (one_mul _).symm
      _ ≤ max 1 ‖Q‖ * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hinput : dist (x.2, Q x.1) (y.2, Q y.1) ≤ max 1 ‖Q‖ * dist x y := by
    rw [Prod.dist_eq]
    exact max_le ht (hq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))
  calc
    dist (absorptionMap Q K x) (absorptionMap Q K y)
      ≤ dist x.1 y.1 + dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_add_add_le _ _ _ _
    _ ≤ dist x y + LK * (max 1 ‖Q‖ * dist x y) :=
      add_le_add ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK))
    _ = _ := by ring

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators


theorem solution : type_of% @_root_.OAI.C0Absorption.absorption_upper := @_root_.OAI.C0Absorption.absorption_upper

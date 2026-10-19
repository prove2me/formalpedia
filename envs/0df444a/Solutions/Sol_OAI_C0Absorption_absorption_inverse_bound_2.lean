-- Prove2me | solution 2 for OAI.C0Absorption.absorption_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:58:10.413753+00:00
-- url     : https://prove2.me/submissions/8f4a2f4a-1edc-4b21-987f-7a60225e6aba

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Triangular.lean:L60-L95
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.absorption_inverse_bound. The node keeps its source
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

theorem absorption_inverse_bound {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    {LK cg : ℝ} (hLK : 0 ≤ LK) (hcg : 0 < cg)
    (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y)
    (hg : ∀ x y, cg * dist x y ≤ dist (g x) (g y))
    (hQK : ∀ x : E × U, Q (K x) = g x-x.2) :
    ∀ x y, dist x y ≤ max (1+LK*‖Q‖/cg) (‖Q‖/cg) *
      dist (absorptionMap Q K x) (absorptionMap Q K y) := by
  intro x y
  let F := absorptionMap Q K
  have hQF (a : Z × E) : Q (F a) = g (a.2, Q a.1) := by
    simp only [F, absorptionMap, map_add, hQK]
    abel
  have hinput : dist (x.2,Q x.1) (y.2,Q y.1) ≤ (‖Q‖/cg) * dist (F x) (F y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcg).mpr
    calc
      dist (x.2, Q x.1) (y.2, Q y.1) * cg
        = cg * dist (x.2, Q x.1) (y.2, Q y.1) := mul_comm _ _
      _ ≤ dist (g (x.2,Q x.1)) (g (y.2,Q y.1)) := hg _ _
      _ = dist (Q (F x)) (Q (F y)) := by rw [hQF, hQF]
      _ ≤ ‖Q‖ * dist (F x) (F y) := Q.lipschitz.dist_le_mul _ _
  have hf : dist x.1 y.1 ≤ (1+LK*‖Q‖/cg) * dist (F x) (F y) := by
    calc
      dist x.1 y.1 = dist (F x-K (x.2,Q x.1)) (F y-K (y.2,Q y.1)) := by
        simp [F, absorptionMap]
      _ ≤ dist (F x) (F y)+dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_sub_sub_le _ _ _ _
      _ ≤ dist (F x) (F y)+LK*((‖Q‖/cg)*dist (F x) (F y)) :=
        add_le_add_right ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK)) _
      _ = _ := by ring
  have hs : dist x.2 y.2 ≤ (‖Q‖/cg)*dist (F x) (F y) :=
    (show dist x.2 y.2 ≤ dist (x.2,Q x.1) (y.2,Q y.1) by rw [Prod.dist_eq]; exact le_max_left _ _).trans hinput
  rw [Prod.dist_eq]
  exact max_le (hf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg))
    (hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))

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


theorem solution : type_of% @_root_.OAI.C0Absorption.absorption_inverse_bound := @_root_.OAI.C0Absorption.absorption_inverse_bound

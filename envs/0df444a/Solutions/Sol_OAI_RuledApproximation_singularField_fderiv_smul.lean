-- Prove2me | solution 1 for OAI.RuledApproximation.singularField_fderiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:24:25.391244+00:00
-- url     : https://prove2.me/submissions/a2eb3889-e64e-43c7-b092-5e7aee005635

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularField.lean:L60-L74
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularField_fderiv_smul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt
import Theorems.Thm_OAI_RuledApproximation_singularField_smul

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularField_fderiv_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) (r • z) = r^(p-2) • fderiv ℝ (singularField p) z := by
  have he : (fun w : Plane => singularField p (r • w)) =ᶠ[𝓝 z]
      (fun w : Plane => r^(p-1) • singularField p w) := by
    filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous (fun w : Plane => w 1))).mem_nhds hz]
      with w hw
    exact singularField_smul p hr hw
  have hd := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  have he' := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_smul r, fderiv_fun_const_smul hd] at he'
  have hp : r^(p-1) = r*r^(p-2) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
    ring
  rw [hp,mul_smul] at he'
  exact (smul_right_injective (Plane →L[ℝ] Plane) hr.ne') he'

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularField_fderiv_smul := @_root_.OAI.RuledApproximation.singularField_fderiv_smul

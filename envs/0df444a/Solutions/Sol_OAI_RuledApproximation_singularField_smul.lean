-- Prove2me | solution 1 for OAI.RuledApproximation.singularField_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:23:13.244571+00:00
-- url     : https://prove2.me/submissions/344c81d0-afc1-464d-95c2-89f239f2abb8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularField.lean:L45-L58
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularField_smul. The node keeps its source
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

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularField_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    singularField p (r • z) = r^(p-1) • singularField p z := by
  have he : (r*z 1)/(1/2:ℝ) = r*(z 1/(1/2)) := by ring
  have hpow : r^(p-1) = r^(p-2)*r := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
  ext i
  fin_cases i
  · change ((1/2:ℝ)/2)*((r*z 1)/(1/2))^(p-1)*(p+(2-p)*(r*z 0/(r*z 1))^2) =
      r^(p-1)*(((1/2:ℝ)/2)*(z 1/(1/2))^(p-1)*(p+(2-p)*(z 0/z 1)^2))
    rw [he,Real.mul_rpow hr.le (by positivity),mul_div_mul_left _ _ hr.ne']
    ring
  · change ((r*z 1)/(1/2:ℝ))^(p-2)*(r*z 0) = r^(p-1)*((z 1/(1/2))^(p-2)*z 0)
    rw [he,Real.mul_rpow hr.le (by positivity),hpow]
    ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularField_smul := @_root_.OAI.RuledApproximation.singularField_smul

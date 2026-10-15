-- Prove2me | solution 1 for OAI.RuledApproximation.singularField_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:21:45.598445+00:00
-- url     : https://prove2.me/submissions/4e91f5ec-a342-4419-9f1e-6c1b168a3679

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularField.lean:L25-L39
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularField_contDiffAt. The node keeps its source
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

lemma singularField_contDiffAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (singularField p) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun b : Plane => ((1/2:ℝ)/2)*(b 1/(1/2))^(p-1)*
        (p+(2-p)*(b 0/b 1)^2)) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    have hpow := h1.rpow_const_of_ne (p := p-1) (by positivity)
    exact (contDiffAt_const.mul hpow).mul
      (contDiffAt_const.add (contDiffAt_const.mul (((by fun_prop :
        ContDiffAt ℝ ∞ (fun b : Plane => b 0) z).div (by fun_prop) hz.ne').pow 2)))
  · change ContDiffAt ℝ ∞ (fun b : Plane => (b 1/(1/2:ℝ))^(p-2)*b 0) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    exact (h1.rpow_const_of_ne (p := p-2) (by positivity)).mul (by fun_prop)

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularField_contDiffAt := @_root_.OAI.RuledApproximation.singularField_contDiffAt

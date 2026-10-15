-- Prove2me | solution 1 for OAI.RuledApproximation.coneTriangle_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:48:48.188543+00:00
-- url     : https://prove2.me/submissions/763de9d7-7f5f-4537-af06-ad70779b0e54

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/ConeVolume.lean:L29-L49
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.coneTriangle_volume. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Theorems.Thm_OAI_RuledApproximation_coneTriangle_isCompact
import Theorems.Thm_OAI_RuledApproximation_plane_setIntegral_horizontal_interval

-- ---- from OAI.Geometry.RuledCovering.PlanarIntegration ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_volume_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    volume.real S = ∫ r in s, max (u r-l r) 0 := by
  have hi := plane_setIntegral_horizontal_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.ConeVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma coneTriangle_volume {a : ℝ} (ha : 0 ≤ a) : volume.real (coneTriangle a) = a^2 := by
  have heq : ∀ z : Plane, z ∈ coneTriangle a ↔ z 1 ∈ Icc 0 a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneTriangle,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneTriangle_isCompact a).measurableSet
    (coneTriangle_isCompact a).measure_lt_top.ne (s := Icc 0 a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = ∫ r in (0:ℝ)..a, 2*r := by
    rw [intervalIntegral.integral_of_le ha,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = a^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := (0:ℝ)) (b := a) 1
  simp only [pow_one] at hh
  rw [hh]
  norm_num
  ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.coneTriangle_volume := @_root_.OAI.RuledApproximation.coneTriangle_volume

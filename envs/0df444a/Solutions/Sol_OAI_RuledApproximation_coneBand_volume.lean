-- Prove2me | solution 1 for OAI.RuledApproximation.coneBand_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:51:09.646176+00:00
-- url     : https://prove2.me/submissions/23969290-1d20-4ba6-9d6c-6ba7e631c599

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/ConeVolume.lean:L63-L84
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.coneBand_volume. The node keeps its source
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

lemma coneBand_isCompact (d a : ℝ) : IsCompact (coneBand d a) := by
  apply (coneTriangle_isCompact a).of_isClosed_subset
  · unfold coneBand
    exact (isClosed_le (f := fun _ : Plane => d) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  · intro z hz
    exact ⟨(abs_nonneg _).trans hz.2.2,hz.2⟩

lemma coneBand_volume {d a : ℝ} (hd : 0 ≤ d) (hda : d ≤ a) :
    volume.real (coneBand d a) = a^2-d^2 := by
  have heq : ∀ z : Plane, z ∈ coneBand d a ↔ z 1 ∈ Icc d a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneBand,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneBand_isCompact d a).measurableSet
    (coneBand_isCompact d a).measure_lt_top.ne (s := Icc d a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc d a, max (r- -r) 0) = ∫ r in d..a, 2*r := by
    rw [intervalIntegral.integral_of_le hda,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc d a, max (r- -r) 0) = a^2-d^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := d) (b := a) 1
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


theorem solution : type_of% @_root_.OAI.RuledApproximation.coneBand_volume := @_root_.OAI.RuledApproximation.coneBand_volume

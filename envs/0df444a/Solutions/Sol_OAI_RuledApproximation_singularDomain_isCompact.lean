-- Prove2me | solution 1 for OAI.RuledApproximation.singularDomain_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:31:32.793064+00:00
-- url     : https://prove2.me/submissions/903ab1f8-7f70-4d6b-aa74-30005719819a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularBounds.lean:L69-L83
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularDomain_isCompact. The node keeps its source
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

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_norm_sq (z : Plane) : ‖z‖^2 = z 0^2+z 1^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs]

lemma plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0),sq_abs (z 1)]

lemma singularDomain_isCompact (p gamma c : ℝ) : IsCompact (singularDomain p gamma c) := by
  have hb : Continuous (fun z : Plane => z 0) := by fun_prop
  have hr : Continuous (fun z : Plane => z 1) := by fun_prop
  have hcap : Continuous (fun z : Plane => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ)) := by
    unfold ceilingPolynomial
    fun_prop
  have hclosed : IsClosed (singularDomain p gamma c) :=
    (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
      ((isClosed_le hb.abs hr).inter (isClosed_le hr hcap)))
  apply (isCompact_closedBall (0 : Plane) 4).of_isClosed_subset hclosed
  intro z hz
  have hz0 : |z 0| ≤ 2 := hz.2.2.1.trans hz.2.1
  have hz1 : |z 1| ≤ 2 := (abs_of_nonneg ((abs_nonneg _).trans hz.2.2.1)).le.trans hz.2.1
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (plane_norm_le_sum z).trans (by linarith)

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularDomain_isCompact := @_root_.OAI.RuledApproximation.singularDomain_isCompact

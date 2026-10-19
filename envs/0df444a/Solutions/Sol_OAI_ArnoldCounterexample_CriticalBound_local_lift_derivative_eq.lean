-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:08:54.088827+00:00
-- url     : https://prove2.me/submissions/e35f2c5c-e0bf-4612-af46-ba93b949bacb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Deformation.lean:L40-L61
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Theorems.Thm_OAI_ArnoldCounterexample_Quadric_tangentCurve_hasDerivAt_zero

-- ---- from OAI.Geometry.Arnold.Deformation ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric

/-- Every local lift has the same horizontal derivative as a global extension;
this follows from the explicit curves in the actual quadric. -/
lemma local_lift_derivative_eq {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (U : Set CV) (g : CV → ℝ)
    (hg : LocalFunctionLift h z U g) (v : CV) (hv : Horizontal z v) :
    fderiv ℝ g z v = fderiv ℝ G z v := by
  obtain ⟨hU, hzU, hgs, hagree⟩ := hg
  have hc := tangentCurve_hasDerivAt_zero z v hv
  have hd := (hgs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  have hd' : HasFDerivAt g (fderiv ℝ g z) (tangentCurve z v hv 0 : CV) := by
    simpa only [tangentCurve_zero] using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt 0 hc
  have hglobal := (hG.differentiable (by simp) (tangentCurve z v hv 0 : CV)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hmem : ∀ᶠ t in nhds (0 : ℝ), (tangentCurve z v hv t : CV) ∈ U :=
    hc.continuousAt.eventually (by convert! hU.mem_nhds hzU using 1; simp)
  have heq : (fun t ↦ g (tangentCurve z v hv t)) =ᶠ[nhds (0 : ℝ)]
      (fun t ↦ G (tangentCurve z v hv t)) := by
    filter_upwards [hmem] with t ht
    rw [hagree _ ht, hGagree]
  have hsame := hcomp.congr_of_eventuallyEq heq.symm
  simpa only [tangentCurve_zero] using hsame.unique hglobal

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ArnoldCounterexample.Quadric


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq := @_root_.OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq

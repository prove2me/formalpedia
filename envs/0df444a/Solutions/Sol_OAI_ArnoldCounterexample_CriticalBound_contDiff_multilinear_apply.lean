-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:51:47.035304+00:00
-- url     : https://prove2.me/submissions/537bed89-5907-44dc-973e-f34631b21622

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Differentiation.lean:L14-L32
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply. The node keeps its source
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

-- ---- from OAI.Geometry.Arnold.Differentiation ----
namespace OAI

universe uE uF uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound

/-- Smooth evaluation including all moving vector arguments. -/
theorem contDiff_multilinear_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [×n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by
  induction n with
  | zero =>
      convert! (continuousMultilinearCurryFin0 ℝ F G).contDiff.comp hf using 1
      ext x
      exact congrArg (f x) (Subsingleton.elim _ _)
  | succ n ih =>
      have hc : ContDiff ℝ k (fun x ↦ (f x).curryLeft (v 0 x)) := by
        convert! ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ F) G).contDiff.comp hf).clm_apply (hv 0) using 1
      convert! ih hc (fun i ↦ hv i.succ) using 1
      ext x
      exact congrArg (f x) (Fin.cons_self_tail (v · x)).symm

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open VectorField

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator


theorem solution.{uE,uF,uG} : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply.{uE,uF,uG} := @_root_.OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply.{uE,uF,uG}

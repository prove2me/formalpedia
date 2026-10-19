-- Prove2me | solution 2 for OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:26:02.135712+00:00
-- url     : https://prove2.me/submissions/84f7ade4-d00f-491f-b9a2-c011c3d601d1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Volume.lean:L142-L160
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume

-- ---- from OAI.Geometry.Arnold.Volume ----
namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_3
end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

/-- Differentiating honest circle equivariance, rather than assuming its
infinitesimal consequence. -/
lemma fderiv_circle_equivariant {m n : ℕ} (F : CSpace m → CSpace n)
    (hF : Differentiable ℝ F) (z : CSpace m)
    (hphase : ∀ a : ℂ, Complex.normSq a = 1 → F (a • z) = a • F z) :
    fderiv ℝ F z (Complex.I • z) = Complex.I • F z := by
  let a : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * Complex.I)
  have ha : HasDerivAt a Complex.I 0 := by
    simpa [a] using ((Complex.ofRealCLM.hasDerivAt).mul_const Complex.I).cexp (x := (0 : ℝ))
  have ha0 : a 0 = 1 := by simp [a]
  have hau (t : ℝ) : Complex.normSq (a t) = 1 := by
    simp [a, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have heq : (fun t ↦ F (a t • z)) = fun t ↦ a t • F z :=
    funext (fun t ↦ hphase _ (hau t))
  have hd := (hF (a 0 • z)).hasFDerivAt.comp_hasDerivAt 0 (ha.smul_const z)
  rw [ha0, one_smul] at hd
  dsimp only [Function.comp_def] at hd
  rw [heq] at hd
  exact hd.unique (ha.smul_const (F z))

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ContinuousAlternatingMap


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant := @_root_.OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant

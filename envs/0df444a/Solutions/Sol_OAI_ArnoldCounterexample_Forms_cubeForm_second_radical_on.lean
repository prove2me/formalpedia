-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.cubeForm_second_radical_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:31:19.837992+00:00
-- url     : https://prove2.me/submissions/fdde3d57-a62c-42a5-a091-8827d44a39e4

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Volume.lean:L226-L243
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.cubeForm_second_radical_on. The node keeps its source
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
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_cubeForm_radical_on

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

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

lemma cubeForm_second_radical_on {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hskew : ∀ u v, B u v = -B v u)
    (u w : E) (v : Fin 4 → E) (hw : B u w = 0) (hv : ∀ i, B u (v i) = 0) :
    cubeForm B (Matrix.vecCons w (Matrix.vecCons u v)) = 0 := by
  have hz := cubeForm_radical_on B hskew u (Matrix.vecCons w v) (by
    intro i
    refine Fin.cases hw (fun j ↦ hv j) i)
  have heq : (Matrix.vecCons w (Matrix.vecCons u v)) ∘ Equiv.swap (0 : Fin 6) 1 =
      Matrix.vecCons u (Matrix.vecCons w v) := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hs := (cubeForm B).toAlternatingMap.map_swap
    (Matrix.vecCons w (Matrix.vecCons u v)) (show (0 : Fin 6) ≠ 1 by decide)
  rw [heq] at hs
  change cubeForm B (Matrix.vecCons u (Matrix.vecCons w v)) =
    -cubeForm B (Matrix.vecCons w (Matrix.vecCons u v)) at hs
  rw [hz] at hs
  exact neg_eq_zero.mp hs.symm

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


theorem solution.{uE} : type_of% @_root_.OAI.ArnoldCounterexample.Forms.cubeForm_second_radical_on.{uE} := @_root_.OAI.ArnoldCounterexample.Forms.cubeForm_second_radical_on.{uE}

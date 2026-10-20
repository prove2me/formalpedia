-- Prove2me | solution 2 for OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:12:20.81606+00:00
-- url     : https://prove2.me/submissions/d242f117-116e-42a0-897d-6a8d1e194712

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/ThreePoints.lean:L110-L131
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Theorems.Thm_OAI_ArnoldCounterexample_ThreePoints_classify_coordinates

-- ---- from OAI.Geometry.Arnold.ThreePoints ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

lemma qzero_critical : MultiplierCritical qzero := by
  refine ⟨⟨?_, ?_⟩, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qzero, pole, east, Matrix.cons_val_two]

lemma qplus_critical : MultiplierCritical qplus := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨?_, ?_⟩, Real.sqrt 3, Real.sqrt 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qplus, Matrix.cons_val_two] <;> nlinarith only [hs]

lemma qminus_critical : MultiplierCritical qminus := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨?_, ?_⟩, -Real.sqrt 3, -Real.sqrt 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qminus, Matrix.cons_val_two] <;> nlinarith only [hs]

/-- Exhaustiveness includes the isolated degenerate point. -/
theorem multiplierCritical_iff (q : Pair) :
    MultiplierCritical q ↔ q = qzero ∨ q = qplus ∨ q = qminus := by
  constructor
  · rintro ⟨⟨hx, hy⟩, lam, μ, h₀, h₁, h₂, g₀, g₁, g₂⟩
    rcases classify_coordinates hx hy h₀ h₁ h₂ g₀ g₁ g₂ with h | h
    · left
      rcases h with ⟨hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
      apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qzero, pole, east, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂]
    · rcases h with ⟨hμ, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
      have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hm : μ = Real.sqrt 3 ∨ μ = -Real.sqrt 3 :=
        sq_eq_sq_iff_eq_or_eq_neg.mp (hμ.trans hs.symm)
      rcases hm with hm | hm
      · right; left
        apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qplus, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hm]
      · right; right
        apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qminus, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hm]
  · rintro (rfl | rfl | rfl)
    · exact qzero_critical
    · exact qplus_critical
    · exact qminus_critical

open scoped Matrix

end ThreePoints
end ArnoldCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.ThreePoints
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff := @_root_.OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff

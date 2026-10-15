-- Prove2me | solution 1 for OAI.RuledApproximation.IsTriangle.linear_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:58:05.589299+00:00
-- url     : https://prove2.me/submissions/983d6783-7eef-478c-989e-63ba154796d1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/TipCylinders.lean:L12-L26
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.IsTriangle.linear_image. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral
import Definitions.Def_OAI_Geometry_RuledCovering_TipCylinders

-- ---- from OAI.Geometry.RuledCovering.TipCylinders ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsTriangle.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsTriangle P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsTriangle (f '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨f c,f u,f v,?_,?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : f ∘ ![u,v] = ![f u,f v] := by funext i; fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨_,⟨s,t,hs,ht,hst,rfl⟩,rfl⟩
      exact ⟨s,t,hs,ht,hst,by simp⟩
    · rintro ⟨s,t,hs,ht,hst,rfl⟩
      exact ⟨c+s•u+t•v,⟨s,t,hs,ht,hst,rfl⟩,by simp⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.IsTriangle.linear_image := @_root_.OAI.RuledApproximation.IsTriangle.linear_image

-- Prove2me | solution 1 for OAI.Solenoidal.globalDirectForce_classicalSolution
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:03:02.510809+00:00
-- url     : https://prove2.me/submissions/902f6af3-f255-4a1c-8fa7-7e0623a98fa1

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean:L267-L299
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.globalDirectForce_classicalSolution. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential

-- ---- from OAI.MathematicalPhysics.SheetFlows.DirectForce ----
namespace OAI

/-! SheetFlows direct force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem directForce_equation (ν : ℝ) (u : Field)
    (hadv : ∀ t x, advection u t x = 0) (t : ℝ) (x : Space) :
    timePartial u t x + advection u t x =
      -gradient (0 : Pressure) t x + ν • laplacian u t x + directForce ν u t x := by
  simp only [hadv, add_zero, gradient_zero, Pi.zero_apply, neg_zero, zero_add, directForce]
  abel

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

end DirectionalCalculus

theorem fieldDirectional_smooth {u : Field} (hu : Smooth u) (v : SpaceTime) :
    Smooth (fieldDirectional u v) := directional_contDiff hu v

theorem spatialPartial_eq_fieldDirectional {u : Field} (hu : Smooth u) (j : Fin 3) :
    spatialPartial u j = fieldDirectional u (0, basis j) := by
  funext t x
  have h := (hu.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have he : fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) := h.fderiv
  change fderiv ℝ (u t) x (basis j) = _
  rw [he]
  rfl

theorem fullTimePartial_eq_fieldDirectional {u : Field} (hu : Smooth u) :
    fullTimePartial u = fieldDirectional u (1, 0) := by
  funext t x
  exact ((hu.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

theorem smooth_spatialPartial {u : Field} (hu : Smooth u) (j : Fin 3) :
    Smooth (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_smooth hu _

theorem smooth_fullTimePartial {u : Field} (hu : Smooth u) : Smooth (fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hu]
  exact fieldDirectional_smooth hu _

theorem smooth_spatial_slice {u : Field} (hu : Smooth u) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (u t) := hu.comp (contDiff_const.prodMk contDiff_id)

theorem smooth_temporal_slice {u : Field} (hu : Smooth u) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => u t x) := hu.comp (contDiff_id.prodMk contDiff_const)

theorem timePartial_eq_fullTimePartial {u : Field} (hu : Smooth u)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timePartial u t x = fullTimePartial u t x :=
  ((smooth_temporal_slice hu x).differentiable (by simp) t).derivWithin
    (uniqueDiffOn_Ici 0 t ht)

theorem globalDirectForce_eq_directForce {u : Field} (hu : Smooth u)
    (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    globalDirectForce ν u t x = directForce ν u t x := by
  simp only [globalDirectForce, directForce, timePartial_eq_fullTimePartial hu ht x]

theorem globalDirectForce_classicalSolution {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (hdiv : DivergenceFree u)
    (hzero : ∀ x, u 0 x = 0) (hadv : ∀ t x, advection u t x = 0) (ν : ℝ) :
    ClassicalSolution ν (globalDirectForce ν u) u (0 : Pressure) where
  spatial_periodic_u := hp
  spatial_periodic_p := by intro t x k; rfl
  continuous_u := fun _ _ => hu.continuous.continuousOn
  differentiable_t := fun t _ x =>
    ((smooth_temporal_slice hu x).differentiable (by simp) t).differentiableWithinAt
  continuous_t := by
    intro T _
    apply (smooth_fullTimePartial hu).continuous.continuousOn.congr
    intro z hz
    exact timePartial_eq_fullTimePartial hu hz.1.1 z.2
  differentiable_x := fun t _ => (smooth_spatial_slice hu t).differentiable (by simp)
  continuous_x := fun _ _ j => (smooth_spatialPartial hu j).continuous.continuousOn
  differentiable_xx := fun t _ j =>
    (smooth_spatial_slice (smooth_spatialPartial hu j) t).differentiable (by simp)
  continuous_xx := fun _ _ i j =>
    (smooth_spatialPartial (smooth_spatialPartial hu i) j).continuous.continuousOn
  continuous_p := fun _ _ => continuous_const.continuousOn
  differentiable_p := fun _ _ => differentiable_const _
  continuous_px := by
    intro T _
    simp only [gradient_zero]
    exact continuous_const.continuousOn
  pressure_mean_zero := by intro t _; simp
  incompressible := fun t _ x => hdiv t x
  initial := hzero
  equation := by
    intro t ht x
    rw [globalDirectForce_eq_directForce hu ν ht]
    exact directForce_equation ν u hadv t x

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.globalDirectForce_classicalSolution := @_root_.OAI.Solenoidal.globalDirectForce_classicalSolution

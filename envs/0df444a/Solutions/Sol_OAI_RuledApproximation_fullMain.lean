-- Prove2me | solution 1 for OAI.RuledApproximation.fullMain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:03:14.120242+00:00
-- url     : https://prove2.me/submissions/f2aaedfc-24d0-4e8f-a3d4-53e871db7b7f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Main.lean:L13-L15
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.RuledApproximation.fullMain.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_RuledApproximation_fullMain) verbatim and is proved by it.
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
import Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_isometry
import Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_open_enlarge
import Theorems.Thm_OAI_RuledApproximation_globalize_local_covers
import Theorems.Thm_OAI_RuledApproximation_hyperbolic_local_patch
import Theorems.Thm_OAI_RuledApproximation_logarithmic
import Theorems.Thm_OAI_RuledApproximation_nilpotent
import Theorems.Thm_OAI_RuledApproximation_orthogonalGrid
import Theorems.Thm_OAI_RuledApproximation_singular

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_inflation_budget (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 < B ∧ B * C < C + eps := by
  have hc : Continuous (fun d : ℝ => (1+d)*C) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1+d)*C < C + eps :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using lt_add_of_pos_right C heps))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2, by linarith, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- General physical weighted hyperbolic approximation, before isometry transport. -/
theorem physical_hyperbolic_cover {h L : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hhyp : ∀ p ∈ D, HyperbolicAt L v p) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover Cylinder.parallelogram (physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h L v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => hyperbolic_local_patch hh hL hB hU hv (hDU hp) (hhyp p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.Hyperbolic ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Scaled-plane approximation under every Euclidean isometry. -/
theorem physicalHyperbolic : PhysicalHyperbolicStatement := by
  intro h L D v hh hL hD hv hH e he F
  exact (physical_hyperbolic_cover hh hL hD hv hH he).isometry F

lemma norm_plane_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma physicalWeight_one (g : Plane) : physicalWeight 1 g = weight g := by
  simp only [physicalWeight, weight, norm_plane_sq, one_pow, one_mul]
  congr 2
  ring

lemma cycle_physicalRuled (D : Set Plane) (v : Plane → Plane) (L : ℝ) :
    cycleCoordinates '' physicalRuled 1 D v L = ruled D v L := by
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    exact ⟨p, hp, r, hr, by simp [cycleCoordinates]⟩
  · rintro ⟨p, hp, r, hr, rfl⟩
    refine ⟨vec3 r (p 0+r*v p 0) (p 1+r*v p 1),
      ⟨p, hp, r, hr, by simp⟩, ?_⟩
    rfl

/-- General hyperbolic approximation: arbitrary compact labels, including
positive-area frontiers and area-zero sets. -/
theorem hyperbolic : HyperbolicStatement := by
  intro D v L hD hv hL hH e he
  have hc := physicalHyperbolic 1 L D v (by norm_num) hL hD hv hH e he
    cycleCoordinates.toIsometryEquiv
  simpa only [LinearIsometryEquiv.coe_toIsometryEquiv, cycle_physicalRuled,
    physicalWeight_one, one_mul] using hc

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SpecializedCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The product-cell endpoint follows from the stronger arbitrary-compact producer
and exact open-base enlargement. -/
theorem productCell : ProductCellStatement := by
  intro h M D v hh hM hD _ hv hH e he
  have hc := physical_hyperbolic_cover hh hM hD hv hH (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.Main ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

theorem fullMain : FullMain :=
  ⟨hyperbolic, physicalHyperbolic, logarithmic, productCell,
    orthogonalGrid, nilpotent, singular⟩

end RuledApproximation

end

end OAI

-- ---- mission target ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Filter Metric

theorem solution : FullMain := by
  first
    | exact OAI.RuledApproximation.fullMain
    | (apply OAI.RuledApproximation.fullMain <;> assumption)
    | (intros; apply OAI.RuledApproximation.fullMain <;> assumption)

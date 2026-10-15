-- Prove2me | solution 1 for OAI.RuledApproximation.orthogonalGrid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:02:40.549982+00:00
-- url     : https://prove2.me/submissions/bcc4b240-902d-4a6d-8d7c-6e869aa9b249

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SpecializedCover.lean:L105-L119
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.orthogonalGrid. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_globalize_local_covers
import Theorems.Thm_OAI_RuledApproximation_hyperbolic_local_patch

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

-- ---- from OAI.Geometry.RuledCovering.SpecializedCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_charpoly (A : Plane →ₗ[ℝ] Plane) :
    A.charpoly = Polynomial.X ^ 2 -
      Polynomial.C (LinearMap.trace ℝ Plane A) * Polynomial.X + Polynomial.C (LinearMap.det A) := by
  rw [← LinearMap.charpoly_toMatrix A (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.charpoly_fin_two, LinearMap.det_toMatrix,
    ← LinearMap.trace_eq_matrix_trace]

lemma plane_hyperbolic_eigenvalues (A : Plane →ₗ[ℝ] Plane)
    (ht : LinearMap.trace ℝ Plane A = 0) (hd : LinearMap.det A < 0) :
    Module.End.HasEigenvalue A (Real.sqrt (-LinearMap.det A)) ∧
    Module.End.HasEigenvalue A (-Real.sqrt (-LinearMap.det A)) := by
  have hs : Real.sqrt (-LinearMap.det A) ^ 2 = -LinearMap.det A :=
    Real.sq_sqrt (by linarith)
  constructor <;> rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, ht] <;> simp [hs]

lemma eigenvalue_le_norm (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Module.End.HasEigenvalue A.toLinearMap lam) : lam ≤ ‖A‖ := by
  obtain ⟨u, hu⟩ := h.exists_hasEigenvector
  have hue : A u = lam • u := hu.apply_eq_smul
  have hn := A.le_opNorm u
  rw [hue, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hn
  exact le_of_mul_le_mul_right hn (norm_pos_iff.mpr hu.2)

/-- The orthogonal-grid endpoint needs no new cover construction: its norm bound
implies precisely the two-eigenvalue condition of the general theorem. -/
theorem orthogonalGrid : OrthogonalGridStatement := by
  intro D v kappa hD _ hv hk hH e he
  have hhyp : ∀ p ∈ D, HyperbolicAt 1 v p := by
    intro p hp
    obtain ⟨ht,hd,hn⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    refine ⟨_, by simpa using hlam, ?_, hplus, hminus⟩
    simpa only [one_mul] using ((eigenvalue_le_norm _ hlam.le hplus).trans hn).trans_lt hk
  have hc := physical_hyperbolic_cover (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    (by norm_num : (0:ℝ)<1) hD hv hhyp he
  simpa only [physicalWeight, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using hc

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.orthogonalGrid := @_root_.OAI.RuledApproximation.orthogonalGrid

-- Prove2me | solution 1 for OAI.RuledApproximation.logarithmic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:07:39.930975+00:00
-- url     : https://prove2.me/submissions/19665203-0540-4dba-88f1-fa5fa5b65b1c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SpecializedCover.lean:L130-L164
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.logarithmic. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_open_enlarge
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

-- ---- from OAI.Geometry.RuledCovering.Hyperbolic ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma norm_plane_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma physicalWeight_one (g : Plane) : physicalWeight 1 g = weight g := by
  simp only [physicalWeight, weight, norm_plane_sq, one_pow, one_mul]
  congr 2
  ring

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

lemma eigenvalue_smul (A : Plane →ₗ[ℝ] Plane) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue A lam) (k : ℝ) :
    Module.End.HasEigenvalue (k • A) (k * lam) := by
  obtain ⟨u, hu⟩ := hlam.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change k • A u = (k*lam) • u
    rw [hu.apply_eq_smul, mul_smul]
  · exact hu.2

lemma OpenRectangleC2.smoothNear {D : Set Plane} {v : Plane → Plane}
    (hv : OpenRectangleC2 D v) : SmoothNear 1 D v := by
  obtain ⟨a,b,_,hD,hv⟩ := hv
  refine ⟨{p | ∀ i, p i ∈ Ioo (a i) (b i)}, ?_,hD,hv.of_le (by norm_num)⟩
  have he : {p : Plane | ∀ i, p i ∈ Ioo (a i) (b i)} =
      ⋂ i : Fin 2, (fun p : Plane => p i) ⁻¹' Ioo (a i) (b i) := by ext p; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (by fun_prop))

/-- The logarithmic-cell endpoint follows with its exact velocity scaling and
orthonormal-coordinate weight, while its boundary hypothesis remains local. -/
theorem logarithmic : LogarithmicStatement := by
  intro X k D v hX hk hD _ hv hH e he
  obtain ⟨U,hU,hDU,hv1⟩ := hv.smoothNear
  have hw : SmoothNear 1 D (fun p => k • v p) :=
    ⟨U,hU,hDU,hv1.const_smul k⟩
  have hhyp : ∀ p ∈ D, HyperbolicAt X (fun p => k • v p) p := by
    intro p hp
    obtain ⟨ht,hd,hsmall⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    have hder := ((hv1.contDiffAt (hU.mem_nhds (hDU hp))).differentiableAt
      (by norm_num)).hasFDerivAt.const_smul k
    have hf : fderiv ℝ (fun p => k • v p) p = k • fderiv ℝ v p := hder.fderiv
    refine ⟨k*Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap), by positivity,
      by nlinarith, ?_, ?_⟩
    · rw [hf]
      exact eigenvalue_smul _ hplus k
    · rw [hf]
      change Module.End.HasEigenvalue (k • (fderiv ℝ v p).toLinearMap) (- (k * _))
      rw [← mul_neg]
      exact eigenvalue_smul _ hminus k
  have hc := physical_hyperbolic_cover (by norm_num : (0:ℝ)<1) hX hD hw hhyp (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  rw [one_mul]
  have hint : (∫ p in D, physicalWeight 1 (k • v p)) =
      ∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [physicalWeight_one, weight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hint]
  ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.logarithmic := @_root_.OAI.RuledApproximation.logarithmic

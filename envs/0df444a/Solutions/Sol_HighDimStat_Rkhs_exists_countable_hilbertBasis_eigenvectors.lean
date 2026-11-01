-- Prove2me | solution 1 for HighDimStat.Rkhs.exists_countable_hilbertBasis_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T11:06:42.613751+00:00
-- url     : https://prove2.me/submissions/34221a4b-a1b5-4aa0-a067-c83dec6e87ec

import Mathlib

open scoped InnerProductSpace
open Module.End

namespace HighDimStat.Rkhs

theorem orthonormal_countable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) :
    Countable ι := by
  have hdist (i j : ι) (hij : i ≠ j) : 1 < dist (v i) (v j) := by
    have h_sq : dist (v i) (v j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, hv.2 hij, mul_zero, sub_zero, hv.1 i, hv.1 j]
      norm_num
    have hpos : 0 ≤ dist (v i) (v j) := dist_nonneg
    have h_gt : (1 : ℝ) < dist (v i) (v j) ^ 2 := by rw [h_sq]; norm_num
    nlinarith
  have hdisj : Pairwise fun i j ↦ Disjoint (Metric.ball (v i) (1 / 2)) (Metric.ball (v j) (1 / 2)) := by
    intro i j hij
    rw [Set.disjoint_iff]
    rintro x ⟨hxi, hxj⟩
    simp only [Metric.mem_ball] at hxi hxj
    rw [dist_comm] at hxi
    have := (dist_triangle (v i) x (v j)).trans_lt (add_lt_add hxi hxj)
    rw [add_halves] at this
    have := hdist i j hij
    linarith
  exact Pairwise.countable_of_isOpen_disjoint hdisj
    (fun i ↦ Metric.isOpen_ball)
    (fun i ↦ Metric.nonempty_ball.mpr (by norm_num))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def get_basis (T : E →L[ℝ] E) (μ : ℝ) :
    Σ (w : Set (Module.End.eigenspace (T : Module.End ℝ E) μ)),
      HilbertBasis w ℝ (Module.End.eigenspace (T : Module.End ℝ E) μ) := by
  haveI : CompleteSpace (Module.End.eigenspace (T : Module.End ℝ E) μ) :=
    IsClosed.completeSpace_coe (hs := ContinuousLinearMap.isClosed_eigenspace T μ)
  have h := exists_hilbertBasis ℝ (Module.End.eigenspace (T : Module.End ℝ E) μ)
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

noncomputable def v' (T : E →L[ℝ] E) (p : Σ (μ : ℝ), (get_basis T μ).1) : E :=
  ((get_basis T p.1).2 p.2 : E)

lemma v'_orthonormal (T : E →L[ℝ] E) (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) :
    Orthonormal ℝ (v' T) :=
  OrthogonalFamily.orthonormal_sigma_orthonormal
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces hsym)
    (fun μ => (get_basis T μ).2.orthonormal)

lemma v'_eigenvector (T : E →L[ℝ] E) (p : Σ (μ : ℝ), (get_basis T μ).1) :
    T (v' T p) = p.1 • v' T p :=
  Module.End.mem_eigenspace_iff.mp ((get_basis T p.1).2 p.2).2

lemma orthogonal_eigenspace (T : E →L[ℝ] E) (x : E)
    (hx : x ∈ (Submodule.span ℝ (Set.range (v' T)))ᗮ) (μ : ℝ) :
    x ∈ (Module.End.eigenspace (T : Module.End ℝ E) μ)ᗮ := by
  let W := Module.End.eigenspace (T : Module.End ℝ E) μ
  rw [Submodule.mem_orthogonal']
  intro y hy
  let y_W : W := ⟨y, hy⟩
  let b := (get_basis T μ).2
  have hsum := ((b.hasSum_repr y_W).mapL W.subtypeL).mapL (innerSL ℝ x)
  have hzero (i : (get_basis T μ).1) : ⟪x, W.subtype (b i)⟫_ℝ = 0 := by
    have h_mem : W.subtype (b i) ∈ Submodule.span ℝ (Set.range (v' T)) :=
      Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal h_mem hx
  have hzero' (i : (get_basis T μ).1) :
      (innerSL ℝ x) (W.subtypeL (b.repr y_W i • b i)) = 0 := by
    rw [map_smul, Submodule.coe_subtypeL, innerSL_apply_apply, inner_smul_right, hzero, mul_zero]
  simp only [hzero'] at hsum
  have h_inner : ⟪x, y⟫_ℝ = 0 := hsum.unique hasSum_zero
  exact h_inner

lemma orthogonalComplement_span_range_v'_eq_bot (T : E →L[ℝ] E)
    (hT : IsCompactOperator T) (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) :
    (Submodule.span ℝ (Set.range (v' T)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h_orth (μ : ℝ) : x ∈ (Module.End.eigenspace (T : Module.End ℝ E) μ)ᗮ :=
    orthogonal_eigenspace T x hx μ
  have h_iInf : x ∈ ⨅ μ, (Module.End.eigenspace (T : Module.End ℝ E) μ)ᗮ := by
    rw [Submodule.mem_iInf]
    exact h_orth
  rw [Submodule.iInf_orthogonal] at h_iInf
  have h_bot : (⨆ μ, Module.End.eigenspace (T : Module.End ℝ E) μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym
  rw [h_bot, Submodule.mem_bot] at h_iInf
  exact h_iInf

/-- Spectral theorem for compact self-adjoint operators on a separable real Hilbert space:
there is a countable Hilbert basis consisting of eigenvectors. -/
theorem exists_countable_hilbertBasis_eigenvectors
    [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E) (hT : IsCompactOperator T) (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      ∀ j, T (b j) = μ j • b j := by
  let ι' := Σ (μ : ℝ), (get_basis T μ).1
  have hv' : Orthonormal ℝ (v' T) := v'_orthonormal T hsym
  have hι' : Countable ι' := orthonormal_countable hv'
  have h_enc : Nonempty (Encodable ι') := Encodable.nonempty_encodable.mpr hι'
  let _ : Encodable ι' := h_enc.some
  let ι : Type := Set.range (Encodable.encode (α := ι'))
  have hι : Countable ι := inferInstance
  let e : ι ≃ ι' := (Encodable.equivRangeEncode ι').symm
  let v : ι → E := v' T ∘ e
  have hv : Orthonormal ℝ v := hv'.comp e e.injective
  have h_range : Set.range v = Set.range (v' T) := e.surjective.range_comp (v' T)
  have h_bot : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [h_range]
    exact orthogonalComplement_span_range_v'_eq_bot T hT hsym
  let b : HilbertBasis ι ℝ E := HilbertBasis.mkOfOrthogonalEqBot hv h_bot
  have hb_coe : (b : ι → E) = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv h_bot
  let μ : ι → ℝ := fun j ↦ (e j).1
  refine ⟨ι, hι, b, μ, fun j ↦ ?_⟩
  have hj : b j = v' T (e j) := by
    rw [← Function.comp_apply (f := v' T) (g := e) (x := j)]
    exact congr_fun hb_coe j
  rw [hj]
  exact v'_eigenvector T (e j)

end HighDimStat.Rkhs

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E) (hT : IsCompactOperator T) (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      ∀ j, T (b j) = μ j • b j :=
  HighDimStat.Rkhs.exists_countable_hilbertBasis_eigenvectors T hT hsym


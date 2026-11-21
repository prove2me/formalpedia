-- Prove2me | solution 1 for MasulloGRH.isCompactOperator_iff_approxNumber_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:21:31.991949+00:00
-- url     : https://prove2.me/submissions/11b3001f-e80d-4fe6-990f-d98b128437eb

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open Filter Metric Set
open scoped InnerProductSpace Topology

namespace MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private lemma approximationErrors_nonempty_of_pos {n : ℕ} (hn : 0 < n) (A : E →L[𝕜] F) :
    (approximationErrors n A).Nonempty := by
  refine ⟨‖A - 0‖, 0, ?_, rfl⟩
  change FiniteDimensional 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F)) ∧
    Module.finrank 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F)) < n
  rw [LinearMap.range_zero, finrank_bot]
  exact ⟨inferInstance, hn⟩

private lemma projection_image_compact_approximation (A : E →L[𝕜] F) (hA : IsCompactOperator A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Submodule 𝕜 F, ∃ _ : FiniteDimensional 𝕜 V,
      ‖A - V.starProjection.comp A‖ < ε := by
  obtain ⟨K, hK, hImage⟩ := hA.image_closedBall_subset_compact (1 : ℝ)
  obtain ⟨s, hsf, hCover⟩ :=
    (Metric.totallyBounded_iff.mp hK.totallyBounded) (ε / 2) (by positivity)
  let V := Submodule.span 𝕜 s
  let hV : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 hsf
  refine ⟨V, hV, ?_⟩
  have hNorm : ‖A - V.starProjection.comp A‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity : 0 ≤ ε / 2)
    intro x hx
    have hx' : x ∈ closedBall (0 : E) 1 := by simp [Metric.mem_closedBall, dist_zero_right, hx]
    have hy := hCover (hImage ⟨x, hx', rfl⟩)
    obtain ⟨y, hyS, hyball⟩ := by simpa only [mem_iUnion] using hy
    have hyV : y ∈ V := Submodule.subset_span hyS
    have hs : V.starProjection y = y := V.starProjection_eq_self_iff.mpr hyV
    have hDiff : (A - V.starProjection.comp A) x = Vᗮ.starProjection (A x - y) := by
      rw [V.starProjection_orthogonal]
      simp [map_sub, hs]
    rw [hDiff]
    have hd : dist (A x) y < ε / 2 := hyball
    rw [dist_eq_norm] at hd
    exact (Vᗮ.norm_starProjection_apply_le _).trans hd.le
  exact hNorm.trans_lt (by linarith)

private lemma exists_finite_rank_error_lt (A : E →L[𝕜] F) (hA : IsCompactOperator A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F, FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) ∧
      ‖A - R‖ < ε := by
  obtain ⟨V, hV, hErr⟩ := projection_image_compact_approximation A hA hε
  let R := V.starProjection.comp A
  have hR : LinearMap.range (R : E →ₗ[𝕜] F) ≤ V := by
    rintro y ⟨x, rfl⟩
    exact (V.orthogonalProjectionOnto (A x)).property
  exact ⟨R, Submodule.finiteDimensional_of_le hR, hErr⟩

private lemma finite_rank_isCompactOperator (R : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F))] : IsCompactOperator R := by
  let V := LinearMap.range (R : E →ₗ[𝕜] F)
  let S : E →L[𝕜] V := R.codRestrict V fun x ↦ LinearMap.mem_range_self _ x
  have hS : IsCompactOperator S := isCompactOperator_of_locallyCompactSpace_dom S
  exact hS.clm_comp V.subtypeL

/-- The approximation-number formulation of compactness behind C.3.6.1.
It is enough to assume a Hilbert structure and completeness on the codomain. -/
theorem isCompactOperator_iff_approxNumber_tendsto_zero [CompleteSpace F]
    (A : E →L[𝕜] F) :
    IsCompactOperator A ↔ Tendsto (fun n : ℕ ↦ approxNumber n A) atTop (𝓝 0) := by
  constructor
  · intro hA
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨R, hRf, hR⟩ := exists_finite_rank_error_lt A hA hε
    let r := Module.finrank 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F))
    refine ⟨r + 1, fun n hn ↦ ?_⟩
    have hN : 0 < n := by omega
    have hZero : ∀ a ∈ approximationErrors n A, 0 ≤ a := by
      rintro a ⟨T, _, rfl⟩
      exact norm_nonneg _
    have hBdd : BddBelow (approximationErrors n A) := ⟨0, hZero⟩
    have hLower : 0 ≤ approxNumber n A := by
      apply le_csInf (approximationErrors_nonempty_of_pos hN A)
      exact hZero
    have hUpper : approxNumber n A ≤ ‖A - R‖ :=
      csInf_le hBdd ⟨R, ⟨hRf, by change r < n; omega⟩, rfl⟩
    simpa [Real.dist_eq, abs_of_nonneg hLower] using hUpper.trans_lt hR
  · intro hT
    let C : Set (E →L[𝕜] F) := {T | IsCompactOperator T}
    have hC : IsClosed C := isClosed_setOfPred_isCompactOperator
    have hA : A ∈ closure C := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hT ε hε
      have hApprox : approxNumber (N + 1) A < ε := by
        have hh := hN (N + 1) (by omega)
        rw [Real.dist_eq, sub_zero] at hh
        exact (le_abs_self _).trans_lt hh
      obtain ⟨_, ⟨R, hR, rfl⟩, hErr⟩ :=
        exists_lt_of_csInf_lt (approximationErrors_nonempty_of_pos (by omega) A) hApprox
      let _ : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) := hR.1
      exact ⟨R, finite_rank_isCompactOperator R, by simpa only [dist_eq_norm, norm_sub_rev] using hErr⟩
    rwa [hC.closure_eq] at hA

end MasulloGRH

open MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem solution [CompleteSpace F]
    (A : E →L[𝕜] F) :
    IsCompactOperator A ↔ Tendsto (fun n : ℕ ↦ approxNumber n A) atTop (𝓝 0) :=
  isCompactOperator_iff_approxNumber_tendsto_zero A

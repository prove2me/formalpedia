-- Prove2me | solution 1 for MasulloGRH.approxNumber_eq_inf_orthogonalComplement
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:04:34.22919+00:00
-- url     : https://prove2.me/submissions/c5cfa599-a599-43f8-9c6f-60e10d322d95

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open Set
open scoped InnerProductSpace

namespace MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private lemma approxNumber_le_of_rankBelow {m : ℕ} (A R : E →L[𝕜] F)
    (hR : ApproximationRankBelow m R) : approxNumber m A ≤ ‖A - R‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨S, _, rfl⟩
    exact norm_nonneg _
  · exact ⟨R, hR, rfl⟩

private lemma projection_composition_rankBelow {m : ℕ} (A : E →L[𝕜] F)
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] (hm : Module.finrank 𝕜 K < m) :
    ApproximationRankBelow m (A.comp K.starProjection) := by
  let L := A.comp K.subtypeL
  let P := K.orthogonalProjectionOnto
  have hEq : A.comp K.starProjection = L.comp P := by
    ext x
    rfl
  have hL : Module.finrank 𝕜 (LinearMap.range (L : K →ₗ[𝕜] F)) < m :=
    (LinearMap.finrank_range_le (L : K →ₗ[𝕜] F)).trans_lt hm
  have hle : LinearMap.range ((L.comp P : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤
      LinearMap.range (L : K →ₗ[𝕜] F) :=
    LinearMap.range_comp_le_range (P : E →ₗ[𝕜] K) (L : K →ₗ[𝕜] F)
  rw [hEq]
  exact ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans_lt hL⟩

private lemma norm_sub_composition_projection_le (A : E →L[𝕜] F)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    ‖A - A.comp K.starProjection‖ ≤ ‖A.comp Kᗮ.subtypeL‖ := by
  have hEq : A - A.comp K.starProjection = (A.comp Kᗮ.subtypeL).comp Kᗮ.orthogonalProjectionOnto := by
    have hSt : (A.comp Kᗮ.subtypeL).comp Kᗮ.orthogonalProjectionOnto = A.comp Kᗮ.starProjection := by
      ext x
      rfl
    rw [hSt, Submodule.starProjection_orthogonal]
    ext x
    simp
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left Kᗮ.orthogonalProjectionOnto_norm_le (norm_nonneg _)).trans_eq (mul_one _))

variable [CompleteSpace E]

private noncomputable def orthogonalKerEquivRange (R : E →L[𝕜] F) :
    (R.kerᗮ : Submodule 𝕜 E) ≃ₗ[𝕜] LinearMap.range (R : E →ₗ[𝕜] F) := by
  let _ : CompleteSpace (R.ker : Submodule 𝕜 E) := R.isClosed_ker.completeSpace_coe
  exact (R.ker.quotientEquivOfIsCompl R.kerᗮ R.ker.isCompl_orthogonal).symm.trans
    (R : E →ₗ[𝕜] F).quotKerEquivRange

omit [CompleteSpace E] in
private lemma norm_restriction_ker_le (A R : E →L[𝕜] F) :
    ‖A.comp R.ker.subtypeL‖ ≤ ‖A - R‖ := by
  have heq : A.comp R.ker.subtypeL = (A - R).comp R.ker.subtypeL := by
    ext x
    have hx : R x = 0 := x.property
    simp [hx]
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg _)).trans_eq (mul_one _))

/-- The min side of (C.3.5.4), with finite-rank infima as in (C.3.6.2).
The formula holds for bounded Hilbert-space operators even without compactness,
when the minimum is interpreted as an infimum. -/
theorem approxNumber_eq_inf_orthogonalComplement {m : ℕ} (hm : 0 < m)
    (A : E →L[𝕜] F) :
    approxNumber m A =
      sInf {r : ℝ | ∃ K : Submodule 𝕜 E, FiniteDimensional 𝕜 K ∧
        Module.finrank 𝕜 K < m ∧ r = ‖A.comp Kᗮ.subtypeL‖} := by
  let S : Set ℝ := {r | ∃ K : Submodule 𝕜 E, FiniteDimensional 𝕜 K ∧
      Module.finrank 𝕜 K < m ∧ r = ‖A.comp Kᗮ.subtypeL‖}
  change approxNumber m A = sInf S
  have hS : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨K, _, _, rfl⟩
    exact norm_nonneg _
  apply le_antisymm
  · apply le_csInf
    · refine ⟨_, ⊥, inferInstance, ?_, rfl⟩
      simpa only [finrank_bot] using hm
    · rintro r ⟨K, hK, hmK, rfl⟩
      let _ : FiniteDimensional 𝕜 K := hK
      exact (approxNumber_le_of_rankBelow A _ (projection_composition_rankBelow A K hmK)).trans
        (norm_sub_composition_projection_le A K)
  · unfold approxNumber
    apply le_csInf
    · refine ⟨‖A - 0‖, 0, ?_, rfl⟩
      change FiniteDimensional 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F)) ∧
        Module.finrank 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F)) < m
      rw [LinearMap.range_zero, finrank_bot]
      exact ⟨inferInstance, hm⟩
    · rintro r ⟨R, hR, rfl⟩
      let _ : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) := hR.1
      let _ : CompleteSpace (R.ker : Submodule 𝕜 E) := R.isClosed_ker.completeSpace_coe
      let Eqv := orthogonalKerEquivRange R
      have hfin : FiniteDimensional 𝕜 R.kerᗮ := FiniteDimensional.of_injective Eqv.toLinearMap Eqv.injective
      have hrank : Module.finrank 𝕜 R.kerᗮ < m := Eqv.finrank_eq.trans_lt hR.2
      have heq : R.kerᗮᗮ = R.ker := R.ker.orthogonal_orthogonal
      have hmem : ‖A.comp R.ker.subtypeL‖ ∈ S := by
        refine ⟨R.kerᗮ, hfin, hrank, ?_⟩
        rw [heq]
      exact (csInf_le hS hmem).trans (norm_restriction_ker_le A R)

end MasulloGRH

open MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [CompleteSpace E]

theorem solution {m : ℕ} (hm : 0 < m)
    (A : E →L[𝕜] F) :
    approxNumber m A =
      sInf {r : ℝ | ∃ K : Submodule 𝕜 E, FiniteDimensional 𝕜 K ∧
        Module.finrank 𝕜 K < m ∧ r = ‖A.comp Kᗮ.subtypeL‖} :=
  approxNumber_eq_inf_orthogonalComplement hm A

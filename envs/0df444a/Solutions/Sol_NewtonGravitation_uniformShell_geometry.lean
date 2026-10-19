-- Prove2me | solution 1 for NewtonGravitation.uniformShell_geometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:09:51.173526+00:00
-- url     : https://prove2.me/submissions/f1f64385-15dc-48ef-a531-3b4f54414916

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation Metric
open scoped Pointwise

namespace NGAux

/-- restriction of a linear isometry to the unit sphere -/
noncomputable def sph (A : Space ≃ₗᵢ[ℝ] Space) (u : sphere (0 : Space) 1) : sphere (0 : Space) 1 :=
  ⟨A u, by simp⟩

lemma sph_measurable (A : Space ≃ₗᵢ[ℝ] Space) : Measurable (sph A) :=
  (A.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

lemma toSphere_map_sph (A : Space ≃ₗᵢ[ℝ] Space) :
    (volume : Measure Space).toSphere.map (sph A) = (volume : Measure Space).toSphere := by
  ext s hs
  rw [Measure.map_apply (sph_measurable A) hs,
    Measure.toSphere_apply' _ (sph_measurable A hs), Measure.toSphere_apply' _ hs]
  congr 1
  have h1 : ((↑) '' (sph A ⁻¹' s) : Set Space) = A ⁻¹' ((↑) '' s) := by
    ext x; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨sph A u, hu, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · have : ‖A x‖ = 1 := by rw [← hvx]; simpa using v.2
        simpa using this
      · have : (sph A ⟨x, by have : ‖A x‖ = 1 := (by rw [← hvx]; simpa using v.2); simpa using this⟩) = v :=
          Subtype.ext hvx.symm
        show sph A _ ∈ s
        convert hv
  have h2 : Set.Ioo (0:ℝ) 1 • (A ⁻¹' ((↑) '' s : Set Space)) = A ⁻¹' (Set.Ioo (0:ℝ) 1 • ((↑) '' s)) := by
    ext x; constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      exact ⟨c, hc, A y, hy, by simp⟩
    · rintro ⟨c, hc, y, hy, hxy⟩
      refine ⟨c, hc, A.symm y, by simpa using hy, ?_⟩
      apply A.injective; simp [← hxy]
  rw [h1, h2]
  have hA : MeasurePreserving (A.toHomeomorph.toMeasurableEquiv) volume volume :=
    A.measurePreserving
  exact hA.measure_preimage_equiv _

lemma shell_phi_meas (a : ℝ) :
    Measurable (fun u : sphere (0 : Space) 1 => a • (u : Space)) :=
  (continuous_subtype_val.const_smul a).measurable

lemma toSphere_univ_ne_zero : (volume : Measure Space).toSphere Set.univ ≠ 0 := by
  rw [Ne, Measure.measure_univ_eq_zero]; exact Measure.toSphere_ne_zero _

lemma shell_const_ne_top (M : NNReal) :
    ((M : ENNReal) / (volume : Measure Space).toSphere Set.univ) ≠ ⊤ :=
  ENNReal.div_ne_top ENNReal.coe_ne_top toSphere_univ_ne_zero

lemma uniformShell_isFinite (M : NNReal) (a : ℝ) : IsFiniteMeasure (uniformShell M a) := by
  constructor
  rw [uniformShell, Measure.smul_apply, Measure.map_apply (shell_phi_meas a) MeasurableSet.univ,
    smul_eq_mul]
  exact ENNReal.mul_lt_top (shell_const_ne_top M).lt_top (measure_lt_top _ _)

lemma uniformShell_symm (M : NNReal) (a : ℝ) : IsSphericallySymmetric (uniformShell M a) := by
  intro A
  rw [uniformShell, Measure.map_smul, Measure.map_map A.continuous.measurable (shell_phi_meas a)]
  have : (A ∘ fun u : sphere (0 : Space) 1 => a • (u : Space)) =
      (fun u : sphere (0 : Space) 1 => a • (u : Space)) ∘ sph A := by
    funext u; simp [sph]
  rw [this, ← Measure.map_map (shell_phi_meas a) (sph_measurable A), toSphere_map_sph]

lemma uniformShell_ball (M : NNReal) (a : ℝ) (ha : 0 < a) :
    (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := by
  rw [uniformShell, Measure.smul_apply, Measure.map_apply (shell_phi_meas a) measurableSet_ball]
  have : (fun u : sphere (0 : Space) 1 => a • (u : Space)) ⁻¹' Metric.ball 0 a = ∅ := by
    ext u; simp [norm_smul, abs_of_pos ha]
  simp [this]

end NGAux

open NGAux in
theorem solution (M : NNReal) (a : ℝ) (ha : 0 < a) :
    IsFiniteMeasure (uniformShell M a) ∧
      IsSphericallySymmetric (uniformShell M a) ∧
      (uniformShell M a) (Metric.ball (0 : Space) a) = 0 :=
  ⟨uniformShell_isFinite M a, uniformShell_symm M a, uniformShell_ball M a ha⟩

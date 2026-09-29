-- Prove2me | solution 1 for MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/17d35452-14f4-5fad-84f8-09b3513bb9cb

import Mathlib
import Theorems.Thm_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq

open MeasureTheory

theorem solution
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n₁ n₂ : ℕ} (e : Fin n₁ → V) (f : Fin n₂ → V)
    (he : LinearIndependent ℝ e) (hf : LinearIndependent ℝ f)
    (hspan : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range f)) :
    ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e i) (e j)).det|)) •
        Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e i) volume)
      ((fun a : Fin n₂ → ℝ => ∑ i, a i • f i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) =
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (f i) (f j)).det|) := by
  classical

  have hspan' : (Submodule.span ℝ (Set.range f)).map ((LinearEquiv.refl ℝ V : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) =
      Submodule.span ℝ (Set.range e) := by
    rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]; exact hspan.symm
  have hind := MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq B
    (LinearEquiv.refl ℝ V) (fun _ _ => rfl) e f he hf hspan' (fun _ => 1) measurable_const (fun _ => rfl)
  have h1 : ∀ μ : Measure V, μ.withDensity (fun _ => (1 : ENNReal)) = μ := fun μ => withDensity_one
  have hid : ((LinearEquiv.refl ℝ V : V ≃ₗ[ℝ] V) : V → V) = id := funext fun x => rfl
  rw [h1, h1, hid, Measure.map_id] at hind

  rw [← hind, Measure.smul_apply, smul_eq_mul]

  set T : (Fin n₂ → ℝ) → V := fun a => ∑ i, a i • f i with hT
  have hTlin : T = (Fintype.linearCombination ℝ f : (Fin n₂ → ℝ) → V) := by
    funext a; rw [hT, Fintype.linearCombination_apply]
  have hTemb : MeasurableEmbedding T := by
    rw [hTlin]
    have hker : LinearMap.ker (Fintype.linearCombination ℝ f) = ⊥ :=
      LinearMap.ker_eq_bot.2 (LinearIndependent.fintypeLinearCombination_injective hf)
    exact (LinearMap.isClosedEmbedding_of_injective hker).measurableEmbedding
  rw [hTemb.map_apply, Set.preimage_image_eq _ hTemb.injective, Real.volume_pi_Ico]
  simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]

end S_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
end P2MW
export P2MW.S_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq (solution)

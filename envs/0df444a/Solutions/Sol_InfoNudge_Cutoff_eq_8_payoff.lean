-- Prove2me | solution 1 for InfoNudge.Cutoff.eq_8_payoff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:05:00.940829+00:00
-- url     : https://prove2.me/submissions/e7e6eab7-aeb2-47cf-8a1f-44a27fdb50b7

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

open MeasureTheory

open InfoNudge.Cutoff in
theorem solution (M : Params) (hS : Standing M) (π : ℝ → ℝ) (hπ : IsMechanism π) :
    (∫ θ, (π θ * U0 M 1 1 θ + (1 - π θ) * U0 M 0 0 θ) ∂M.P) =
      (1 + M.δ) / ta M * objective M π := by
  obtain ⟨hβ0, hβ1, hδ0, hδ1, hK, hprob, hsupp⟩ := hS
  haveI := hprob
  have hae : ∀ᵐ θ ∂M.P, θ ∈ Set.Icc (0 : ℝ) 1 := mem_ae_iff.mpr hsupp
  have hπi : Integrable π M.P :=
    Integrable.of_bound hπ.1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hπ.2 θ).1, (hπ.2 θ).2])
  have hθπ : Integrable (fun θ => θ * π θ) M.P := by
    refine Integrable.of_bound (measurable_id.mul hπ.1).aestronglyMeasurable 1 ?_
    filter_upwards [hae] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg (hπ.2 θ).1]
    nlinarith [hθ.1, hθ.2, (hπ.2 θ).1, (hπ.2 θ).2]
  have e : (fun θ => π θ * U0 M 1 1 θ + (1 - π θ) * U0 M 0 0 θ) =
      fun θ => (1 + M.β * M.δ) * π θ - ((1 + M.δ) * (M.β * M.δ ^ 2 * M.C)) * (θ * π θ) := by
    funext θ; simp only [U0]; ring
  rw [e, integral_sub (hπi.const_mul _) (hθπ.const_mul _), integral_const_mul, integral_const_mul]
  unfold objective th ta
  have hK0 : M.β * M.δ ^ 2 * M.C ≠ 0 := by linarith
  have h1d : 1 + M.δ ≠ 0 := by linarith
  have hC0 : M.C ≠ 0 := right_ne_zero_of_mul hK0
  have hβ0' : M.β ≠ 0 := hβ0.ne'
  have hδ0' : M.δ ≠ 0 := hδ0.ne'
  field_simp <;> ring
